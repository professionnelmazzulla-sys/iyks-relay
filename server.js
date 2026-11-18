'use strict';
/*
 * "I know your secrets" - serveur relais (codes de salle, jusqu'à 6 joueurs)
 * ----------------------------------------------------------------------
 * Copie adaptée du relais de Meat Please. Les deux sont INDÉPENDANTS :
 * autre dépôt, autre service, autre numéro de protocole.
 *
 * Topologie "étoile" : l'hôte (id 0) est l'autorité du jeu.
 *   - un invité (id 1 à 5) parle seulement à l'hôte ;
 *   - l'hôte parle à tous les invités, ou à un seul (champ "to").
 *
 * Aucune dépendance : seulement Node.js (version 18 ou plus).
 *   Lancer :  node server.js        (écoute sur le port 8080, ou la variable PORT)
 *
 * Protocole (messages JSON texte, par WebSocket) :
 *   client -> serveur : {t:"create", ver}          crée une salle
 *                       {t:"join", code, ver}      rejoint une salle
 *                       {t:"lock", locked}         (hôte) ferme/ouvre la salle aux nouveaux
 *                       {t:"msg", k, d, to?}       message (invité -> hôte ; hôte -> tous ou "to")
 *   serveur -> client : {t:"created", code, id:0}
 *                       {t:"joined", id}           (à l'invité)
 *                       {t:"peer_joined", id}      (à l'hôte)
 *                       {t:"peer_left", id}        (à l'hôte)
 *                       {t:"room_closed"}          (aux invités)
 *                       {t:"msg", k, d, from}
 *                       {t:"error", reason}  (no_room | full | version | busy | locked)
 */

const http = require('http');
const crypto = require('crypto');

const PORT = parseInt(process.env.PORT, 10) || 8080;
const PROTOCOL_VERSION = 100;   // différent de Meat Please (1) : les deux jeux ne se mélangent pas
const MAX_PLAYERS = 6;          // hôte compris
const MAX_PAYLOAD = 8192;        // taille max d'un message (octets)
const MAX_ROOMS = 2000;
const MAX_MSG_PER_SECOND = 60;
const IDLE_ROOM_MS = 60 * 60 * 1000;   // une salle sans invité est supprimée après 1 h
const CODE_ALPHABET = 'ABCDEFGHJKLMNPRSTUVWXYZ';   // sans I, O, Q (faciles à confondre)
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';

const rooms = new Map();    // code -> { host, guests: Map(id -> client), locked, created }
const clients = new Set();


// ---------------------------------------------------------------
//  Mini WebSocket (RFC 6455) : poignée de main + lecture/écriture de trames
// ---------------------------------------------------------------

class Client {
  constructor(socket) {
    this.socket = socket;
    this.buf = Buffer.alloc(0);
    this.alive = true;
    this.closed = false;
    this.room = null;
    this.role = null;
    this.id = -1;
    this.fragments = [];
    this.fragOpcode = 0;
    this.fragSize = 0;
    this.windowStart = Date.now();
    this.windowCount = 0;
  }

  send(obj) {
    this.sendFrame(0x1, Buffer.from(JSON.stringify(obj), 'utf8'));
  }

  sendFrame(opcode, payload) {
    if (this.closed || this.socket.destroyed) return;
    const len = payload.length;
    let header;
    if (len < 126) {
      header = Buffer.from([0x80 | opcode, len]);
    } else if (len < 65536) {
      header = Buffer.alloc(4);
      header[0] = 0x80 | opcode;
      header[1] = 126;
      header.writeUInt16BE(len, 2);
    } else {
      header = Buffer.alloc(10);
      header[0] = 0x80 | opcode;
      header[1] = 127;
      header.writeBigUInt64BE(BigInt(len), 2);
    }
    this.socket.write(Buffer.concat([header, payload]));
  }

  close(code) {
    if (this.closed) return;
    const payload = Buffer.alloc(2);
    payload.writeUInt16BE(code || 1000);
    this.sendFrame(0x8, payload);
    this.closed = true;
    this.socket.end();
    handleClose(this);
  }

  onData(chunk) {
    this.alive = true;
    this.buf = Buffer.concat([this.buf, chunk]);
    while (!this.closed) {
      if (this.buf.length < 2) return;
      const b0 = this.buf[0];
      const b1 = this.buf[1];
      const fin = (b0 & 0x80) !== 0;
      const opcode = b0 & 0x0f;
      const masked = (b1 & 0x80) !== 0;
      let len = b1 & 0x7f;
      let offset = 2;
      if (len === 126) {
        if (this.buf.length < 4) return;
        len = this.buf.readUInt16BE(2);
        offset = 4;
      } else if (len === 127) {
        if (this.buf.length < 10) return;
        const big = this.buf.readBigUInt64BE(2);
        if (big > BigInt(MAX_PAYLOAD)) return this.close(1009);
        len = Number(big);
        offset = 10;
      }
      if (len > MAX_PAYLOAD) return this.close(1009);
      if (!masked) return this.close(1002);       // un client DOIT masquer ses trames
      if (this.buf.length < offset + 4 + len) return;
      const mask = this.buf.subarray(offset, offset + 4);
      const data = Buffer.from(this.buf.subarray(offset + 4, offset + 4 + len));
      for (let i = 0; i < data.length; i++) data[i] ^= mask[i & 3];
      this.buf = this.buf.subarray(offset + 4 + len);
      this.onFrame(fin, opcode, data);
    }
  }

  onFrame(fin, opcode, data) {
    if (opcode === 0x8) return this.close(1000);                 // fermeture
    if (opcode === 0x9) return this.sendFrame(0xA, data);        // ping -> pong
    if (opcode === 0xA) return;                                  // pong
    if (opcode === 0x1 || opcode === 0x2) {
      this.fragOpcode = opcode;
      this.fragments = [data];
      this.fragSize = data.length;
    } else if (opcode === 0x0) {
      this.fragments.push(data);
      this.fragSize += data.length;
      if (this.fragSize > MAX_PAYLOAD) return this.close(1009);
    } else {
      return this.close(1002);
    }
    if (fin) {
      const message = Buffer.concat(this.fragments);
      const type = this.fragOpcode;
      this.fragments = [];
      this.fragSize = 0;
      if (type === 0x1) handleText(this, message.toString('utf8'));
    }
  }
}


// ---------------------------------------------------------------
//  Salles
// ---------------------------------------------------------------

function newCode() {
  for (let attempt = 0; attempt < 50; attempt++) {
    let code = '';
    for (let i = 0; i < 4; i++) {
      code += CODE_ALPHABET[crypto.randomInt(CODE_ALPHABET.length)];
    }
    if (!rooms.has(code)) return code;
  }
  return null;
}

function handleText(c, text) {
  const now = Date.now();
  if (now - c.windowStart > 1000) {
    c.windowStart = now;
    c.windowCount = 0;
  }
  if (++c.windowCount > MAX_MSG_PER_SECOND) return c.close(1008);

  let m;
  try { m = JSON.parse(text); } catch (e) { return; }
  if (!m || typeof m.t !== 'string') return;

  switch (m.t) {
    case 'create': {
      if (c.room) return;
      if (m.ver !== PROTOCOL_VERSION) return c.send({ t: 'error', reason: 'version' });
      if (rooms.size >= MAX_ROOMS) return c.send({ t: 'error', reason: 'busy' });
      const code = newCode();
      if (!code) return c.send({ t: 'error', reason: 'busy' });
      rooms.set(code, { host: c, guests: new Map(), locked: false, created: now });
      c.room = code;
      c.role = 'host';
      c.id = 0;
      c.send({ t: 'created', code, id: 0 });
      log('salle ' + code + ' créée (' + rooms.size + ' salle(s))');
      break;
    }
    case 'join': {
      if (c.room) return;
      const code = String(m.code || '').trim().toUpperCase();
      const room = rooms.get(code);
      if (!room) return c.send({ t: 'error', reason: 'no_room' });
      if (m.ver !== PROTOCOL_VERSION) return c.send({ t: 'error', reason: 'version' });
      if (room.locked) return c.send({ t: 'error', reason: 'locked' });
      if (room.guests.size + 1 >= MAX_PLAYERS) return c.send({ t: 'error', reason: 'full' });
      let id = 1;
      while (room.guests.has(id)) id++;
      room.guests.set(id, c);
      c.room = code;
      c.role = 'guest';
      c.id = id;
      c.send({ t: 'joined', id });
      room.host.send({ t: 'peer_joined', id });
      log('salle ' + code + ' : joueur ' + id + ' connecté (' + (room.guests.size + 1) + '/' + MAX_PLAYERS + ')');
      break;
    }
    case 'lock': {
      const room = rooms.get(c.room);
      if (!room || c.role !== 'host') return;
      room.locked = !!m.locked;
      break;
    }
    case 'msg': {
      const room = rooms.get(c.room);
      if (!room || typeof m.k !== 'string' || m.k.length > 32) return;
      if (c.role === 'host') {
        const out = { t: 'msg', k: m.k, d: m.d, from: 0 };
        if (Number.isInteger(m.to)) {
          const target = room.guests.get(m.to);
          if (target) target.send(out);
        } else {
          for (const g of room.guests.values()) g.send(out);
        }
      } else {
        room.host.send({ t: 'msg', k: m.k, d: m.d, from: c.id });
      }
      break;
    }
    default:
      break;
  }
}

function handleClose(c) {
  clients.delete(c);
  if (!c.room) return;
  const code = c.room;
  c.room = null;
  const room = rooms.get(code);
  if (!room) return;
  if (c.role === 'host') {
    rooms.delete(code);
    for (const g of room.guests.values()) {
      g.room = null;
      g.send({ t: 'room_closed' });
      g.close(1000);
    }
    log('salle ' + code + ' fermée (' + rooms.size + ' salle(s))');
  } else {
    room.guests.delete(c.id);
    room.host.send({ t: 'peer_left', id: c.id });
    log('salle ' + code + ' : joueur ' + c.id + ' parti');
  }
}

function log(text) {
  console.log(new Date().toISOString() + '  ' + text);
}


// ---------------------------------------------------------------
//  Serveur HTTP + passage en WebSocket
// ---------------------------------------------------------------

const server = http.createServer((req, res) => {
  // Une page simple : sert aussi à "réveiller" le serveur depuis un navigateur.
  res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
  res.end('I know your secrets relay OK - ' + rooms.size + ' salle(s)\n');
});

server.on('upgrade', (req, socket, head) => {
  const key = req.headers['sec-websocket-key'];
  const upgrade = String(req.headers['upgrade'] || '').toLowerCase();
  if (!key || upgrade !== 'websocket') {
    socket.destroy();
    return;
  }
  const accept = crypto.createHash('sha1').update(key + WS_GUID).digest('base64');
  socket.write(
    'HTTP/1.1 101 Switching Protocols\r\n' +
    'Upgrade: websocket\r\n' +
    'Connection: Upgrade\r\n' +
    'Sec-WebSocket-Accept: ' + accept + '\r\n\r\n'
  );
  socket.setNoDelay(true);

  const c = new Client(socket);
  clients.add(c);
  socket.on('data', (chunk) => c.onData(chunk));
  socket.on('close', () => { c.closed = true; handleClose(c); });
  socket.on('error', () => { c.closed = true; socket.destroy(); handleClose(c); });
  if (head && head.length) c.onData(head);
});

// Toutes les 25 s : ping aux clients, coupe ceux qui ne répondent plus,
// supprime les salles abandonnées. (Ça évite aussi que la connexion soit coupée par inactivité.)
setInterval(() => {
  const now = Date.now();
  for (const c of clients) {
    if (!c.alive) {
      c.socket.destroy();
      continue;
    }
    c.alive = false;
    c.sendFrame(0x9, Buffer.alloc(0));
  }
  for (const [code, room] of rooms) {
    if (room.guests.size === 0 && now - room.created > IDLE_ROOM_MS) {
      room.host.close(1000);
    }
  }
}, 25000);

server.listen(PORT, '0.0.0.0', () => {
  log('I know your secrets relay : à l\'écoute sur le port ' + PORT);
});
