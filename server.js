// سبورتنا: سيرفر رسم مشترك لحظي (Express + Socket.io)
// التشغيل: npm install ثم npm start  ← http://localhost:3000

const path = require('path');
const fs = require('fs');
const http = require('http');
const crypto = require('crypto');
const express = require('express');
const { Server } = require('socket.io');

const PORT = process.env.PORT || 3000;
const DATA_FILE = path.join(__dirname, 'data', 'boards.json');

// أبعاد اللوحة المنطقية (نفسها عند كل الأجهزة)
const W = 1500;
const H = 1000;

const LIMITS = {
  rooms: 200,        // أقصى عدد لوحات بالذاكرة
  strokes: 8000,     // أقصى عدد خطوط باللوحة الواحدة
  points: 20000,     // أقصى عدد أرقام (x,y) بالخط الواحد
  batch: 2000,       // أقصى دفعة نقاط بالرسالة الواحدة
  livePerUser: 4,
  name: 24
};

const ROOM_RE = /^[a-zA-Z0-9_-]{1,40}$/;
const ID_RE = /^[a-z0-9]{4,24}$/;
const HEX = /^#[0-9a-fA-F]{6}$/;
const COLORS = ['#E0607E', '#3D8BD9', '#D98A1F', '#2E9E6B', '#9A6AD6', '#D35A3A', '#1F9BA8', '#B5512F'];

// ---------- التحقق من البيانات القادمة من المتصفح ----------
function cleanPts(p, max) {
  if (!Array.isArray(p) || p.length % 2 !== 0 || p.length > max) return null;
  const out = new Array(p.length);
  for (let i = 0; i < p.length; i++) {
    const v = p[i];
    if (typeof v !== 'number' || !Number.isFinite(v) || v < -300 || v > W + 300) return null;
    out[i] = Math.round(v);
  }
  return out;
}
function clampW(w) {
  const n = Number(w);
  return Number.isFinite(n) ? Math.min(90, Math.max(1, n)) : 6;
}
function cleanStroke(s) {
  if (!s || typeof s !== 'object' || !ID_RE.test(s.id)) return null;
  const p = cleanPts(s.p, LIMITS.points);
  if (!p || p.length < 2) return null;
  return {
    id: s.id,
    by: typeof s.by === 'string' && ID_RE.test(s.by) ? s.by : 'unknown',
    c: HEX.test(s.c) ? s.c : '#F2EFE6',
    w: clampW(s.w),
    e: s.e === true,
    p
  };
}
function cleanName(n) {
  if (typeof n !== 'string') return '';
  return n.replace(/[\u0000-\u001F\u007F\u200B-\u200F\u202A-\u202E\u2066-\u2069]/g, '').trim().slice(0, LIMITS.name);
}

// ---------- اللوحات ----------
const boards = new Map(); // room -> { strokes, live, users, guestN, colorN }

function newBoard(strokes) {
  return { strokes: strokes || [], live: new Map(), users: new Map(), guestN: 0, colorN: 0 };
}
function getBoard(room) {
  let b = boards.get(room);
  if (!b) {
    if (boards.size >= LIMITS.rooms) return null;
    b = newBoard();
    boards.set(room, b);
  }
  return b;
}
function publicUsers(b) {
  return [...b.users.values()].map((u) => ({ id: u.id, name: u.name, color: u.color }));
}

// تحميل الرسومات المحفوظة (إن وجدت)
try {
  const saved = JSON.parse(fs.readFileSync(DATA_FILE, 'utf8'));
  for (const [room, strokes] of Object.entries(saved)) {
    if (ROOM_RE.test(room) && Array.isArray(strokes)) {
      boards.set(room, newBoard(strokes.map(cleanStroke).filter(Boolean)));
    }
  }
  console.log('تم تحميل', boards.size, 'لوحة محفوظة');
} catch (_) { /* أول تشغيل: ما في ملف */ }

let saveTimer = null;
function scheduleSave() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    const out = {};
    for (const [room, b] of boards) if (b.strokes.length) out[room] = b.strokes;
    fs.mkdir(path.dirname(DATA_FILE), { recursive: true }, () => {
      const tmp = DATA_FILE + '.tmp';
      fs.writeFile(tmp, JSON.stringify(out), (err) => {
        if (!err) fs.rename(tmp, DATA_FILE, () => {});
      });
    });
  }, 2000);
}

// ---------- HTTP ----------
const app = express();
const server = http.createServer(app);
const io = new Server(server, { maxHttpBufferSize: 1e6 });

const PAGE = path.join(__dirname, 'public', 'board.html');
app.use(express.static(path.join(__dirname, 'public'), { index: false }));
app.get('/', (req, res) => res.sendFile(PAGE));
app.get('/r/:room', (req, res) => {
  if (!ROOM_RE.test(req.params.room)) return res.redirect('/');
  res.sendFile(PAGE);
});
app.get('/healthz', (req, res) => res.send('ok'));

// ---------- Socket.io ----------
io.on('connection', (socket) => {
  const auth = socket.handshake.auth || {};
  const room = typeof auth.room === 'string' && ROOM_RE.test(auth.room) ? auth.room : 'main';
  const clientId = typeof auth.clientId === 'string' && ID_RE.test(auth.clientId)
    ? auth.clientId
    : crypto.randomBytes(6).toString('hex');

  const b = getBoard(room);
  if (!b) {
    socket.emit('full');
    socket.disconnect(true);
    return;
  }

  socket.join(room);
  const user = {
    id: socket.id,
    name: cleanName(auth.name) || ('رسّام ' + (++b.guestN)),
    color: COLORS[b.colorN++ % COLORS.length]
  };
  b.users.set(socket.id, user);

  socket.emit('init', {
    you: { id: user.id, name: user.name, color: user.color },
    strokes: b.strokes,
    live: [...b.live.values()],
    users: publicUsers(b)
  });
  socket.to(room).emit('users', publicUsers(b));

  const mineLive = new Set();

  function commit(id) {
    mineLive.delete(id);
    const s = b.live.get(id);
    if (!s) return;
    b.live.delete(id);
    b.strokes.push(s);
    if (b.strokes.length > LIMITS.strokes) b.strokes.splice(0, b.strokes.length - LIMITS.strokes);
    io.to(room).emit('stroke:commit', s);
    scheduleSave();
  }

  socket.on('stroke:start', (d) => {
    if (!d || !ID_RE.test(d.id) || b.live.has(d.id) || mineLive.size >= LIMITS.livePerUser) return;
    const p = cleanPts(d.p, LIMITS.batch);
    if (!p || p.length < 2) return;
    const s = { id: d.id, by: clientId, c: HEX.test(d.c) ? d.c : '#F2EFE6', w: clampW(d.w), e: d.e === true, p };
    b.live.set(s.id, s);
    mineLive.add(s.id);
    socket.to(room).emit('stroke:start', s);
  });

  socket.on('stroke:points', (d) => {
    if (!d || !mineLive.has(d.id)) return;
    const s = b.live.get(d.id);
    const p = cleanPts(d.p, LIMITS.batch);
    if (!s || !p || !p.length || s.p.length + p.length > LIMITS.points) return;
    for (const v of p) s.p.push(v);
    socket.to(room).emit('stroke:points', { id: d.id, p });
  });

  socket.on('stroke:end', (d) => {
    if (d && mineLive.has(d.id)) commit(d.id);
  });

  // تراجع: يشيل آخر خط رسمه نفس الشخص (حتى لو عمل تحديث للصفحة)
  socket.on('undo', () => {
    for (let i = b.strokes.length - 1; i >= 0; i--) {
      if (b.strokes[i].by === clientId) {
        const [s] = b.strokes.splice(i, 1);
        io.to(room).emit('stroke:remove', { id: s.id });
        scheduleSave();
        return;
      }
    }
  });

  socket.on('clear', () => {
    b.strokes = [];
    io.to(room).emit('cleared');
    scheduleSave();
  });

  socket.on('cursor', (d) => {
    if (!d || d.x === null) {
      socket.to(room).volatile.emit('cursor', { sid: socket.id, x: null, y: null });
      return;
    }
    if (!Number.isFinite(d.x) || !Number.isFinite(d.y)) return;
    socket.to(room).volatile.emit('cursor', {
      sid: socket.id,
      x: Math.round(Math.max(0, Math.min(W, d.x))),
      y: Math.round(Math.max(0, Math.min(H, d.y))),
      drawing: d.drawing === true
    });
  });

  socket.on('rename', (n) => {
    const name = cleanName(n);
    if (!name) return;
    user.name = name;
    io.to(room).emit('users', publicUsers(b));
  });

  socket.on('disconnect', () => {
    for (const id of [...mineLive]) commit(id);
    b.users.delete(socket.id);
    io.to(room).emit('users', publicUsers(b));
    io.to(room).emit('cursor', { sid: socket.id, x: null, y: null });
    if (!b.users.size && !b.strokes.length && room !== 'main') boards.delete(room);
  });
});

server.listen(PORT, () => {
  console.log('سبورتنا شغالة على http://localhost:' + PORT);
});
