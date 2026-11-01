// منقوشة بزيت وزعتر: سبورة رسم مشتركة لحظية + ألعاب (Express + Socket.io)
// التشغيل: npm install ثم npm start  ← http://localhost:3000

const path = require('path');
const fs = require('fs');
const http = require('http');
const crypto = require('crypto');
const express = require('express');
const { Server } = require('socket.io');

const PORT = process.env.PORT || 3000;
const DATA_FILE = path.join(__dirname, 'data', 'boards.json');

// أبعاد اللوحة المنطقية (نفسها عند كل الأجهزة). صارت أطول لتحت: 1500×2000
const W = 1500;
const H = 2000;

const LIMITS = {
  rooms: 200,        // أقصى عدد لوحات بالذاكرة
  strokes: 8000,     // أقصى عدد خطوط وإيموجي باللوحة الواحدة
  points: 20000,     // أقصى عدد أرقام (x,y) بالخط الواحد
  batch: 2000,       // أقصى دفعة نقاط بالرسالة الواحدة
  livePerUser: 4,
  name: 24
};

const ROOM_RE = /^[a-zA-Z0-9_-]{1,40}$/;
const ID_RE = /^[a-z0-9]{4,24}$/;
const HEX = /^#[0-9a-fA-F]{6}$/;
const COLORS = ['#E0607E', '#3D8BD9', '#D98A1F', '#2E9E6B', '#9A6AD6', '#D35A3A', '#1F9BA8', '#B5512F'];

// الإيموجي اللي بتنحط على السبورة (لازم تكون نفس القائمة اللي بـ public/board.html)
const STAMPS = new Set(['😂', '😢', '😠', '😍', '😮', '😎', '🤔', '🥳', '👍', '👏', '❤️', '⭐', '🔥', '💯']);

// لعبة الذاكرة: كم زوج، ومن وين بننقّي الإيموجي
const MEM_PAIRS = 10;
const MEM_PREVIEW_MS = 5000;   // كم بتضل الكروت مكشوفة أول اللعبة
const MEM_ASK_MS = 30000;      // كم بنستنى الثاني يرد على «مستعد؟»
const MEM_POOL = ['🐶', '🐱', '🐭', '🐰', '🦊', '🐻', '🐼', '🐸', '🐵', '🦁', '🐯', '🐮', '🐷', '🐔', '🐧',
  '🦋', '🍎', '🍉', '🍇', '🍓', '🍌', '🍕', '🍩', '⚽', '🚗', '🌙', '🌈', '🎈', '🎁', '🚀'];

// لعبة الحية
const SN = {
  W: 28, H: 28,          // حجم اللوحة بالمربعات
  TICK: 110,             // كل كم ملي ثانية بتتحرك الحيات خطوة
  START_LEN: 3,          // طول الحية أول ما تبلّش أو ترجع صغيرة
  WIN_LEN: 20,           // اللي بيوصل لهالطول أول بيفوز
  ROUND_MS: 120000,      // مدة الجولة (دقيقتين)، وبعدها الأطول بيفوز
  FOOD_MOVE_MS: 7000,    // إذا ما حدا أكل الدائرة، بتنقل لمكان ثاني
  SAFE_MS: 1500,         // بعد ما ترجع صغيرة بتكون محمية شوي
  COUNT_MS: 3000         // العد التنازلي قبل البداية
};
const SN_DIRS = { u: [0, -1], d: [0, 1], l: [-1, 0], r: [1, 0] };
const SN_OPP = { u: 'd', d: 'u', l: 'r', r: 'l' };
const SN_COLORS = ['#F5D76E', '#93CFEE', '#F2A0BE', '#F4A96A', '#F2EFE6', '#C9A7F0', '#A9DFA0', '#7FE0D6'];

// لعبة التلوين: أسماء الرسومات (لازم تكون نفس اللي بـ public/board.html)
const PAINT_PICS = new Set(['house', 'flower', 'tree', 'car', 'fish', 'butterfly', 'rocket', 'cat',
  'mandala', 'peacock', 'owl', 'castle', 'ship', 'train', 'sea', 'land', 'lantern', 'olive']);
const PAINT_REGION = /^[a-z0-9]{1,8}$/;
const PAINT_MAX = 300; // أقصى عدد أجزاء ملوّنة بالرسمة الوحدة

// ---------- التحقق من البيانات القادمة من المتصفح ----------
function cleanPts(p, max) {
  if (!Array.isArray(p) || p.length % 2 !== 0 || p.length > max) return null;
  const out = new Array(p.length);
  for (let i = 0; i < p.length; i++) {
    const v = p[i];
    const lim = i % 2 ? H : W; // الزوجي x والفردي y
    if (typeof v !== 'number' || !Number.isFinite(v) || v < -300 || v > lim + 300) return null;
    out[i] = Math.round(v);
  }
  return out;
}
function clampW(w) {
  const n = Number(w);
  return Number.isFinite(n) ? Math.min(90, Math.max(1, n)) : 6;
}
function clampStamp(w) {
  const n = Number(w);
  return Number.isFinite(n) ? Math.min(240, Math.max(24, Math.round(n))) : 90;
}
function cleanStroke(s) {
  if (!s || typeof s !== 'object' || !ID_RE.test(s.id)) return null;
  const p = cleanPts(s.p, LIMITS.points);
  if (!p || p.length < 2) return null;
  const by = typeof s.by === 'string' && ID_RE.test(s.by) ? s.by : 'unknown';
  if (s.m !== undefined) {
    if (!STAMPS.has(s.m)) return null;
    return { id: s.id, by, m: s.m, w: clampStamp(s.w), p: p.slice(0, 2) };
  }
  return { id: s.id, by, c: HEX.test(s.c) ? s.c : '#F2EFE6', w: clampW(s.w), e: s.e === true, p };
}
function cleanName(n) {
  if (typeof n !== 'string') return '';
  return n.replace(/[\u0000-\u001F\u007F\u200B-\u200F\u202A-\u202E\u2066-\u2069]/g, '').trim().slice(0, LIMITS.name);
}
function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

// ---------- الألعاب ----------
const XO_LINES = [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]];

function newXo() {
  return {
    cells: Array(9).fill(''),
    turn: 'X',
    seats: { X: null, O: null },   // { cid, pid, name }
    winner: null,                  // 'X' | 'O' | 'draw'
    line: null,
    score: { X: 0, O: 0, draw: 0 }
  };
}
function publicXo(b) {
  const x = b.xo;
  const seat = (k) => (x.seats[k] ? { pid: x.seats[k].pid, name: x.seats[k].name } : null);
  return { cells: x.cells, turn: x.turn, winner: x.winner, line: x.line, score: x.score, seats: { X: seat('X'), O: seat('O') } };
}

function newMem() {
  const picks = shuffle(MEM_POOL.slice()).slice(0, MEM_PAIRS);
  return {
    phase: 'idle',        // idle: لسا ما بلّشت | preview: الكروت مكشوفة 5 ثواني | play | done
    cards: shuffle([...picks, ...picks]),
    matched: Array(MEM_PAIRS * 2).fill(false),
    open: [],             // الكروت المقلوبة هلأ (واحد أو اثنين)
    lock: null,           // مين عم يقلب هلأ { cid, pid, name }
    moves: 0,
    scores: new Map(),    // cid -> { pid, name, n }
    round: 0,
    timer: null,
    ask: null,            // طلب «مستعد؟» { cid, pid, name, no: Set(cid) }
    askTimer: null,
    previewEnds: 0,
    previewTimer: null
  };
}
function clearMemTimers(m) {
  clearTimeout(m.timer);
  clearTimeout(m.askTimer);
  clearTimeout(m.previewTimer);
}
function publicMem(b) {
  const m = b.mem;
  const peek = m.phase === 'preview';
  return {
    phase: m.phase,
    // الكروت المخفية بتوصل null، فما حدا بيقدر يغشّ من المتصفح
    faces: m.cards.map((c, i) => (peek || m.matched[i] || m.open.includes(i) ? c : null)),
    matched: m.matched,
    open: m.open,
    lock: m.lock ? { pid: m.lock.pid, name: m.lock.name } : null,
    moves: m.moves,
    pairs: MEM_PAIRS,
    found: m.matched.filter(Boolean).length / 2,
    scores: [...m.scores.values()]
      .map((s) => ({ pid: s.pid, name: s.name, n: s.n }))
      .sort((a, c) => c.n - a.n),
    ask: m.ask ? { pid: m.ask.pid, name: m.ask.name, no: [...m.ask.no].map((cid) => b.pids.get(cid)) } : null,
    previewLeft: peek ? Math.max(0, m.previewEnds - Date.now()) : 0
  };
}
function emitMem(b, room) {
  io.to(room).emit('mem', publicMem(b));
}
// رسالة لشخص معين (على كل تبويباته المفتوحة)
function tellCid(b, cid, game, text) {
  for (const u of b.users.values()) if (u.cid === cid) io.to(u.id).emit('game:msg', { game, text });
}
function otherCids(b, cid) {
  return new Set([...b.users.values()].map((u) => u.cid).filter((c) => c !== cid));
}
// بداية لعبة: كروت جديدة، بتنكشف للكل 5 ثواني وبعدين بتنقلب
function memBegin(b, room) {
  clearMemTimers(b.mem);
  const m = newMem();
  m.phase = 'preview';
  m.previewEnds = Date.now() + MEM_PREVIEW_MS;
  b.mem = m;
  m.previewTimer = setTimeout(() => {
    if (b.mem !== m) return;
    m.phase = 'play';
    emitMem(b, room);
  }, MEM_PREVIEW_MS);
  emitMem(b, room);
}
function memCancelAsk(b, room, note) {
  const m = b.mem;
  if (!m.ask) return;
  const ask = m.ask;
  clearTimeout(m.askTimer);
  m.ask = null;
  if (note) tellCid(b, ask.cid, 'mem', note);
  emitMem(b, room);
}

// ---------- الحية ----------
function newSnake() {
  return {
    phase: 'idle',        // idle | count: عد تنازلي | play | over
    players: new Map(),   // cid -> { pid, name, color, body: [خانات، الراس أول وحدة], dir, queue, safeUntil }
    food: null,           // رقم الخانة اللي فيها الدائرة
    foodAt: 0,
    startAt: 0,
    endsAt: 0,
    winner: null,
    ask: null,
    askTimer: null,
    countTimer: null,
    loop: null
  };
}
function stopSnake(g) {
  clearInterval(g.loop);
  clearTimeout(g.countTimer);
  clearTimeout(g.askTimer);
}
function snakeOccupied(g, except) {
  const occ = new Set();
  for (const s of g.players.values()) if (s !== except) for (const c of s.body) occ.add(c);
  return occ;
}
const snCell = (x, y) => ((y + SN.H) % SN.H) * SN.W + ((x + SN.W) % SN.W);

// بنحط الحية بمكان فاضي، صغيرة، وقدامها شوية مكان
function snakeSpawn(g, s) {
  const occ = snakeOccupied(g, s);
  for (let t = 0; t < 300; t++) {
    const x = crypto.randomInt(SN.W), y = crypto.randomInt(SN.H);
    const dir = 'udlr'[crypto.randomInt(4)];
    const [dx, dy] = SN_DIRS[dir];
    const body = [];
    let ok = true;
    for (let i = -4; i < SN.START_LEN && ok; i++) {
      const c = snCell(x - dx * i, y - dy * i);
      if (occ.has(c) || c === g.food) ok = false;
      else if (i >= 0) body.push(c);
    }
    if (ok) { s.body = body; s.dir = dir; s.queue = []; return; }
  }
  s.body = [snCell(crypto.randomInt(SN.W), crypto.randomInt(SN.H))];
  s.dir = 'r'; s.queue = [];
}
function snakeFood(g) {
  const occ = snakeOccupied(g);
  g.food = null;
  for (let t = 0; t < 600; t++) {
    const c = crypto.randomInt(SN.W * SN.H);
    if (!occ.has(c)) { g.food = c; break; }
  }
  g.foodAt = Date.now();
}
function snakeAdd(b, g, cid) {
  if (g.players.has(cid)) return;
  const u = [...b.users.values()].find((x) => x.cid === cid);
  if (!u) return;
  const s = { pid: b.pids.get(cid), name: u.name, color: SN_COLORS[g.players.size % SN_COLORS.length], body: [], dir: 'r', queue: [], safeUntil: 0 };
  g.players.set(cid, s);
  snakeSpawn(g, s);
}
function publicSnake(b) {
  const g = b.snake;
  const now = Date.now();
  return {
    phase: g.phase,
    w: SN.W, h: SN.H, winLen: SN.WIN_LEN, roundMs: SN.ROUND_MS,
    food: g.food,
    foodLeft: g.phase === 'play' && g.food !== null ? Math.max(0, g.foodAt + SN.FOOD_MOVE_MS - now) : 0,
    foodMs: SN.FOOD_MOVE_MS,
    players: [...g.players.values()].map((s) => ({
      pid: s.pid, name: s.name, color: s.color, body: s.body, dir: s.dir, len: s.body.length, safe: s.safeUntil > now
    })),
    left: g.phase === 'play' ? Math.max(0, g.endsAt - now) : 0,
    count: g.phase === 'count' ? Math.max(0, g.startAt - now) : 0,
    winner: g.winner,
    ask: g.ask ? { pid: g.ask.pid, name: g.ask.name, no: [...g.ask.no].map((cid) => b.pids.get(cid)) } : null
  };
}
function publicPaint(b) {
  const fills = {};
  for (const [pic, m] of b.paint.fills) fills[pic] = Object.fromEntries(m);
  return { pic: b.paint.pic, fills };
}
function emitSnake(b, room) {
  io.to(room).emit('snake', publicSnake(b));
}
function snakeCancelAsk(b, room, note) {
  const g = b.snake;
  if (!g.ask) return;
  const ask = g.ask;
  clearTimeout(g.askTimer);
  g.ask = null;
  if (note) tellCid(b, ask.cid, 'snake', note);
  emitSnake(b, room);
}
// بداية جولة: عد تنازلي 3 ثواني وبعدين بتتحرك الحيات
function snakeBegin(b, room, cids) {
  stopSnake(b.snake);
  const g = newSnake();
  b.snake = g;
  g.phase = 'count';
  g.startAt = Date.now() + SN.COUNT_MS;
  for (const cid of cids) snakeAdd(b, g, cid);
  g.countTimer = setTimeout(() => {
    if (b.snake !== g) return;
    if (!g.players.size) { g.phase = 'idle'; emitSnake(b, room); return; }
    g.phase = 'play';
    g.endsAt = Date.now() + SN.ROUND_MS;
    snakeFood(g);
    g.loop = setInterval(() => snakeTick(b, room, g), SN.TICK);
    emitSnake(b, room);
  }, SN.COUNT_MS);
  emitSnake(b, room);
}
function snakeEnd(b, room, g) {
  clearInterval(g.loop);
  g.phase = 'over';
  const list = [...g.players.values()];
  const best = Math.max(0, ...list.map((s) => s.body.length));
  const top = list.filter((s) => s.body.length === best);
  g.winner = { pids: top.map((s) => s.pid), names: top.map((s) => s.name), len: best, draw: top.length > 1 };
  emitSnake(b, room);
}
function snakeTick(b, room, g) {
  if (b.snake !== g || g.phase !== 'play') { clearInterval(g.loop); return; }
  const now = Date.now();
  const list = [...g.players.values()];
  let ate = false;

  // كل حية بتمشي خطوة (والحيطان بترجعك من الجهة الثانية)
  for (const s of list) {
    if (s.queue.length) s.dir = s.queue.shift();
    const h = s.body[0];
    const [dx, dy] = SN_DIRS[s.dir];
    const nh = snCell((h % SN.W) + dx, Math.floor(h / SN.W) + dy);
    s.body.unshift(nh);
    if (nh === g.food) ate = true; // أكلت: ما بنقصّ الذيل فبتطول خانة
    else s.body.pop();
  }

  // الخبط: إذا راسك خبط بجسم حية ثانية، هي اللي بترجع صغيرة. راس براس: الاثنين
  const reset = new Set();
  const notes = [];
  for (const a of list) {
    if (a.safeUntil > now) continue;
    for (const v of list) {
      if (v === a || v.safeUntil > now) continue;
      const i = v.body.indexOf(a.body[0]);
      if (i === 0) {
        if (!reset.has(a) || !reset.has(v)) notes.push('راس براس! ' + a.name + ' و' + v.name + ' رجعوا صغار');
        reset.add(a); reset.add(v);
      } else if (i > 0) {
        reset.add(v);
        notes.push(a.name + ' خبط بـ' + v.name + '، ورجع ' + v.name + ' صغير');
      }
    }
  }
  for (const s of reset) {
    snakeSpawn(g, s);
    s.safeUntil = now + SN.SAFE_MS;
  }
  if (notes.length) io.to(room).emit('game:msg', { game: 'snake', text: notes[0] });

  // الدائرة: إذا انأكلت أو طوّلت بمكانها، بتنقل
  if (ate || g.food === null || now - g.foodAt >= SN.FOOD_MOVE_MS) snakeFood(g);

  // الفوز: أول واحد بيوصل للطول المطلوب، أو الأطول لما يخلص الوقت
  if (list.some((s) => s.body.length >= SN.WIN_LEN) || now >= g.endsAt) { snakeEnd(b, room, g); return; }
  emitSnake(b, room);
}

// ---------- اللوحات ----------
const boards = new Map(); // room -> board

function newBoard(strokes) {
  return {
    strokes: strokes || [], live: new Map(), users: new Map(), guestN: 0, colorN: 0,
    pids: new Map(),   // cid -> رقم عام للاعب (ما بنكشف الـ cid للباقيين)
    xo: newXo(),
    mem: newMem(),
    snake: newSnake(),
    paint: { pic: 'house', fills: new Map() } // pic -> Map(جزء -> لون)
  };
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

  let pid = b.pids.get(clientId);
  if (!pid) {
    pid = crypto.randomBytes(5).toString('hex');
    b.pids.set(clientId, pid);
  }

  socket.join(room);
  const user = {
    id: socket.id,
    cid: clientId, // ما بينبعت للباقيين
    name: cleanName(auth.name) || ('رسّام ' + (++b.guestN)),
    color: COLORS[b.colorN++ % COLORS.length]
  };
  b.users.set(socket.id, user);

  const isHere = (cid) => [...b.users.values()].some((u) => u.cid === cid);
  const othersHere = () => [...b.users.values()].some((u) => u.cid !== clientId);
  const tell = (game, text) => socket.emit('game:msg', { game, text });

  socket.emit('init', {
    you: { id: user.id, name: user.name, color: user.color, pid },
    strokes: b.strokes,
    live: [...b.live.values()],
    users: publicUsers(b),
    xo: publicXo(b),
    mem: publicMem(b),
    snake: publicSnake(b),
    paint: publicPaint(b)
  });
  socket.to(room).emit('users', publicUsers(b));

  const mineLive = new Set();

  function addCommitted(s) {
    b.strokes.push(s);
    if (b.strokes.length > LIMITS.strokes) b.strokes.splice(0, b.strokes.length - LIMITS.strokes);
    io.to(room).emit('stroke:commit', s);
    scheduleSave();
  }

  function commit(id) {
    mineLive.delete(id);
    const s = b.live.get(id);
    if (!s) return;
    b.live.delete(id);
    addCommitted(s);
  }

  // ---------- الرسم ----------
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

  // إيموجي على السبورة
  socket.on('stamp', (d) => {
    if (!d || !ID_RE.test(d.id) || !STAMPS.has(d.m)) return;
    const p = cleanPts(d.p, 2);
    if (!p || p.length !== 2) return;
    addCommitted({ id: d.id, by: clientId, m: d.m, w: clampStamp(d.w), p });
  });

  // تراجع: يشيل آخر خط أو إيموجي حطّه نفس الشخص (حتى لو عمل تحديث للصفحة)
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

  // ---------- إكس أو ----------
  socket.on('xo:move', (i) => {
    const x = b.xo;
    if (!Number.isInteger(i) || i < 0 || i > 8 || x.winner || x.cells[i]) return;
    const k = x.turn;
    const seat = x.seats[k];
    if (seat && seat.cid !== clientId) return tell('xo', 'مش دورك، استنى ' + seat.name);
    if (!seat) {
      const other = x.seats[k === 'X' ? 'O' : 'X'];
      // إذا إنت ماسك الحرف الثاني وفي حدا معك، خلّيه هو يلعب
      if (other && other.cid === clientId && othersHere()) return tell('xo', 'دور ' + k + '، خلّي صاحبك يلعبها');
      x.seats[k] = { cid: clientId, pid, name: user.name };
    }
    x.cells[i] = k;
    const line = XO_LINES.find(([a, c, d]) => x.cells[a] && x.cells[a] === x.cells[c] && x.cells[a] === x.cells[d]);
    if (line) { x.winner = k; x.line = line; x.score[k]++; }
    else if (x.cells.every(Boolean)) { x.winner = 'draw'; x.score.draw++; }
    else x.turn = k === 'X' ? 'O' : 'X';
    io.to(room).emit('xo', publicXo(b));
  });

  // جولة جديدة: نفس اللاعبين ونفس النتيجة
  socket.on('xo:new', () => {
    const x = b.xo;
    for (const k of ['X', 'O']) if (x.seats[k] && !isHere(x.seats[k].cid)) x.seats[k] = null;
    if (x.seats.X && x.seats.O && x.seats.X.cid === x.seats.O.cid) x.seats.O = null;
    x.cells = Array(9).fill('');
    x.turn = 'X';
    x.winner = null;
    x.line = null;
    io.to(room).emit('xo', publicXo(b));
  });

  // تصفير كامل: لاعبين جداد ونتيجة صفر
  socket.on('xo:reset', () => {
    b.xo = newXo();
    io.to(room).emit('xo', publicXo(b));
  });

  // ---------- ذاكرة الإيموجي ----------
  socket.on('mem:flip', (i) => {
    const m = b.mem;
    if (m.phase !== 'play') return;
    if (!Number.isInteger(i) || i < 0 || i >= m.cards.length || m.matched[i] || m.open.includes(i)) return;
    if (m.open.length >= 2) return;
    if (m.open.length === 1 && m.lock && m.lock.cid !== clientId) return tell('mem', 'استنى، ' + m.lock.name + ' عم يقلب');

    clearTimeout(m.timer);

    if (m.open.length === 0) {
      m.lock = { cid: clientId, pid, name: user.name };
      m.open = [i];
      const round = ++m.round;
      // إذا قلب كرت ونسي، بنرجّعه بعد 10 ثواني عشان ما يعلق الباقيين
      m.timer = setTimeout(() => {
        if (b.mem === m && m.round === round && m.open.length === 1) {
          m.open = [];
          m.lock = null;
          io.to(room).emit('mem', publicMem(b));
        }
      }, 10000);
      io.to(room).emit('mem', publicMem(b));
      return;
    }

    // الكرت الثاني
    m.open.push(i);
    m.moves++;
    const [a, c] = m.open;
    if (m.cards[a] === m.cards[c]) {
      m.matched[a] = m.matched[c] = true;
      const s = m.scores.get(clientId) || { pid, name: user.name, n: 0 };
      s.n++;
      s.name = user.name;
      m.scores.set(clientId, s);
      m.open = [];
      m.lock = null;
      if (m.matched.every(Boolean)) m.phase = 'done';
      io.to(room).emit('mem', publicMem(b));
    } else {
      const round = ++m.round;
      io.to(room).emit('mem', publicMem(b));
      m.timer = setTimeout(() => {
        if (b.mem === m && m.round === round) {
          m.open = [];
          m.lock = null;
          io.to(room).emit('mem', publicMem(b));
        }
      }, 1100);
    }
  });

  // «ابدأ اللعبة»: إذا إنت لحالك بتبلّش فوراً، وإذا في حدا معك بنسأله «مستعد؟»
  socket.on('mem:start', () => {
    const m = b.mem;
    if (m.phase === 'preview') return;
    if (m.ask) {
      // إذا في طلب من غيرك وضغطت «ابدأ»، كأنك قلت «نعم»
      if (m.ask.cid !== clientId) memBegin(b, room);
      return;
    }
    if (!othersHere()) { memBegin(b, room); return; }
    m.ask = { cid: clientId, pid, name: user.name, no: new Set() };
    m.askTimer = setTimeout(() => {
      if (b.mem === m && m.ask) memCancelAsk(b, room, 'ما حدا ردّ، جرّب كمان مرة');
    }, MEM_ASK_MS);
    emitMem(b, room);
  });

  // الرد على «مستعد؟»: true = نعم، false = لا
  socket.on('mem:answer', (yes) => {
    const m = b.mem;
    if (!m.ask || m.ask.cid === clientId || m.phase === 'preview') return;
    if (yes === true) { memBegin(b, room); return; }
    m.ask.no.add(clientId);
    tellCid(b, m.ask.cid, 'mem', user.name + ' مش جاهز هلأ');
    const others = otherCids(b, m.ask.cid);
    if ([...others].every((c) => m.ask.no.has(c))) memCancelAsk(b, room);
    else emitMem(b, room);
  });

  socket.on('mem:cancel', () => {
    if (b.mem.ask && b.mem.ask.cid === clientId) memCancelAsk(b, room);
  });

  // ---------- الحية ----------
  socket.on('snake:start', () => {
    const g = b.snake;
    if (g.phase === 'count') { // الجولة على وشك تبلّش: بتدخل معهم
      if (!g.players.has(clientId)) { snakeAdd(b, g, clientId); emitSnake(b, room); }
      return;
    }
    if (g.ask) {
      if (g.ask.cid !== clientId) snakeBegin(b, room, [g.ask.cid, clientId]);
      return;
    }
    if (!othersHere()) { snakeBegin(b, room, [clientId]); return; }
    g.ask = { cid: clientId, pid, name: user.name, no: new Set() };
    g.askTimer = setTimeout(() => {
      if (b.snake === g && g.ask) snakeCancelAsk(b, room, 'ما حدا ردّ، جرّب كمان مرة');
    }, MEM_ASK_MS);
    emitSnake(b, room);
  });

  socket.on('snake:answer', (yes) => {
    const g = b.snake;
    if (!g.ask || g.ask.cid === clientId) return;
    if (yes === true) { snakeBegin(b, room, [g.ask.cid, clientId]); return; }
    g.ask.no.add(clientId);
    tellCid(b, g.ask.cid, 'snake', user.name + ' مش جاهز هلأ');
    const others = otherCids(b, g.ask.cid);
    if ([...others].every((c) => g.ask.no.has(c))) snakeCancelAsk(b, room);
    else emitSnake(b, room);
  });

  socket.on('snake:cancel', () => {
    if (b.snake.ask && b.snake.ask.cid === clientId) snakeCancelAsk(b, room);
  });

  socket.on('snake:dir', (d) => {
    const g = b.snake;
    const s = g.players.get(clientId);
    if (!s || !SN_DIRS[d] || (g.phase !== 'play' && g.phase !== 'count')) return;
    if (g.phase === 'count') { // قبل البداية بتختار وين بدك تمشي
      const [dx, dy] = SN_DIRS[d];
      if (s.body.length > 1 && snCell((s.body[0] % SN.W) + dx, Math.floor(s.body[0] / SN.W) + dy) === s.body[1]) return;
      s.dir = d;
      emitSnake(b, room);
      return;
    }
    const last = s.queue.length ? s.queue[s.queue.length - 1] : s.dir;
    if (d === last || d === SN_OPP[last] || s.queue.length >= 2) return;
    s.queue.push(d);
  });

  // ---------- التلوين ----------
  socket.on('paint:fill', (d) => {
    if (!d || !PAINT_PICS.has(d.pic) || typeof d.r !== 'string' || !PAINT_REGION.test(d.r)) return;
    if (d.c !== null && !HEX.test(d.c)) return;
    let f = b.paint.fills.get(d.pic);
    if (!f) { f = new Map(); b.paint.fills.set(d.pic, f); }
    if (d.c === null) f.delete(d.r);
    else {
      if (!f.has(d.r) && f.size >= PAINT_MAX) return;
      f.set(d.r, d.c);
    }
    socket.to(room).emit('paint:fill', { pic: d.pic, r: d.r, c: d.c });
  });

  // تغيير الرسمة بيصير عند الكل، عشان تلوّنوا مع بعض
  socket.on('paint:pic', (pic) => {
    if (!PAINT_PICS.has(pic) || b.paint.pic === pic) return;
    b.paint.pic = pic;
    socket.to(room).emit('paint:pic', { pic, by: user.name });
  });

  socket.on('paint:clear', (pic) => {
    if (!PAINT_PICS.has(pic)) return;
    b.paint.fills.delete(pic);
    io.to(room).emit('paint:clear', { pic, by: user.name });
  });

  // ---------- الاسم والخروج ----------
  socket.on('rename', (n) => {
    const name = cleanName(n);
    if (!name) return;
    user.name = name;
    for (const k of ['X', 'O']) if (b.xo.seats[k] && b.xo.seats[k].cid === clientId) b.xo.seats[k].name = name;
    const sc = b.mem.scores.get(clientId);
    if (sc) sc.name = name;
    if (b.mem.lock && b.mem.lock.cid === clientId) b.mem.lock.name = name;
    if (b.mem.ask && b.mem.ask.cid === clientId) b.mem.ask.name = name;
    const sp = b.snake.players.get(clientId);
    if (sp) sp.name = name;
    if (b.snake.ask && b.snake.ask.cid === clientId) b.snake.ask.name = name;
    io.to(room).emit('users', publicUsers(b));
    io.to(room).emit('xo', publicXo(b));
    io.to(room).emit('mem', publicMem(b));
    emitSnake(b, room);
  });

  socket.on('disconnect', () => {
    for (const id of [...mineLive]) commit(id);
    b.users.delete(socket.id);
    io.to(room).emit('users', publicUsers(b));
    io.to(room).emit('cursor', { sid: socket.id, x: null, y: null });

    // إذا طلع لاعب من إكس أو بنفضّي مكانه عشان حدا ثاني يكمّل
    if (!isHere(clientId)) {
      let changed = false;
      for (const k of ['X', 'O']) {
        if (b.xo.seats[k] && b.xo.seats[k].cid === clientId) { b.xo.seats[k] = null; changed = true; }
      }
      if (changed) io.to(room).emit('xo', publicXo(b));
    }

    // طلب «مستعد؟» معلّق: إذا طلع صاحب الطلب، أو ما ضل حدا يرد، بنلغيه
    const ask = b.mem.ask;
    if (ask) {
      const others = otherCids(b, ask.cid);
      if (ask.cid === clientId && !isHere(clientId)) memCancelAsk(b, room);
      else if (!others.size) memCancelAsk(b, room, 'صاحبك طلع، اضغط «ابدأ اللعبة» لتلعب لحالك');
      else if ([...others].every((c) => ask.no.has(c))) memCancelAsk(b, room);
    }

    // الحية: إذا طلع لاعب بنشيل حيته، وإذا ما ضل لاعبين بنوقف الجولة
    const g = b.snake;
    if (!isHere(clientId) && g.players.delete(clientId)) {
      if (!g.players.size && (g.phase === 'play' || g.phase === 'count')) {
        stopSnake(g);
        g.phase = 'idle';
        g.food = null;
      }
      emitSnake(b, room);
    }
    const sAsk = g.ask;
    if (sAsk) {
      const others = otherCids(b, sAsk.cid);
      if (sAsk.cid === clientId && !isHere(clientId)) snakeCancelAsk(b, room);
      else if (!others.size) snakeCancelAsk(b, room, 'صاحبك طلع، اضغط «ابدأ اللعبة» لتلعب لحالك');
      else if ([...others].every((c) => sAsk.no.has(c))) snakeCancelAsk(b, room);
    }

    if (!b.users.size && !b.strokes.length && room !== 'main') {
      clearMemTimers(b.mem);
      stopSnake(b.snake);
      boards.delete(room);
    }
  });
});

server.listen(PORT, () => {
  console.log('منقوشة بزيت وزعتر شغالة على http://localhost:' + PORT);
});
