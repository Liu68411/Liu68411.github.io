'use strict';

/* ============================================================
   函数与几何实验室
   纯前端：表达式解析 / 数值计算 / Canvas 2D & 3D / 交互几何
   ============================================================ */

const $ = (sel, root = document) => root.querySelector(sel);
const $$ = (sel, root = document) => Array.from(root.querySelectorAll(sel));
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const lerp = (a, b, t) => a + (b - a) * t;
const TAU = Math.PI * 2;
const DEG = Math.PI / 180;

let uidCounter = 1;
const uid = (p = 'o') => `${p}_${uidCounter++}`;

const PALETTE = ['#7c3aed', '#0f766e', '#2563eb', '#b45309', '#be123c', '#0891b2'];
const GEO_COLORS = {
  point: '#0f766e', line: '#475569', triangle: '#0f766e', quad: '#2563eb',
  circle: '#7c3aed', bisector: '#b45309', mark: '#15803d', similar: '#b45309'
};

const canvas = $('#board');
const ctx = canvas.getContext('2d');
let W = 0, H = 0, DPR = 1;

const state = {
  mode: 'plane',              // plane | space | blank
  tab: 'function',            // function | conic | geometry
  tool: 'select',
  view: { zoom: 1, panX: 0, panY: 0 },
  space: {
    yaw: -0.72, pitch: 0.36, zoom: 1, panX: 0, panY: 0,
    points: []
  },
  functions: [],
  activeFnId: null,
  curve: null,
  conicType: 'circle',
  conicParams: {
    circle: { h: 0, k: 0, r: 3 },
    ellipse: { h: 0, k: 0, a: 4, b: 2.4 },
    parabola: { h: 0, k: 0, p: 2, orient: 'right' },
    hyperbola: { h: 0, k: 0, a: 3, b: 2, orient: 'horizontal' }
  },
  conicResult: null,
  circleTangent: null,
  tangentPicking: false,
  analysisMode: 'function',
  calc: null,
  rotateExpr: '180 - 2α',
  keepOriginal: true,
  geom: {
    points: [], shapes: [], marks: [], transforms: [], alpha: null, nextLabel: 0,
    snap: true, showLabels: true, horizontalBase: true
  },
  selected: null,
  hover: null,
  pending: [],
  transformTarget: null,
  preview: null,
  drag: null,
  markFirst: null,
  history: [],
  future: [],
  saveTimer: null
};

/* ---------- 基础工具 ---------- */

function esc(s) {
  return String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
}
function fmt(n, digits = 3) {
  if (!Number.isFinite(n)) return '—';
  const a = Math.abs(n);
  if (a !== 0 && (a < 1e-4 || a >= 1e6)) return n.toExponential(2).replace('e+', '×10^').replace('e-', '×10^-');
  const r = Number(n.toFixed(digits));
  return String(Object.is(r, -0) ? 0 : r);
}
function fmtSigned(n, digits = 3) {
  const s = fmt(n, digits);
  return s.startsWith('-') ? `− ${s.slice(1)}` : `+ ${s}`;
}
function deg(rad) { return rad / DEG; }
function rad(d) { return d * DEG; }
function dist(a, b) { return Math.hypot(a.x - b.x, a.y - b.y); }
function mid(a, b) { return { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 }; }
function sub(a, b) { return { x: a.x - b.x, y: a.y - b.y }; }
function add(a, b) { return { x: a.x + b.x, y: a.y + b.y }; }
function mul(a, k) { return { x: a.x * k, y: a.y * k }; }
function norm(a) { const l = Math.hypot(a.x, a.y) || 1; return { x: a.x / l, y: a.y / l }; }
function perp(a) { return { x: -a.y, y: a.x }; }
function dot(a, b) { return a.x * b.x + a.y * b.y; }
function cross(a, b) { return a.x * b.y - a.y * b.x; }
function rotate(a, ang) {
  const c = Math.cos(ang), s = Math.sin(ang);
  return { x: a.x * c - a.y * s, y: a.x * s + a.y * c };
}
function angleAt(p, a, b) {
  const u = sub(a, p), v = sub(b, p);
  const d = dot(u, v) / ((Math.hypot(u.x, u.y) || 1) * (Math.hypot(v.x, v.y) || 1));
  return Math.acos(clamp(d, -1, 1));
}
function pointInPoly(p, poly) {
  let inside = false;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const a = poly[i], b = poly[j];
    if (((a.y > p.y) !== (b.y > p.y)) && (p.x < (b.x - a.x) * (p.y - a.y) / (b.y - a.y) + a.x)) inside = !inside;
  }
  return inside;
}
function distToSegment(p, a, b) {
  const v = sub(b, a), w = sub(p, a);
  const c1 = dot(w, v), c2 = dot(v, v);
  if (c2 === 0) return dist(p, a);
  const t = clamp(c1 / c2, 0, 1);
  return dist(p, { x: a.x + v.x * t, y: a.y + v.y * t });
}
function distToLine(p, a, b) {
  const v = sub(b, a);
  const l = Math.hypot(v.x, v.y);
  if (!l) return dist(p, a);
  return Math.abs(cross(v, sub(p, a))) / l;
}
function pointOnRay(p, o, a) {
  const v = sub(a, o), w = sub(p, o);
  return dot(v, w) >= 0 && distToLine(p, o, a) < 1e-9;
}
function escMath(s) {
  return esc(s)
    .replace(/\^(-?\d+(?:\.\d+)?)/g, '<sup>$1</sup>')
    .replace(/\*/g, '·');
}
function toast(msg, kind = '') {
  const el = $('#toast');
  el.textContent = msg;
  el.className = 'toast show ' + kind;
  clearTimeout(toast._t);
  toast._t = setTimeout(() => { el.className = 'toast ' + kind; }, 2600);
}
function showFatal(err) {
  const box = $('#jsError');
  box.style.display = 'block';
  box.textContent = '页面脚本遇到错误：\n' + (err && err.stack ? err.stack : err);
}
window.addEventListener('error', e => showFatal(e.error || e.message));

/* ============================================================
   表达式解析器
   支持 + - * / ^、括号、隐式乘法、sin/cos/tan/ln/log/exp/sqrt/abs
   ============================================================ */

const FUNCS = {
  sin: Math.sin, cos: Math.cos, tan: Math.tan,
  asin: Math.asin, acos: Math.acos, atan: Math.atan,
  sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh,
  ln: Math.log, log: x => Math.log10(x), exp: Math.exp,
  sqrt: Math.sqrt, abs: Math.abs, floor: Math.floor, ceil: Math.ceil
};
const CONSTS = { pi: Math.PI, e: Math.E };

function tokenize(src) {
  const s = String(src).replace(/π/g, 'pi').replace(/×/g, '*').replace(/÷/g, '/')
    .replace(/−/g, '-').replace(/²/g, '^2').replace(/³/g, '^3');
  const tokens = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (/\s/.test(c)) { i++; continue; }
    if (/[0-9.]/.test(c)) {
      const m = /^(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?/.exec(s.slice(i));
      if (!m) throw new Error('数字格式不正确');
      tokens.push({ type: 'num', value: parseFloat(m[0]) });
      i += m[0].length;
      continue;
    }
    if (/[a-zA-Z]/.test(c)) {
      const m = /^[a-zA-Z]+/.exec(s.slice(i));
      let name = m[0].toLowerCase();
      // 将 sinx 拆成 sin x 之类的简写交给隐式乘法处理
      tokens.push({ type: 'ident', value: name });
      i += name.length;
      continue;
    }
    if ('+-*/^(),'.includes(c)) {
      tokens.push({ type: c === '(' || c === ')' || c === ',' ? c : 'op', value: c });
      i++;
      continue;
    }
    throw new Error(`无法识别的字符「${c}」`);
  }

  // 补隐式乘法：2x、2(x+1)、(x+1)(x-1)、x sin(x)
  const out = [];
  const endsValue = t => t && (t.type === 'num' || t.type === ')' || (t.type === 'ident' && !FUNCS[t.value]));
  const startsValue = t => t && (t.type === 'num' || t.type === '(' || (t.type === 'ident' && !FUNCS[t.value]));
  for (let k = 0; k < tokens.length; k++) {
    const t = tokens[k], prev = out[out.length - 1];
    if (prev && endsValue(prev) && startsValue(t)) out.push({ type: 'op', value: '*' });
    out.push(t);
  }
  return out;
}

function parseExpression(src) {
  const tokens = tokenize(src);
  let pos = 0;
  const peek = () => tokens[pos];
  const eat = (type, value) => {
    const t = tokens[pos];
    if (!t || t.type !== type || (value !== undefined && t.value !== value)) return null;
    pos++;
    return t;
  };
  function parseAdd() {
    let node = parseMul();
    while (peek() && peek().type === 'op' && (peek().value === '+' || peek().value === '-')) {
      const op = tokens[pos++].value;
      node = { t: 'bin', op, l: node, r: parseMul() };
    }
    return node;
  }
  function parseMul() {
    let node = parseUnary();
    while (peek() && peek().type === 'op' && (peek().value === '*' || peek().value === '/')) {
      const op = tokens[pos++].value;
      node = { t: 'bin', op, l: node, r: parseUnary() };
    }
    return node;
  }
  function parseUnary() {
    const t = peek();
    if (t && t.type === 'op' && (t.value === '+' || t.value === '-')) {
      pos++;
      return { t: 'un', op: t.value, a: parseUnary() };
    }
    return parsePower();
  }
  function parsePower() {
    const base = parsePrimary();
    if (peek() && peek().type === 'op' && peek().value === '^') {
      pos++;
      return { t: 'bin', op: '^', l: base, r: parseUnary() };
    }
    return base;
  }
  function parsePrimary() {
    const t = peek();
    if (!t) throw new Error('表达式不完整');
    if (t.type === 'num') { pos++; return { t: 'num', v: t.value }; }
    if (t.type === '(') {
      pos++;
      const n = parseAdd();
      if (!eat(')')) throw new Error('缺少右括号');
      return n;
    }
    if (t.type === 'ident') {
      pos++;
      const name = t.value;
      if (name === 'x') return { t: 'var', name: 'x' };
      if (CONSTS[name] !== undefined) return { t: 'const', name };
      if (FUNCS[name]) {
        if (!eat('(')) throw new Error(`函数 ${name} 后需要括号`);
        const args = [parseAdd()];
        while (eat(',')) args.push(parseAdd());
        if (!eat(')')) throw new Error('缺少右括号');
        return { t: 'call', name, args };
      }
      throw new Error(`未知符号「${name}」`);
    }
    throw new Error('表达式格式不正确');
  }
  if (!tokens.length) throw new Error('请输入函数表达式');
  const root = parseAdd();
  if (pos < tokens.length) throw new Error('表达式后有多余内容');
  return root;
}

function evalNode(n, x) {
  switch (n.t) {
    case 'num': return n.v;
    case 'var': return x;
    case 'const': return CONSTS[n.name];
    case 'un': return n.op === '-' ? -evalNode(n.a, x) : evalNode(n.a, x);
    case 'bin': {
      const a = evalNode(n.l, x), b = evalNode(n.r, x);
      switch (n.op) {
        case '+': return a + b;
        case '-': return a - b;
        case '*': return a * b;
        case '/': return a / b;
        case '^': return Math.pow(a, b);
      }
      return NaN;
    }
    case 'call': {
      const a = n.args.map(v => evalNode(v, x));
      if (n.name === 'log' && a.length === 2) return Math.log(a[0]) / Math.log(a[1]);
      if (n.name === 'atan' && a.length === 2) return Math.atan2(a[0], a[1]);
      const f = FUNCS[n.name];
      return f ? f(a[0]) : NaN;
    }
  }
  return NaN;
}

/* ---------- 符号化简 ---------- */

const isNum = n => n && n.t === 'num';
const isVar = n => n && n.t === 'var';
const num = v => ({ t: 'num', v });
const zero = () => num(0);
const one = () => num(1);
function nval(n) { return isNum(n) ? n.v : null; }
function isZero(n) { return isNum(n) && Math.abs(n.v) < 1e-12; }
function isOne(n) { return isNum(n) && Math.abs(n.v - 1) < 1e-12; }

function simplify(n) {
  if (!n) return n;
  if (n.t === 'un') {
    const a = simplify(n.a);
    if (isNum(a)) return num(n.op === '-' ? -a.v : a.v);
    if (n.op === '+') return a;
    if (a.t === 'un' && a.op === '-') return a.a;
    return { t: 'un', op: '-', a };
  }
  if (n.t === 'bin') {
    const a = simplify(n.l), b = simplify(n.r);
    const av = nval(a), bv = nval(b);
    switch (n.op) {
      case '+':
        if (isZero(a)) return b;
        if (isZero(b)) return a;
        if (av !== null && bv !== null) return num(av + bv);
        if (b.t === 'un' && b.op === '-') return simplify({ t: 'bin', op: '-', l: a, r: b.a });
        return { t: 'bin', op: '+', l: a, r: b };
      case '-':
        if (isZero(b)) return a;
        if (isZero(a)) return simplify({ t: 'un', op: '-', a: b });
        if (av !== null && bv !== null) return num(av - bv);
        return { t: 'bin', op: '-', l: a, r: b };
      case '*':
        if (isZero(a) || isZero(b)) return zero();
        if (isOne(a)) return b;
        if (isOne(b)) return a;
        if (av !== null && bv !== null) return num(av * bv);
        if (av === -1) return simplify({ t: 'un', op: '-', a: b });
        if (bv === -1) return simplify({ t: 'un', op: '-', a });
        // 2 · (x²/2) → x²；系数不是整数时保留分数形式 3x²/2
        if (av !== null && b.t === 'bin' && b.op === '/' && isNum(b.r) && b.r.v !== 0) {
          const coef = av / b.r.v;
          if (Number.isInteger(coef)) return simplify({ t: 'bin', op: '*', l: num(coef), r: b.l });
          return simplify({ t: 'bin', op: '/', l: { t: 'bin', op: '*', l: num(av), r: b.l }, r: b.r });
        }
        if (bv !== null && a.t === 'bin' && a.op === '/' && isNum(a.r) && a.r.v !== 0) {
          const coef = bv / a.r.v;
          if (Number.isInteger(coef)) return simplify({ t: 'bin', op: '*', l: num(coef), r: a.l });
          return simplify({ t: 'bin', op: '/', l: { t: 'bin', op: '*', l: num(bv), r: a.l }, r: a.r });
        }
        // 把数字放到左边
        if (bv !== null && av === null) return { t: 'bin', op: '*', l: b, r: a };
        return { t: 'bin', op: '*', l: a, r: b };
      case '/':
        if (isZero(a)) return zero();
        if (isOne(b)) return a;
        if (av !== null && bv !== null && bv !== 0) {
          const r = av / bv;
          if (Math.abs(r - Math.round(r)) < 1e-12) return num(Math.round(r));
        }
        if (bv !== null && bv !== 0 && a.t === 'bin' && a.op === '*' && isNum(a.l)) {
          const coef = a.l.v / bv;
          if (Number.isInteger(coef)) return simplify({ t: 'bin', op: '*', l: num(coef), r: a.r });
        }
        return { t: 'bin', op: '/', l: a, r: b };
      case '^':
        if (isZero(b)) return one();
        if (isOne(b)) return a;
        if (isOne(a)) return one();
        if (av !== null && bv !== null) {
          const r = Math.pow(av, bv);
          if (Number.isFinite(r)) return num(r);
        }
        return { t: 'bin', op: '^', l: a, r: b };
    }
  }
  if (n.t === 'call') {
    const args = n.args.map(simplify);
    if (args.every(isNum)) {
      const vals = args.map(a => a.v);
      if (n.name === 'ln' && args[0].t === 'const' && args[0].name === 'e') return one();
      let r;
      if (n.name === 'log' && vals.length === 2) r = Math.log(vals[0]) / Math.log(vals[1]);
      else if (n.name === 'atan' && vals.length === 2) r = Math.atan2(vals[0], vals[1]);
      else r = FUNCS[n.name] ? FUNCS[n.name](vals[0]) : NaN;
      if (Number.isFinite(r) && Math.abs(r - Math.round(r)) < 1e-10) return num(Math.round(r));
      if (Number.isFinite(r)) return num(r);
    }
    return { t: 'call', name: n.name, args };
  }
  return n;
}

/* ---------- 符号求导 ---------- */

function differentiate(n, x = 1) {
  switch (n.t) {
    case 'num': case 'const': return zero();
    case 'var': return num(x);
    case 'un': return { t: 'un', op: n.op, a: differentiate(n.a) };
    case 'bin': {
      const { l, r, op } = n;
      if (op === '+' || op === '-') return { t: 'bin', op, l: differentiate(l), r: differentiate(r) };
      if (op === '*') return {
        t: 'bin', op: '+',
        l: { t: 'bin', op: '*', l: differentiate(l), r: r },
        r: { t: 'bin', op: '*', l: l, r: differentiate(r) }
      };
      if (op === '/') return {
        t: 'bin', op: '/',
        l: {
          t: 'bin', op: '-',
          l: { t: 'bin', op: '*', l: differentiate(l), r: r },
          r: { t: 'bin', op: '*', l: l, r: differentiate(r) }
        },
        r: { t: 'bin', op: '^', l: r, r: num(2) }
      };
      if (op === '^') {
        if (isNum(r)) {
          return {
            t: 'bin', op: '*',
            l: { t: 'bin', op: '*', l: r, r: { t: 'bin', op: '^', l: l, r: num(r.v - 1) } },
            r: differentiate(l)
          };
        }
        // u^v = e^(v ln u)
        return {
          t: 'bin', op: '*',
          l: { t: 'bin', op: '^', l, r },
          r: {
            t: 'bin', op: '+',
            l: { t: 'bin', op: '*', l: differentiate(r), r: { t: 'call', name: 'ln', args: [l] } },
            r: {
              t: 'bin', op: '/',
              l: { t: 'bin', op: '*', l: r, r: differentiate(l) },
              r: l
            }
          }
        };
      }
      return zero();
    }
    case 'call': {
      const a = n.args[0];
      const da = differentiate(a);
      const mulda = d => ({ t: 'bin', op: '*', l: d, r: da });
      switch (n.name) {
        case 'sin': return mulda({ t: 'call', name: 'cos', args: [a] });
        case 'cos': return { t: 'un', op: '-', a: mulda({ t: 'call', name: 'sin', args: [a] }) };
        case 'tan': return {
          t: 'bin', op: '/', l: da,
          r: { t: 'bin', op: '^', l: { t: 'call', name: 'cos', args: [a] }, r: num(2) }
        };
        case 'exp': return mulda({ t: 'call', name: 'exp', args: [a] });
        case 'ln': return { t: 'bin', op: '/', l: da, r: a };
        case 'log': return {
          t: 'bin', op: '/', l: da,
          r: { t: 'bin', op: '*', l: a, r: { t: 'call', name: 'ln', args: [num(10)] } }
        };
        case 'sqrt': return {
          t: 'bin', op: '/', l: da,
          r: { t: 'bin', op: '*', l: num(2), r: { t: 'call', name: 'sqrt', args: [a] } }
        };
        case 'abs': return {
          t: 'bin', op: '*', l: da,
          r: { t: 'bin', op: '/', l: a, r: { t: 'call', name: 'abs', args: [a] } }
        };
        case 'asin': return { t: 'bin', op: '/', l: da, r: { t: 'call', name: 'sqrt', args: [{ t: 'bin', op: '-', l: num(1), r: { t: 'bin', op: '^', l: a, r: num(2) } }] } };
        case 'acos': return { t: 'un', op: '-', a: { t: 'bin', op: '/', l: da, r: { t: 'call', name: 'sqrt', args: [{ t: 'bin', op: '-', l: num(1), r: { t: 'bin', op: '^', l: a, r: num(2) } }] } } };
        case 'atan': return { t: 'bin', op: '/', l: da, r: { t: 'bin', op: '+', l: num(1), r: { t: 'bin', op: '^', l: a, r: num(2) } } };
        case 'sinh': return mulda({ t: 'call', name: 'cosh', args: [a] });
        case 'cosh': return mulda({ t: 'call', name: 'sinh', args: [a] });
        case 'tanh': return {
          t: 'bin', op: '/', l: da,
          r: { t: 'bin', op: '^', l: { t: 'call', name: 'cosh', args: [a] }, r: num(2) }
        };
      }
      return zero();
    }
  }
  return zero();
}

/* ---------- 符号积分（常见初等函数） ---------- */

function detectLinear(n) {
  try {
    const f0 = evalNode(n, 0), f1 = evalNode(n, 1), f2 = evalNode(n, 2);
    const a = f1 - f0, b = f0;
    if (!Number.isFinite(a) || !Number.isFinite(b)) return null;
    if (Math.abs(f2 - (2 * a + b)) > 1e-8 * (1 + Math.abs(f2))) return null;
    return { a, b };
  } catch { return null; }
}

function integrateNode(n) {
  if (n.t === 'num') return { t: 'bin', op: '*', l: n, r: { t: 'var' } };
  if (n.t === 'var') return { t: 'bin', op: '/', l: { t: 'bin', op: '^', l: { t: 'var' }, r: num(2) }, r: num(2) };
  if (n.t === 'const') return { t: 'bin', op: '*', l: n, r: { t: 'var' } };
  if (n.t === 'un') {
    const i = integrateNode(n.a);
    return i ? { t: 'un', op: n.op, a: i } : null;
  }
  if (n.t === 'bin') {
    if (n.op === '+' || n.op === '-') {
      const a = integrateNode(n.l), b = integrateNode(n.r);
      return a && b ? { t: 'bin', op: n.op, l: a, r: b } : null;
    }
    if (n.op === '*') {
      if (isNum(n.l)) {
        const i = integrateNode(n.r);
        return i ? { t: 'bin', op: '*', l: n.l, r: i } : null;
      }
      if (isNum(n.r)) {
        const i = integrateNode(n.l);
        return i ? { t: 'bin', op: '*', l: n.r, r: i } : null;
      }
    }
    if (n.op === '^' && isNum(n.r)) {
      const p = n.r.v;
      const lin = detectLinear(n.l);
      if (lin && Math.abs(lin.a) > 1e-10) {
        if (Math.abs(p + 1) < 1e-12) {
          return {
            t: 'bin', op: '/',
            l: { t: 'call', name: 'abs', args: [n.l] },
            r: num(lin.a)
          };
        }
        return {
          t: 'bin', op: '/',
          l: { t: 'bin', op: '^', l: n.l, r: num(p + 1) },
          r: num(lin.a * (p + 1))
        };
      }
    }
    if (n.op === '/' && isNum(n.l) && n.r.t === 'var' && Math.abs(n.l.v - 1) < 1e-12) {
      return { t: 'call', name: 'ln', args: [{ t: 'call', name: 'abs', args: [n.r] }] };
    }
  }
  if (n.t === 'call' && n.args.length === 1) {
    const a = n.args[0], lin = detectLinear(a);
    if (lin && Math.abs(lin.a) > 1e-10) {
      const k = lin.a;
      if (n.name === 'sin') return { t: 'bin', op: '/', l: { t: 'un', op: '-', a: { t: 'call', name: 'cos', args: [a] } }, r: num(k) };
      if (n.name === 'cos') return { t: 'bin', op: '/', l: { t: 'call', name: 'sin', args: [a] }, r: num(k) };
      if (n.name === 'exp') return { t: 'bin', op: '/', l: n, r: num(k) };
      if (n.name === 'sqrt') {
        return {
          t: 'bin', op: '*',
          l: { t: 'bin', op: '/', l: num(2), r: num(3 * k) },
          r: { t: 'bin', op: '^', l: a, r: num(1.5) }
        };
      }
    }
  }
  return null;
}

/* ---------- AST 格式化 ---------- */

const PREC = { '+': 1, '-': 1, '*': 2, '/': 2, '^': 4 };
function toStr(n, parentPrec = 0, side = '') {
  if (!n) return '—';
  switch (n.t) {
    case 'num': return fmt(n.v, 6);
    case 'var': return 'x';
    case 'const': return n.name === 'pi' ? 'π' : 'e';
    case 'un': {
      const inner = toStr(n.a, 3);
      return '-' + (n.a.t === 'bin' || n.a.t === 'un' ? `(${inner})` : inner);
    }
    case 'bin': {
      const p = PREC[n.op];
      let ls = toStr(n.l, p, 'l');
      let rs = toStr(n.r, p, 'r');
      if (n.op === '^') {
        return wrap(ls, p, parentPrec) + '^' + wrap(rs, p + 1, parentPrec);
      }
      if (n.op === '*') {
        // 2x、3sin(x)、x(x+1) 的自然写法
        if (isNum(n.l) && !isNum(n.r)) return wrap(ls, p, parentPrec) + rs;
        if (n.l.t === 'bin' && (n.l.op === '+' || n.l.op === '-')) ls = `(${ls})`;
        if (n.r.t === 'bin' && (n.r.op === '+' || n.r.op === '-')) rs = `(${rs})`;
        return wrap(ls, p, parentPrec) + '·' + wrap(rs, p + 1, parentPrec);
      }
      if (n.op === '/') {
        if (n.l.t === 'bin' && (n.l.op === '+' || n.l.op === '-')) ls = `(${ls})`;
        if (n.r.t === 'bin' || n.r.t === 'un') rs = `(${rs})`;
        return wrap(ls, p, parentPrec) + '/' + rs;
      }
      if (n.op === '-') {
        if (n.r.t === 'un' && n.r.op === '-') return wrap(ls, p, parentPrec) + ' + ' + toStr(n.r.a, p + 1, 'r');
        return wrap(ls, p, parentPrec) + ' - ' + wrap(rs, p + 1, parentPrec);
      }
      return wrap(ls, p, parentPrec) + ' + ' + wrap(rs, p + 1, parentPrec);
    }
    case 'call': {
      if (n.name === 'log' && n.args.length === 2) return `log(${toStr(n.args[0])}, ${toStr(n.args[1])})`;
      return `${n.name}(${n.args.map(a => toStr(a)).join(', ')})`;
    }
  }
  return '—';
}
function wrap(s, prec, parentPrec) { return prec < parentPrec ? `(${s})` : s; }

/* ---------- 数值积分 / 数值求导 ---------- */

function simpson(f, a, b, n = 800) {
  if (!(a < b)) [a, b] = [b, a];
  if (n % 2) n++;
  const h = (b - a) / n;
  let s = f(a) + f(b);
  for (let i = 1; i < n; i++) {
    const v = f(a + i * h);
    if (!Number.isFinite(v)) return { value: NaN, singular: true };
    s += v * (i % 2 ? 4 : 2);
  }
  return { value: s * h / 3, singular: false };
}
function numericDerivative(f, x, h = 1e-5) {
  const hh = h * Math.max(1, Math.abs(x));
  return (f(x + hh) - f(x - hh)) / (2 * hh);
}
function autoIntegrate(f, a, b) {
  if (!Number.isFinite(a) || !Number.isFinite(b)) return { value: NaN, singular: true };
  // 检查区间内部奇点
  const lo = Math.min(a, b), hi = Math.max(a, b);
  for (let i = 1; i < 40; i++) {
    const x = lerp(lo, hi, i / 40);
    const v = f(x);
    if (!Number.isFinite(v) || Math.abs(v) > 1e8) return { value: NaN, singular: true };
  }
  const n = 1200;
  const r = simpson(f, a, b, n);
  if (!Number.isFinite(r.value)) return { value: NaN, singular: true };
  return { value: (a <= b ? 1 : -1) * r.value, singular: false };
}

/* ============================================================
   圆锥曲线
   ============================================================ */

function signedPart(v, d = 3) {
  if (Math.abs(v) < 1e-10) return '';
  return fmtSigned(v, d);
}
function coordHTML(x, y) { return `(${fmt(x)}, ${fmt(y)})`; }
function shiftSq(v, c) {
  return Math.abs(c) < 1e-10 ? `${v}²` : `(${v} ${signedPart(-c)})²`;
}
function linearPart(v, c) {
  if (Math.abs(c) < 1e-10) return '';
  const a = Math.abs(c);
  return `${c > 0 ? ' + ' : ' − '}${Math.abs(a - 1) < 1e-10 ? '' : fmt(a)}${v}`;
}
function constPart(c) {
  if (Math.abs(c) < 1e-10) return '';
  return c > 0 ? ` + ${fmt(c)}` : ` − ${fmt(Math.abs(c))}`;
}
function shiftBracket(v, c, coef = 1) {
  const k = Math.abs(coef - 1) < 1e-10 ? '' : fmt(coef);
  if (Math.abs(c) < 1e-10) return `${k}${v}`;
  return `${k}(${v} ${signedPart(-c)})`;
}
function shiftCoord(v, c) {
  return Math.abs(c) < 1e-10 ? v : `${v} ${signedPart(-c)}`;
}
function vertexText(h, k, a, vertical) {
  if (vertical) return `(${fmt(h)}, ${fmt(k + a)})，(${fmt(h)}, ${fmt(k - a)})`;
  return `(${fmt(h + a)}, ${fmt(k)})，(${fmt(h - a)}, ${fmt(k)})`;
}

function buildConic(type, p) {
  const h = Number(p.h) || 0, k = Number(p.k) || 0;
  if (type === 'circle') {
    const r = Math.abs(Number(p.r) || 0);
    if (r < 1e-6) throw new Error('半径需要大于 0');
    const D = -2 * h, E = -2 * k, F = h * h + k * k - r * r;
    const eq = `${shiftSq('x', h)} + ${shiftSq('y', k)} = ${fmt(r * r)}`;
    return {
      kind: 'circle', h, k, r, color: '#7c3aed',
      equation: eq,
      general: `x² + y²${linearPart('x', D)}${linearPart('y', E)}${constPart(F)} = 0`,
      props: [
        ['圆心', coordHTML(h, k)],
        ['半径', `r = ${fmt(r)}`],
        ['周长', `2πr ≈ ${fmt(TAU * r)}`],
        ['面积', `πr² ≈ ${fmt(Math.PI * r * r)}`],
        ['离心率', 'e = 0']
      ],
      foci: [], center: { x: h, y: k }
    };
  }
  if (type === 'ellipse') {
    let a = Math.abs(Number(p.a) || 0), b = Math.abs(Number(p.b) || 0);
    if (a < 1e-6 || b < 1e-6) throw new Error('半轴 a、b 都需要大于 0');
    const vertical = b > a;
    const A = vertical ? b : a, B = vertical ? a : b;
    const c = Math.sqrt(Math.max(0, A * A - B * B));
    const e = c / A;
    const foci = vertical
      ? [{ x: h, y: k + c }, { x: h, y: k - c }]
      : [{ x: h + c, y: k }, { x: h - c, y: k }];
    const eq = vertical
      ? `${shiftSq('x', h)}/${fmt(B * B)} + ${shiftSq('y', k)}/${fmt(A * A)} = 1`
      : `${shiftSq('x', h)}/${fmt(A * A)} + ${shiftSq('y', k)}/${fmt(B * B)} = 1`;
    return {
      kind: 'ellipse', h, k, a, b, A, B, c, e, vertical, color: '#7c3aed',
      equation: eq,
      props: [
        ['中心', coordHTML(h, k)],
        ['长半轴 / 短半轴', `a = ${fmt(A)}, b = ${fmt(B)}`],
        ['焦距', `2c = ${fmt(2 * c)}`],
        ['焦点', foci.map(f => coordHTML(f.x, f.y)).join('，')],
        ['离心率', `e = ${fmt(e, 4)}`],
        ['顶点', vertexText(h, k, A, vertical)]
      ],
      foci, center: { x: h, y: k }
    };
  }
  if (type === 'parabola') {
    const pp = Math.abs(Number(p.p) || 0);
    if (pp < 1e-6) throw new Error('焦准距 p 需要大于 0');
    const orient = p.orient || 'right';
    let eq = '', focus, directrix = '', axis = '', extents;
    const q = pp / 2;
    if (orient === 'right') {
      eq = `${shiftSq('y', k)} = ${shiftBracket('x', h, 2 * pp)}`;
      focus = { x: h + q, y: k }; directrix = `x = ${fmt(h - q)}`;
      axis = `y = ${fmt(k)}`; extents = { xmin: h, xmax: h + 12, ymin: k - 8, ymax: k + 8 };
    } else if (orient === 'left') {
      eq = `${shiftSq('y', k)} = ${shiftBracket('x', h, -2 * pp)}`;
      focus = { x: h - q, y: k }; directrix = `x = ${fmt(h + q)}`;
      axis = `y = ${fmt(k)}`; extents = { xmin: h - 12, xmax: h, ymin: k - 8, ymax: k + 8 };
    } else if (orient === 'up') {
      eq = `${shiftSq('x', h)} = ${shiftBracket('y', k, 2 * pp)}`;
      focus = { x: h, y: k + q }; directrix = `y = ${fmt(k - q)}`;
      axis = `x = ${fmt(h)}`; extents = { xmin: h - 8, xmax: h + 8, ymin: k, ymax: k + 12 };
    } else {
      eq = `${shiftSq('x', h)} = ${shiftBracket('y', k, -2 * pp)}`;
      focus = { x: h, y: k - q }; directrix = `y = ${fmt(k + q)}`;
      axis = `x = ${fmt(h)}`; extents = { xmin: h - 8, xmax: h + 8, ymin: k - 12, ymax: k };
    }
    return {
      kind: 'parabola', h, k, p: pp, orient, color: '#7c3aed',
      equation: eq,
      props: [
        ['顶点', coordHTML(h, k)],
        ['焦点', coordHTML(focus.x, focus.y)],
        ['准线', directrix],
        ['对称轴', axis],
        ['焦准距', `p = ${fmt(pp)}`],
        ['离心率', 'e = 1']
      ],
      foci: [focus], center: { x: h, y: k }, extents
    };
  }
  if (type === 'hyperbola') {
    const a = Math.abs(Number(p.a) || 0), b = Math.abs(Number(p.b) || 0);
    if (a < 1e-6 || b < 1e-6) throw new Error('半轴 a、b 都需要大于 0');
    const vertical = p.orient === 'vertical';
    const c = Math.sqrt(a * a + b * b);
    const e = c / a;
    const foci = vertical
      ? [{ x: h, y: k + c }, { x: h, y: k - c }]
      : [{ x: h + c, y: k }, { x: h - c, y: k }];
    const eq = vertical
      ? `${shiftSq('y', k)}/${fmt(a * a)} − ${shiftSq('x', h)}/${fmt(b * b)} = 1`
      : `${shiftSq('x', h)}/${fmt(a * a)} − ${shiftSq('y', k)}/${fmt(b * b)} = 1`;
    const slope = vertical ? a / b : b / a;
    const asym = `${shiftCoord('y', k)} = ± ${fmt(slope)}${shiftBracket('x', h)}`;
    return {
      kind: 'hyperbola', h, k, a, b, c, e, vertical, color: '#7c3aed',
      equation: eq,
      props: [
        ['中心', coordHTML(h, k)],
        ['实半轴 / 虚半轴', `a = ${fmt(a)}, b = ${fmt(b)}`],
        ['焦点', foci.map(f => coordHTML(f.x, f.y)).join('，')],
        ['渐近线', asym],
        ['离心率', `e = ${fmt(e, 4)}`],
        ['顶点', vertexText(h, k, a, vertical)]
      ],
      foci, center: { x: h, y: k }
    };
  }
  throw new Error('未知曲线类型');
}

/* ============================================================
   视图与坐标变换
   ============================================================ */

function baseScale() { return clamp(Math.min(W, H) / 11.2, 25, 62); }
function scale2d() { return baseScale() * state.view.zoom; }
function origin2d() { return { x: W / 2 + state.view.panX, y: H / 2 + state.view.panY }; }
function w2s(p) {
  const o = origin2d(), s = scale2d();
  return { x: o.x + p.x * s, y: o.y - p.y * s };
}
function s2w(p) {
  const o = origin2d(), s = scale2d();
  return { x: (p.x - o.x) / s, y: (o.y - p.y) / s };
}
function zoomAt(sx, sy, factor) {
  const before = s2w({ x: sx, y: sy });
  const old = state.view.zoom;
  state.view.zoom = clamp(old * factor, 0.18, 9);
  const s = scale2d();
  state.view.panX = sx - W / 2 - before.x * s;
  state.view.panY = sy - H / 2 + before.y * s;
  updateZoomLabel();
  draw();
}
function resetView() {
  state.view.zoom = 1; state.view.panX = 0; state.view.panY = 0;
  updateZoomLabel(); draw(); saveSoon();
}
function updateZoomLabel() {
  const el = $('#zoomLabel');
  if (el) el.textContent = Math.round((state.mode === 'space' ? state.space.zoom : state.view.zoom) * 100) + '%';
}
function fitAll() {
  if (state.mode === 'space') { state.space.zoom = 1; state.space.panX = 0; state.space.panY = 0; updateZoomLabel(); draw(); return; }
  const pts = [];
  const g = state.geom;
  if (state.tab === 'geometry' && g.points.length) g.points.forEach(p => pts.push(p));
  if (state.curve) {
    const e = conicBounds(state.curve);
    pts.push({ x: e.minX, y: e.minY }, { x: e.maxX, y: e.maxY });
  }
  if (pts.length && state.tab === 'geometry') {
    let minX = Math.min(...pts.map(p => p.x)), maxX = Math.max(...pts.map(p => p.x));
    let minY = Math.min(...pts.map(p => p.y)), maxY = Math.max(...pts.map(p => p.y));
    const pad = Math.max(1, Math.min(3, Math.max(maxX - minX, maxY - minY) * 0.12));
    minX -= pad; maxX += pad; minY -= pad; maxY += pad;
    const cx = (minX + maxX) / 2, cy = (minY + maxY) / 2;
    const s = Math.min(W * 0.78 / Math.max(0.1, maxX - minX), H * 0.78 / Math.max(0.1, maxY - minY));
    state.view.zoom = clamp(s / baseScale(), 0.2, 6);
    state.view.panX = -cx * scale2d();
    state.view.panY = cy * scale2d();
  } else if (state.curve) {
    fitCurve(state.curve);
  } else {
    state.view.zoom = 1; state.view.panX = 0; state.view.panY = 0;
  }
  updateZoomLabel(); draw(); saveSoon();
}
function conicBounds(c) {
  if (c.kind === 'circle') return { minX: c.h - c.r, maxX: c.h + c.r, minY: c.k - c.r, maxY: c.k + c.r };
  if (c.kind === 'ellipse') {
    const A = c.A, B = c.B;
    return c.vertical ? { minX: c.h - B, maxX: c.h + B, minY: c.k - A, maxY: c.k + A } : { minX: c.h - A, maxX: c.h + A, minY: c.k - B, maxY: c.k + B };
  }
  if (c.kind === 'parabola') {
    const e = c.extents;
    return { minX: Math.min(e.xmin, c.h), maxX: Math.max(e.xmax, c.h), minY: Math.min(e.ymin, c.k), maxY: Math.max(e.ymax, c.k) };
  }
  const ext = Math.max(c.a, c.b) * 4;
  return { minX: c.h - ext, maxX: c.h + ext, minY: c.k - ext, maxY: c.k + ext };
}
function fitCurve(c) {
  const b = conicBounds(c);
  const cx = (b.minX + b.maxX) / 2, cy = (b.minY + b.maxY) / 2;
  const s = Math.min(W * 0.78 / Math.max(0.2, b.maxX - b.minX), H * 0.78 / Math.max(0.2, b.maxY - b.minY));
  state.view.zoom = clamp(s / baseScale(), 0.2, 6);
  state.view.panX = -cx * scale2d();
  state.view.panY = cy * scale2d();
  updateZoomLabel();
}

/* ============================================================
   画布尺寸 / 主绘制
   ============================================================ */

function resizeBoard() {
  const wrap = $('#canvasWrap');
  const r = wrap.getBoundingClientRect();
  W = Math.max(280, Math.round(r.width));
  H = Math.max(260, Math.round(r.height));
  DPR = Math.min(2.5, window.devicePixelRatio || 1);
  canvas.width = Math.round(W * DPR);
  canvas.height = Math.round(H * DPR);
  canvas.style.width = W + 'px';
  canvas.style.height = H + 'px';
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  draw();
}

function draw() {
  if (!W || !H) return;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.clearRect(0, 0, W, H);
  if (state.mode === 'space') {
    renderSpace();
  } else {
    ctx.fillStyle = '#fffdf8';
    ctx.fillRect(0, 0, W, H);
    if (state.mode === 'plane') drawGrid();
    if (state.tab === 'function') drawFunctions();
    if (state.tab === 'conic' && state.curve && state.curve.visible !== false) {
      drawConic(state.curve);
      drawCircleTangent();
    }
    if (state.tab === 'geometry') drawGeometry();
    drawPendingPreview();
  }
  updateLegend();
}

function roundRectPath(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}
function chip(text, x, y, color = '#5b5344', bg = 'rgba(255,253,249,.92)', align = 'left') {
  ctx.save();
  ctx.font = '11px "PingFang SC","Microsoft YaHei",sans-serif';
  const w = ctx.measureText(text).width + 12;
  let left = x;
  if (align === 'center') left = x - w / 2;
  if (align === 'right') left = x - w;
  roundRectPath(left, y - 10, w, 20, 6);
  ctx.fillStyle = bg;
  ctx.fill();
  ctx.strokeStyle = 'rgba(217,208,189,.75)';
  ctx.lineWidth = 1;
  ctx.stroke();
  ctx.fillStyle = color;
  ctx.textAlign = 'left';
  ctx.textBaseline = 'middle';
  ctx.fillText(text, left + 6, y + .5);
  ctx.restore();
}

/* ---------- 2D 网格 ---------- */

function niceStep(raw) {
  const exp = Math.floor(Math.log10(raw));
  const f = raw / Math.pow(10, exp);
  const base = f < 1.5 ? 1 : f < 3.5 ? 2 : f < 7.5 ? 5 : 10;
  return base * Math.pow(10, exp);
}
function drawGrid() {
  const s = scale2d();
  const o = origin2d();
  const major = niceStep(76 / s);
  const minor = major / 5;
  const left = (0 - o.x) / s, right = (W - o.x) / s;
  const top = (o.y - 0) / s, bottom = (o.y - H) / s;

  ctx.save();
  ctx.lineWidth = 1;
  // 次网格
  if ((right - left) / minor < 240) {
    ctx.strokeStyle = 'rgba(31,41,55,.045)';
    ctx.beginPath();
    for (let x = Math.ceil(left / minor) * minor; x <= right; x += minor) {
      const px = Math.round(o.x + x * s) + .5;
      ctx.moveTo(px, 0); ctx.lineTo(px, H);
    }
    for (let y = Math.ceil(bottom / minor) * minor; y <= top; y += minor) {
      const py = Math.round(o.y - y * s) + .5;
      ctx.moveTo(0, py); ctx.lineTo(W, py);
    }
    ctx.stroke();
  }
  // 主网格
  ctx.strokeStyle = 'rgba(70,90,100,.11)';
  ctx.beginPath();
  for (let x = Math.ceil(left / major) * major; x <= right; x += major) {
    const px = Math.round(o.x + x * s) + .5;
    ctx.moveTo(px, 0); ctx.lineTo(px, H);
  }
  for (let y = Math.ceil(bottom / major) * major; y <= top; y += major) {
    const py = Math.round(o.y - y * s) + .5;
    ctx.moveTo(0, py); ctx.lineTo(W, py);
  }
  ctx.stroke();

  // 坐标轴
  const axisColor = 'rgba(55,65,81,.62)';
  ctx.strokeStyle = axisColor; ctx.lineWidth = 1.35;
  if (o.y >= 0 && o.y <= H) {
    ctx.beginPath(); ctx.moveTo(0, Math.round(o.y) + .5); ctx.lineTo(W, Math.round(o.y) + .5); ctx.stroke();
    // 箭头
    drawArrowHead(W - 8, o.y, W - 1, o.y, axisColor, 7);
    ctx.fillStyle = axisColor;
    ctx.font = 'italic 13px "Cambria Math",Georgia,serif';
    ctx.textAlign = 'right'; ctx.textBaseline = 'bottom';
    ctx.fillText('x', W - 10, o.y - 6);
  }
  if (o.x >= 0 && o.x <= W) {
    ctx.beginPath(); ctx.moveTo(Math.round(o.x) + .5, H); ctx.lineTo(Math.round(o.x) + .5, 0); ctx.stroke();
    drawArrowHead(o.x, 8, o.x, 1, axisColor, 7);
    ctx.fillStyle = axisColor;
    ctx.font = 'italic 13px "Cambria Math",Georgia,serif';
    ctx.textAlign = 'left'; ctx.textBaseline = 'top';
    ctx.fillText('y', o.x + 7, 8);
  }

  // 原点
  if (o.x >= -30 && o.x <= W + 30 && o.y >= -30 && o.y <= H + 30) {
    ctx.fillStyle = '#fffdf8';
    ctx.beginPath(); ctx.arc(o.x, o.y, 3.2, 0, TAU); ctx.fill();
    ctx.strokeStyle = axisColor; ctx.lineWidth = 1.4; ctx.stroke();
    ctx.fillStyle = '#7a6f5c';
    ctx.font = '10.5px "PingFang SC","Microsoft YaHei",sans-serif';
    ctx.textAlign = 'right'; ctx.textBaseline = 'top';
    ctx.fillText('O', o.x - 6, o.y + 4);
  }

  // 刻度与数字
  ctx.fillStyle = '#8b8272';
  ctx.font = '9.5px "PingFang SC","Microsoft YaHei",sans-serif';
  ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  const decimals = major < 0.1 ? 2 : major < 1 ? 1 : 0;
  for (let x = Math.ceil(left / major) * major; x <= right; x += major) {
    if (Math.abs(x) < major / 10) continue;
    const px = o.x + x * s;
    if (px < 16 || px > W - 16) continue;
    if (o.y >= -12 && o.y <= H + 12) {
      ctx.strokeStyle = 'rgba(55,65,81,.5)';
      ctx.beginPath(); ctx.moveTo(px, o.y - 3); ctx.lineTo(px, o.y + 3); ctx.stroke();
      ctx.fillText(fmt(x, decimals), px, clamp(o.y + 6, 6, H - 18));
    }
  }
  ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
  for (let y = Math.ceil(bottom / major) * major; y <= top; y += major) {
    if (Math.abs(y) < major / 10) continue;
    const py = o.y - y * s;
    if (py < 14 || py > H - 14) continue;
    if (o.x >= -12 && o.x <= W + 12) {
      ctx.strokeStyle = 'rgba(55,65,81,.5)';
      ctx.beginPath(); ctx.moveTo(o.x - 3, py); ctx.lineTo(o.x + 3, py); ctx.stroke();
      ctx.fillText(fmt(y, decimals), clamp(o.x - 6, 24, W - 8), py - 1);
    }
  }
  ctx.restore();
}

function drawArrowHead(x1, y1, x2, y2, color, size = 6) {
  const a = Math.atan2(y2 - y1, x2 - x1);
  ctx.save();
  ctx.fillStyle = color;
  ctx.beginPath();
  ctx.moveTo(x2, y2);
  ctx.lineTo(x2 - size * Math.cos(a - .38), y2 - size * Math.sin(a - .38));
  ctx.lineTo(x2 - size * Math.cos(a + .38), y2 - size * Math.sin(a + .38));
  ctx.closePath();
  ctx.fill();
  ctx.restore();
}

/* ---------- 函数图像 ---------- */

function activeFn() { return state.functions.find(f => f.id === state.activeFnId) || state.functions[0] || null; }
function fnColor(i) { return PALETTE[i % PALETTE.length]; }

function functionSegments(fn, evaluator) {
  const s = scale2d(), o = origin2d();
  const xmin = (0 - o.x) / s, xmax = (W - o.x) / s;
  const n = Math.max(360, Math.min(1500, Math.round(W * 1.35)));
  const segs = [];
  let seg = null, prevSy = null;
  const closeSeg = () => {
    if (seg && seg.length > 1) segs.push(seg);
    seg = null;
  };
  for (let i = 0; i <= n; i++) {
    const x = lerp(xmin, xmax, i / n);
    let y;
    try { y = evaluator(x); } catch { y = NaN; }
    if (!Number.isFinite(y) || Math.abs(y) > 1e7) { closeSeg(); prevSy = null; continue; }
    const p = w2s({ x, y });
    if (p.y < -H * 2 || p.y > H * 3) { closeSeg(); prevSy = null; continue; }
    if (prevSy === null || Math.abs(p.y - prevSy) > H * 1.4) {
      closeSeg();
      seg = [];
    }
    seg.push(p);
    prevSy = p.y;
  }
  closeSeg();
  return segs;
}

function strokeSegments(segs, color, width = 2.2, dash = []) {
  ctx.save();
  ctx.strokeStyle = color; ctx.lineWidth = width; ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  ctx.setLineDash(dash);
  for (const seg of segs) {
    if (seg.length < 2) continue;
    ctx.beginPath();
    ctx.moveTo(seg[0].x, seg[0].y);
    for (let i = 1; i < seg.length; i++) ctx.lineTo(seg[i].x, seg[i].y);
    ctx.stroke();
  }
  ctx.restore();
}

function drawFunctions() {
  const active = activeFn();
  if (!state.functions.length) {
    ctx.save();
    ctx.fillStyle = 'rgba(124,58,237,.035)';
    ctx.beginPath(); ctx.arc(W * .5, H * .45, 90, 0, TAU); ctx.fill();
    ctx.fillStyle = '#a89d88';
    ctx.font = '13px "PingFang SC","Microsoft YaHei",sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText('输入一个函数或方程，开始画图', W / 2, H * .45 + 120);
    ctx.restore();
    return;
  }
  const sorted = [...state.functions].sort((a, b) => (a.id === state.activeFnId ? 1 : 0) - (b.id === state.activeFnId ? 1 : 0));
  for (const fn of sorted) {
    if (!fn.visible) continue;
    const isAct = fn.id === state.activeFnId;
    const segs = functionSegments(fn, x => evalNode(fn.ast, x));
    if (!isAct) strokeSegments(segs, fn.color, 1.7);
    else {
      // 外发光
      ctx.save();
      ctx.globalAlpha = .13; strokeSegments(segs, fn.color, 8); ctx.restore();
      strokeSegments(segs, fn.color, 2.7);
    }
  }
  if (!active) return;

  const evalF = x => evalNode(active.ast, x);

  // 面积
  const showAreaEl = $('#showArea');
  const areaOn = showAreaEl ? showAreaEl.checked : true;
  if (state.calc && state.calc.integral && showAreaEl && showAreaEl.checked) {
    drawIntegralArea(active, state.calc.integral.a, state.calc.integral.b, evalF);
  }

  // 导函数
  const showDerEl = $('#showDerivative');
  if (showDerEl && showDerEl.checked) {
    const segs = functionSegments(active, x => numericDerivative(evalF, x));
    strokeSegments(segs, active.color, 1.5, [5, 5]);
  }

  // 切线
  const showTanEl = $('#showTangent');
  if (state.calc && state.calc.deriv && showTanEl && showTanEl.checked) {
    const { x0, y0, slope } = state.calc.deriv;
    const s = scale2d(), o = origin2d();
    const xa = (0 - o.x) / s, xb = (W - o.x) / s;
    const ya = y0 + slope * (xa - x0), yb = y0 + slope * (xb - x0);
    const p1 = w2s({ x: xa, y: ya }), p2 = w2s({ x: xb, y: yb });
    ctx.save();
    ctx.strokeStyle = '#b45309'; ctx.lineWidth = 1.5; ctx.setLineDash([7, 5]);
    ctx.beginPath(); ctx.moveTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y); ctx.stroke();
    ctx.restore();
    const pp = w2s({ x: x0, y: y0 });
    drawStone(pp.x, pp.y, '#b45309');
    chip(`切线 k=${fmt(slope, 3)}`, pp.x + 12, pp.y - 24, '#92400e', 'rgba(255,249,237,.95)');
  }

  // 曲线端点标签
  for (const fn of state.functions) {
    if (!fn.visible) continue;
    const segs = functionSegments(fn, x => evalNode(fn.ast, x));
    const last = segs[segs.length - 1];
    if (last && last.length) {
      const p = last[last.length - 1];
      const idx = state.functions.indexOf(fn) + 1;
      if (p.x > 20 && p.x < W - 10 && p.y > 8 && p.y < H - 8) {
        chip(`f${subscript(idx)}(x)`, Math.min(W - 18, p.x + 8), p.y - 14, fn.color);
      }
    }
  }
}

function subscript(n) {
  const map = { 0: '₀', 1: '₁', 2: '₂', 3: '₃', 4: '₄', 5: '₅', 6: '₆', 7: '₇', 8: '₈', 9: '₉' };
  return String(n).split('').map(c => map[c] || c).join('');
}

function drawStone(x, y, color) {
  ctx.save();
  ctx.beginPath(); ctx.arc(x, y, 5, 0, TAU);
  ctx.fillStyle = '#fffdf8'; ctx.fill();
  ctx.lineWidth = 2.2; ctx.strokeStyle = color; ctx.stroke();
  ctx.restore();
}

function drawIntegralArea(fn, a, b, evaluator) {
  const lo = Math.min(a, b), hi = Math.max(a, b);
  const n = 220;
  const pts = [];
  let bad = false;
  for (let i = 0; i <= n; i++) {
    const x = lerp(lo, hi, i / n);
    const y = evaluator(x);
    if (!Number.isFinite(y) || Math.abs(y) > 1e6) { bad = true; break; }
    pts.push(w2s({ x, y }));
  }
  if (bad || pts.length < 2) return;
  const s = scale2d(), o = origin2d();
  const baseY = o.y;
  ctx.save();
  ctx.beginPath();
  ctx.moveTo(pts[0].x, baseY);
  for (const p of pts) ctx.lineTo(p.x, p.y);
  ctx.lineTo(pts[pts.length - 1].x, baseY);
  ctx.closePath();
  const grad = ctx.createLinearGradient(0, 0, 0, H);
  grad.addColorStop(0, 'rgba(124,58,237,.18)');
  grad.addColorStop(1, 'rgba(37,99,235,.06)');
  ctx.fillStyle = grad; ctx.fill();
  ctx.strokeStyle = 'rgba(124,58,237,.24)'; ctx.lineWidth = 1; ctx.stroke();
  // 边界竖线
  ctx.setLineDash([4, 4]); ctx.strokeStyle = 'rgba(124,58,237,.5)';
  for (const x of [lo, hi]) {
    const p = w2s({ x, y: 0 });
    const top = w2s({ x, y: evaluator(x) });
    if (Number.isFinite(top.y)) {
      ctx.beginPath(); ctx.moveTo(p.x, p.y); ctx.lineTo(top.x, top.y); ctx.stroke();
    }
  }
  ctx.restore();
}

/* ---------- 圆锥曲线绘制 ---------- */

function conicPoints(c) {
  const branches = [];
  if (c.kind === 'circle') {
    const arr = [];
    for (let i = 0; i <= 240; i++) {
      const t = i / 240 * TAU;
      arr.push({ x: c.h + c.r * Math.cos(t), y: c.k + c.r * Math.sin(t) });
    }
    return [arr];
  }
  if (c.kind === 'ellipse') {
    const arr = [];
    for (let i = 0; i <= 260; i++) {
      const t = i / 260 * TAU;
      arr.push({ x: c.h + c.a * Math.cos(t), y: c.k + c.b * Math.sin(t) });
    }
    return [arr];
  }
  if (c.kind === 'parabola') {
    const arr = [];
    const p = c.p;
    const maxT = Math.sqrt(Math.max(6, 2 * p * 22));
    for (let i = 0; i <= 320; i++) {
      const t = lerp(-maxT, maxT, i / 320);
      let x, y;
      if (c.orient === 'right') { x = c.h + t * t / (2 * p); y = c.k + t; }
      else if (c.orient === 'left') { x = c.h - t * t / (2 * p); y = c.k + t; }
      else if (c.orient === 'up') { x = c.h + t; y = c.k + t * t / (2 * p); }
      else { x = c.h + t; y = c.k - t * t / (2 * p); }
      arr.push({ x, y });
    }
    return [arr];
  }
  if (c.kind === 'hyperbola') {
    const arrs = [[], []];
    for (let i = 0; i <= 240; i++) {
      const t = lerp(-2.6, 2.6, i / 240);
      for (let k = 0; k < 2; k++) {
        const sign = k ? -1 : 1;
        let x, y;
        if (c.vertical) {
          x = c.h + c.b * Math.sinh(t);
          y = c.k + sign * c.a * Math.cosh(t);
        } else {
          x = c.h + sign * c.a * Math.cosh(t);
          y = c.k + c.b * Math.sinh(t);
        }
        arrs[k].push({ x, y });
      }
    }
    return arrs;
  }
  return branches;
}

function drawConic(c) {
  const branches = conicPoints(c);
  ctx.save();
  for (const br of branches) {
    if (br.length < 2) continue;
    ctx.beginPath();
    const first = w2s(br[0]);
    ctx.moveTo(first.x, first.y);
    for (let i = 1; i < br.length; i++) {
      const p = w2s(br[i]);
      ctx.lineTo(p.x, p.y);
    }
    ctx.strokeStyle = '#7c3aed'; ctx.lineWidth = 2.6; ctx.lineJoin = 'round';
    ctx.stroke();
  }
  // 辅助线
  ctx.setLineDash([5, 5]);
  if (c.kind === 'parabola') {
    ctx.strokeStyle = 'rgba(180,83,9,.55)'; ctx.lineWidth = 1.2;
    if (c.orient === 'right' || c.orient === 'left') {
      const x = c.orient === 'right' ? c.h - c.p / 2 : c.h + c.p / 2;
      const p1 = w2s({ x, y: c.k - 14 }), p2 = w2s({ x, y: c.k + 14 });
      ctx.beginPath(); ctx.moveTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y); ctx.stroke();
      chip(`准线 x = ${fmt(x)}`, p1.x + 6, p1.y + 14, '#92400e', 'rgba(255,249,237,.94)');
    } else {
      const y = c.orient === 'up' ? c.k - c.p / 2 : c.k + c.p / 2;
      const p1 = w2s({ x: c.h - 14, y }), p2 = w2s({ x: c.h + 14, y });
      ctx.beginPath(); ctx.moveTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y); ctx.stroke();
      chip(`准线 y = ${fmt(y)}`, p1.x + 6, p1.y - 14, '#92400e', 'rgba(255,249,237,.94)');
    }
  }
  if (c.kind === 'hyperbola') {
    ctx.strokeStyle = 'rgba(124,58,237,.24)'; ctx.lineWidth = 1.1;
    const slope = c.vertical ? c.a / c.b : c.b / c.a;
    const L = 18;
    for (const sign of [-1, 1]) {
      const dx = L, dy = slope * L * sign;
      const p1 = c.vertical
        ? w2s({ x: c.h - dx, y: c.k - dy })
        : w2s({ x: c.h - dx, y: c.k - dy });
      const p2 = c.vertical
        ? w2s({ x: c.h + dx, y: c.k + dy })
        : w2s({ x: c.h + dx, y: c.k + dy });
      ctx.beginPath(); ctx.moveTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y); ctx.stroke();
    }
  }
  ctx.restore();

  // 中心
  if (c.kind !== 'parabola') {
    const o = w2s({ x: c.h, y: c.k });
    ctx.save();
    ctx.beginPath(); ctx.arc(o.x, o.y, 3.2, 0, TAU);
    ctx.fillStyle = '#7c3aed'; ctx.fill();
    ctx.fillStyle = '#6b21a8'; ctx.font = '10px "PingFang SC","Microsoft YaHei",sans-serif';
    ctx.fillText('中心', o.x + 7, o.y - 6);
    ctx.restore();
  }
  // 焦点
  for (let i = 0; i < (c.foci || []).length; i++) {
    const f = c.foci[i], p = w2s(f);
    ctx.save();
    ctx.beginPath(); ctx.arc(p.x, p.y, 4, 0, TAU);
    ctx.fillStyle = '#fffdf8'; ctx.fill();
    ctx.strokeStyle = '#b45309'; ctx.lineWidth = 2; ctx.stroke();
    ctx.fillStyle = '#92400e'; ctx.font = 'bold 10px "PingFang SC","Microsoft YaHei",sans-serif';
    ctx.fillText('F' + (i + 1), p.x + 7, p.y + 3);
    ctx.restore();
  }
  if (c.kind === 'parabola') {
    const v = w2s({ x: c.h, y: c.k });
    drawStone(v.x, v.y, '#7c3aed');
    chip('顶点', v.x + 9, v.y + 16, '#6b21a8');
  }
}

/* ---------- 3D 坐标系 ---------- */

function spaceScale() { return clamp(Math.min(W, H) / 13.6, 24, 54) * state.space.zoom; }
function project3(p) {
  const { yaw, pitch } = state.space;
  const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
  const rx = p.x * cy - p.y * sy;
  const ry = p.x * sy + p.y * cy;
  const X = rx;
  const Y = p.z * cp - ry * sp;
  const depth = p.z * sp + ry * cp;
  const s = spaceScale();
  return { x: W / 2 + state.space.panX + X * s, y: H / 2 + state.space.panY - Y * s, depth };
}

function renderSpace() {
  const bg = ctx.createLinearGradient(0, 0, 0, H);
  bg.addColorStop(0, '#fffdf8'); bg.addColorStop(1, '#f8f5ed');
  ctx.fillStyle = bg; ctx.fillRect(0, 0, W, H);

  const N = 6, F = -4;
  // 地面网格
  ctx.save();
  ctx.lineWidth = 1;
  for (let i = F; i <= N; i++) {
    const a = project3({ x: i, y: F, z: 0 }), b = project3({ x: i, y: N, z: 0 });
    const c = project3({ x: F, y: i, z: 0 }), d = project3({ x: N, y: i, z: 0 });
    ctx.strokeStyle = i === 0 ? 'rgba(55,65,81,.28)' : 'rgba(80,95,100,.105)';
    ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(c.x, c.y); ctx.lineTo(d.x, d.y); ctx.stroke();
  }
  // 平面淡色
  const corners = [{ x: F, y: F, z: 0 }, { x: N, y: F, z: 0 }, { x: N, y: N, z: 0 }, { x: F, y: N, z: 0 }].map(project3);
  ctx.beginPath(); ctx.moveTo(corners[0].x, corners[0].y);
  for (let i = 1; i < 4; i++) ctx.lineTo(corners[i].x, corners[i].y);
  ctx.closePath();
  ctx.fillStyle = 'rgba(15,118,110,.025)'; ctx.fill();
  ctx.restore();

  function axis(vec, start, color, label) {
    const a = project3(start);
    const o = project3({ x: 0, y: 0, z: 0 });
    const b = project3(vec);
    ctx.save();
    ctx.strokeStyle = color; ctx.lineCap = 'round';
    ctx.globalAlpha = .34; ctx.lineWidth = 1.2;
    ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(o.x, o.y); ctx.stroke();
    ctx.globalAlpha = 1; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(o.x, o.y); ctx.lineTo(b.x, b.y); ctx.stroke();
    drawArrowHead(o.x, o.y, b.x, b.y, color, 8);
    ctx.fillStyle = color;
    ctx.font = 'italic bold 15px "Cambria Math",Georgia,serif';
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(label, b.x + (vec.x === 0 ? 14 : 5), b.y - (vec.z === 0 ? 11 : 9));
    ctx.restore();
  }
  axis({ x: 6.6, y: 0, z: 0 }, { x: -4, y: 0, z: 0 }, '#dc2626', 'x');
  axis({ x: 0, y: 6.6, z: 0 }, { x: 0, y: -4, z: 0 }, '#16a34a', 'y');
  axis({ x: 0, y: 0, z: 6.6 }, { x: 0, y: 0, z: -4 }, '#2563eb', 'z');

  // 刻度
  ctx.save();
  ctx.font = '9px "PingFang SC","Microsoft YaHei",sans-serif';
  for (let i = F; i <= N; i += 2) {
    if (i === 0) continue;
    const px = project3({ x: i, y: 0, z: 0 });
    const py = project3({ x: 0, y: i, z: 0 });
    const pz = project3({ x: 0, y: 0, z: i });
    ctx.fillStyle = 'rgba(220,38,38,.75)'; ctx.textAlign = 'center'; ctx.textBaseline = 'top';
    ctx.fillText(i, px.x, px.y + 5);
    ctx.fillStyle = 'rgba(22,163,74,.8)';
    ctx.fillText(i, py.x + 8, py.y + 5);
    ctx.fillStyle = 'rgba(37,99,235,.8)'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle';
    ctx.fillText(i, pz.x + 7, pz.y);
  }
  ctx.restore();

  // 原点
  const O = project3({ x: 0, y: 0, z: 0 });
  drawStone(O.x, O.y, '#475569');
  ctx.save();
  ctx.fillStyle = '#475569'; ctx.font = '11px "PingFang SC","Microsoft YaHei",sans-serif';
  ctx.fillText('O', O.x - 15, O.y + 14);
  ctx.restore();

  // 空间点
  const sorted = [...state.space.points].sort((a, b) => project3(a).depth - project3(b).depth);
  for (const p of sorted) {
    if (p.visible === false) continue;
    const sp = project3(p);
    const foot = project3({ x: p.x, y: p.y, z: 0 });
    ctx.save();
    ctx.setLineDash([3, 4]); ctx.strokeStyle = 'rgba(15,118,110,.32)'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(sp.x, sp.y); ctx.lineTo(foot.x, foot.y); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(foot.x, foot.y); ctx.lineTo(project3({ x: p.x, y: 0, z: 0 }).x, project3({ x: p.x, y: 0, z: 0 }).y); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(foot.x, foot.y); ctx.lineTo(project3({ x: 0, y: p.y, z: 0 }).x, project3({ x: 0, y: p.y, z: 0 }).y); ctx.stroke();
    ctx.restore();

    ctx.save();
    ctx.beginPath(); ctx.arc(sp.x, sp.y, 5.5, 0, TAU);
    ctx.fillStyle = '#0f766e'; ctx.fill();
    ctx.strokeStyle = '#fffdf8'; ctx.lineWidth = 2; ctx.stroke();
    ctx.restore();
    chip(`${p.label} (${fmt(p.x, 2)}, ${fmt(p.y, 2)}, ${fmt(p.z, 2)})`, sp.x + 10, sp.y - 15, '#0b5f58', 'rgba(245,251,249,.95)');
  }

  // 视角提示
  ctx.save();
  ctx.fillStyle = 'rgba(107,114,128,.65)';
  ctx.font = '10px "PingFang SC","Microsoft YaHei",sans-serif';
  ctx.textAlign = 'right'; ctx.textBaseline = 'bottom';
  ctx.fillText('拖动旋转 · 滚轮缩放', W - 12, H - 10);
  ctx.restore();
}

/* ---------- 图例 ---------- */

function updateLegend() {
  const el = $('#canvasLegend');
  if (!el) return;
  let html = '';
  if (state.mode === 'space') {
    html = '<div><i style="background:#dc2626"></i>x 轴</div><div><i style="background:#16a34a"></i>y 轴</div><div><i style="background:#2563eb"></i>z 轴</div>';
  } else if (state.tab === 'function') {
    if (!state.functions.length) html = '<div>输入函数后显示图像</div>';
    else {
      state.functions.forEach((f, i) => {
        if (!f.visible) return;
        html += `<div><i style="background:${f.color}"></i>f${subscript(i + 1)}(x) = ${esc(f.expr.length > 18 ? f.expr.slice(0, 18) + '…' : f.expr)}</div>`;
      });
      if ($('#showDerivative') && $('#showDerivative').checked) html += '<div><i class="dash" style="color:#7c3aed"></i>导函数 f′(x)</div>';
      if ($('#showArea') && $('#showArea').checked && state.calc && state.calc.integral) html += '<div><i style="background:rgba(124,58,237,.3)"></i>积分区域</div>';
    }
  } else if (state.tab === 'conic') {
    if (state.curve && state.curve.visible !== false) {
      html = `<div><i style="background:#7c3aed"></i>${esc(state.curve.kind === 'circle' ? '圆' : state.curve.kind === 'ellipse' ? '椭圆' : state.curve.kind === 'parabola' ? '抛物线' : '双曲线')}</div><div>${esc(state.curve.equation)}</div>`;
      if (state.circleTangent) html += '<div><i class="dash" style="color:#e11d48"></i>圆的切线</div>';
    }
  } else if (state.tab === 'geometry') {
    html = '<div><i style="background:#0f766e"></i>顶点 / 图形</div><div><i class="dash" style="color:#b45309"></i>平分线 / 中点</div>';
    html += '<div style="color:#8b8272">刻线 = 等边 · 角弧 = 等角 · 箭头 = 平行</div>';
    if (state.geom.marks.length) html += '<div style="color:#15803d">≅ 全等 &nbsp; <span style="color:#b45309">∽ 相似</span></div>';
    const a = getAlphaInfo();
    if (a) html += `<div style="color:#92400e">α = ${fmt(a.value, 2)}°（${esc(a.label)}）</div>`;
    if ((state.geom.transforms || []).length) html += '<div><i style="background:#2563eb"></i>旋转像 &nbsp; <i style="background:#be123c"></i>轴对称像</div>';
  }
  el.innerHTML = html;
  el.hidden = !html;
}

/* ============================================================
   几何模型
   ============================================================ */

function getPt(id) { return state.geom.points.find(p => p.id === id); }
function getShape(id) { return state.geom.shapes.find(s => s.id === id); }
function nextLabel() {
  const letters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
  const n = state.geom.nextLabel++;
  const base = letters[n % 26];
  const round = Math.floor(n / 26);
  return round ? base + round : base;
}
function makePoint(x, y, label) {
  const p = { id: uid('p'), x, y, label: label || nextLabel(), color: GEO_COLORS.point, visible: true };
  state.geom.points.push(p);
  return p;
}

function usedPointLabels() {
  return new Set(state.geom.points.map(p => String(p.label || '')));
}
function primeLabel(base) {
  const used = usedPointLabels();
  const clean = String(base || '').replace(/[′″‴]+$/g, '');
  const primes = ['′', '″', '‴'];
  for (let i = 0; i < primes.length; i++) {
    if (!used.has(clean + primes[i])) return clean + primes[i];
  }
  let k = 1;
  while (used.has(clean + '′' + k)) k++;
  return clean + '′' + k;
}

// 由其它点决定的派生点（当前用于线段中点），拖动端点时自动同步
function syncDerivedPoints() {
  for (const p of state.geom.points) {
    if (!p.derived || p.derived.type !== 'midpoint') continue;
    const a = getPt(p.derived.a), b = getPt(p.derived.b);
    if (!a || !b) continue;
    p.x = (a.x + b.x) / 2;
    p.y = (a.y + b.y) / 2;
  }
}

function polygonPoints(shape) {
  if (!shape) return null;
  const pts = shapePoints(shape);
  if ((shape.type === 'triangle' && pts.length === 3) || (shape.type === 'quad' && pts.length === 4)) return pts;
  return null;
}

// 当前 α 引用的已有角（随顶点拖动实时更新）
function getAlphaInfo() {
  const a = state.geom.alpha;
  if (!a) return null;
  const s = getShape(a.shapeId);
  if (!s) return null;
  if (s.type === 'angle') {
    const pts = shapePoints(s);
    if (pts.length < 3) return null;
    const [prev, v, next] = pts;
    const value = deg(angleAt(v, prev, next));
    if (!Number.isFinite(value)) return null;
    return { value, shape: s, pts, vertexIndex: 1, vertex: v, prev, next, label: `∠${prev.label}${v.label}${next.label}` };
  }
  const pts = polygonPoints(s);
  if (!pts || !Number.isInteger(a.vertexIndex) || a.vertexIndex < 0 || a.vertexIndex >= pts.length) return null;
  const i = a.vertexIndex, n = pts.length;
  const v = pts[i], prev = pts[(i - 1 + n) % n], next = pts[(i + 1) % n];
  if (!v || !prev || !next) return null;
  const value = deg(angleAt(v, prev, next));
  if (!Number.isFinite(value)) return null;
  return {
    value, shape: s, pts, vertexIndex: i, vertex: v, prev, next,
    label: `∠${prev.label}${v.label}${next.label}`
  };
}
function getAlphaValue() {
  const info = getAlphaInfo();
  return info ? info.value : null;
}

function shapePoints(shape) { return shape.points.map(getPt).filter(Boolean); }
function shapeColor(shape) {
  if (shape.color) return shape.color;
  if (shape.type === 'triangle') return GEO_COLORS.triangle;
  if (shape.type === 'quad') return GEO_COLORS.quad;
  if (shape.type === 'circle') return GEO_COLORS.circle;
  if (shape.type === 'angle') return GEO_COLORS.bisector;
  if (shape.type === 'perp-bisector' || shape.type === 'angle-bisector') return GEO_COLORS.bisector;
  return GEO_COLORS.line;
}
function shapeLabel(shape) {
  const pts = shapePoints(shape);
  const labels = pts.map(p => p.label).join('');
  if (shape.type === 'triangle') {
    const m = triangleMetrics(shape);
    return `${m.className} ${labels}`;
  }
  if (shape.type === 'quad') {
    const m = quadMetrics(shape);
    return `${m.className} ${labels}`;
  }
  if (shape.type === 'circle') {
    if (pts.length >= 2) return `圆 ${pts[0].label}（过 ${pts[1].label}）`;
    return '圆';
  }
  if (shape.type === 'segment') return `线段 ${labels}`;
  if (shape.type === 'ray') return `射线 ${labels}`;
  if (shape.type === 'line') return `直线 ${labels}`;
  if (shape.type === 'perp-bisector') return `${labels} 的垂直平分线`;
  if (shape.type === 'angle-bisector') return `∠${pts[1] ? pts[1].label : ''}${pts[0] ? pts[0].label : ''}${pts[2] ? pts[2].label : ''} 的角平分线`;
  if (shape.type === 'angle') return `∠${pts[0] ? pts[0].label : ''}${pts[1] ? pts[1].label : ''}${pts[2] ? pts[2].label : ''}`;
  return shape.type;
}

function triangleMetrics(shape) {
  const p = shapePoints(shape);
  if (p.length < 3) return null;
  const A = p[0], B = p[1], C = p[2];
  const a = dist(B, C), b = dist(C, A), c = dist(A, B);
  const sides = [a, b, c];
  const angles = [
    deg(angleAt(A, B, C)),
    deg(angleAt(B, C, A)),
    deg(angleAt(C, A, B))
  ];
  const area = Math.abs(cross(sub(B, A), sub(C, A))) / 2;
  const perimeter = a + b + c;
  const maxS = Math.max(a, b, c), minS = Math.min(a, b, c);
  const eq = maxS - minS < 0.02 * Math.max(1e-9, maxS) && maxS > 1e-6;
  const pairs = [];
  for (let i = 0; i < 3; i++) for (let j = i + 1; j < 3; j++) {
    if (Math.abs(sides[i] - sides[j]) < 0.018 * Math.max(1e-9, Math.max(sides[i], sides[j]))) pairs.push([i, j]);
  }
  const iso = pairs.length >= 1;
  const right = angles.some(a => Math.abs(a - 90) < 1.2);
  let className = '三角形';
  if (eq) className = '等边三角形';
  else if (iso && right) className = '等腰直角三角形';
  else if (right) className = '直角三角形';
  else if (iso) className = '等腰三角形';
  return { pts: p, labels: p.map(q => q.label), sides, angles, area, perimeter, eq, iso, right, className };
}

function isoscelesApexInfo(shape) {
  if (!shape || shape.type !== 'triangle') return null;
  const pts = shapePoints(shape);
  if (pts.length < 3) return null;
  let idx = null;
  if (shape.kind === 'isosceles-triangle' || shape.kind === 'equilateral') idx = 2;
  else if (shape.kind === 'right-isosceles') idx = 0;
  if (idx === null) {
    const m = triangleMetrics(shape);
    if (!m) return null;
    const s = m.sides;
    const cand = [
      { i: 0, d: Math.abs(s[1] - s[2]) },
      { i: 1, d: Math.abs(s[0] - s[2]) },
      { i: 2, d: Math.abs(s[0] - s[1]) }
    ].sort((a, b) => a.d - b.d);
    if (cand[0].d <= 0.025 * Math.max(...s, 1e-9)) idx = cand[0].i;
  }
  if (idx === null) return null;
  const base = [0, 1, 2].filter(i => i !== idx);
  const v = pts[idx], a = pts[base[0]], b = pts[base[1]];
  if (!v || !a || !b) return null;
  const angle = deg(angleAt(v, a, b));
  if (!Number.isFinite(angle)) return null;
  return { index: idx, base0: base[0], base1: base[1], pts, vertex: v, a, b, angle };
}

function apexEditorHTML(shape) {
  const info = isoscelesApexInfo(shape);
  if (!info) return '';
  const labels = info.pts.map(p => p.label);
  return `<div class="apex-editor">
    <div class="apex-editor-head"><b>编辑顶角</b><span>底边 ${esc(labels[info.base0] + labels[info.base1])} 保持不动</span></div>
    <div class="apex-input-row">
      <input id="apexAngleInput" type="number" min="2" max="178" step="0.1" value="${fmt(info.angle, 2)}" aria-label="等腰三角形顶角">
      <span class="deg">°</span>
      <button class="btn" id="applyApex">应用</button>
    </div>
    <div class="angle-chips">
      <button class="angle-chip" data-apex-angle="60">60°</button>
      <button class="angle-chip" data-apex-angle="90">90°</button>
      <button class="angle-chip" data-apex-angle="120">120°</button>
      <button class="angle-chip" data-apex-angle="30">30°</button>
    </div>
    <div class="apex-hint">顶点 ${esc(labels[info.index])} 会沿底边 ${esc(labels[info.base0] + labels[info.base1])} 的中垂线移动，两腰仍然相等。</div>
  </div>`;
}

function applyApexAngle(value) {
  const sel = state.selected;
  if (!sel || sel.kind !== 'shape') { toast('请先选中一个等腰三角形', 'warn'); return; }
  const s = getShape(sel.id);
  const info = isoscelesApexInfo(s);
  if (!info) { toast('选中的图形不是可编辑顶角的三角形', 'warn'); return; }
  const angle = Number(value);
  if (!Number.isFinite(angle)) { toast('请输入有效的顶角角度', 'warn'); return; }
  if (angle < 2 || angle > 178) { toast('顶角需要在 2° 到 178° 之间', 'warn'); return; }
  const A = info.a, B = info.b, C = info.vertex;
  const baseLen = dist(A, B);
  if (baseLen < 1e-6) { toast('底边太短，无法设置顶角', 'warn'); return; }
  const m = mid(A, B);
  let n = norm(perp(sub(B, A)));
  const side = dot(sub(C, m), n);
  if (side < 0) n = mul(n, -1);
  else if (Math.abs(side) < 1e-9 && n.y < 0) n = mul(n, -1);
  const h = (baseLen / 2) / Math.tan(rad(angle) / 2);
  if (!Number.isFinite(h)) { toast('无法计算顶角位置', 'warn'); return; }
  pushHistory();
  C.x = m.x + n.x * h;
  C.y = m.y + n.y * h;
  syncDerivedPoints();
  renderAllPanels(); draw(); saveSoon();
  toast(`已把顶角 ${info.pts[info.index].label} 设为 ${fmt(angle, 2)}°`, 'ok');
}

function applyApexFromUI(value) {
  const input = $('#apexAngleInput');
  applyApexAngle(value === undefined ? (input ? parseFloat(input.value) : NaN) : value);
}

function quadAngleEditorHTML(s) {
  if (!s || s.type !== 'quad' || !['parallelogram', 'rhombus'].includes(s.kind)) return '';
  const pts = shapePoints(s);
  if (pts.length < 4) return '';
  const angle = deg(angleAt(pts[0], pts[1], pts[3]));
  return `<div class="apex-editor quad-editor">
    <div class="apex-editor-head"><b>编辑内角</b><span>∠${esc(pts[0].label)} · ${s.kind === 'rhombus' ? '四边等长' : '边长不变'}</span></div>
    <div class="apex-input-row">
      <input id="quadAngleInput" type="number" min="5" max="175" step="0.1" value="${fmt(angle, 2)}" aria-label="平行四边形或菱形内角">
      <span class="deg">°</span>
      <button class="btn" id="applyQuadAngle">应用</button>
    </div>
    <div class="angle-chips">
      <button class="angle-chip" data-quad-angle="45">45°</button>
      <button class="angle-chip" data-quad-angle="60">60°</button>
      <button class="angle-chip" data-quad-angle="75">75°</button>
      <button class="angle-chip" data-quad-angle="120">120°</button>
      <button class="angle-chip" data-quad-angle="135">135°</button>
    </div>
    <div class="apex-hint">∠${esc(pts[1].label)} = ∠${esc(pts[3].label)} = 180° − θ，对边保持平行${s.kind === 'rhombus' ? '，四条边仍然相等' : '，边长不变'}。</div>
  </div>`;
}

function applyQuadAngle(value) {
  const sel = state.selected;
  if (!sel || sel.kind !== 'shape') { toast('请先选中一个平行四边形或菱形', 'warn'); return; }
  const s = getShape(sel.id);
  if (!s || s.type !== 'quad' || !['parallelogram', 'rhombus'].includes(s.kind)) {
    toast('选中的图形不是可编辑内角的平行四边形或菱形', 'warn');
    return;
  }
  const pts = shapePoints(s);
  if (pts.length < 4) return;
  const angle = Number(value);
  if (!Number.isFinite(angle)) { toast('请输入有效的角度', 'warn'); return; }
  if (angle < 5 || angle > 175) { toast('内角需要在 5° 到 175° 之间', 'warn'); return; }
  const A = pts[0], B = pts[1], C = pts[2], D = pts[3];
  const sideAB = dist(A, B);
  const sideAD = s.kind === 'rhombus' ? sideAB : dist(A, D);
  if (sideAB < 1e-6 || sideAD < 1e-6) { toast('边长太短，无法设置角度', 'warn'); return; }
  const dir = norm(sub(B, A));
  const sign = cross(sub(B, A), sub(D, A)) < 0 ? -1 : 1;
  const newAD = mul(rotate(dir, sign * rad(angle)), sideAD);
  const newD = { x: A.x + newAD.x, y: A.y + newAD.y };
  pushHistory();
  D.x = newD.x; D.y = newD.y;
  C.x = B.x + newAD.x; C.y = B.y + newAD.y;
  syncDerivedPoints();
  renderAllPanels(); draw(); saveSoon();
  toast(`已把 ${s.kind === 'rhombus' ? '菱形' : '平行四边形'}的内角设为 ${fmt(angle, 2)}°`, 'ok');
}

function applyQuadFromUI(value) {
  const input = $('#quadAngleInput');
  applyQuadAngle(value === undefined ? (input ? parseFloat(input.value) : NaN) : value);
}

function quadMetrics(shape) {
  const p = shapePoints(shape);
  if (p.length < 4) return null;
  const sides = [], angles = [];
  for (let i = 0; i < 4; i++) {
    sides.push(dist(p[i], p[(i + 1) % 4]));
    angles.push(deg(angleAt(p[i], p[(i + 1) % 4], p[(i + 3) % 4])));
  }
  let area = 0;
  for (let i = 0; i < 4; i++) area += p[i].x * p[(i + 1) % 4].y - p[(i + 1) % 4].x * p[i].y;
  area = Math.abs(area) / 2;
  const perimeter = sides.reduce((a, b) => a + b, 0);
  const allRight = angles.every(a => Math.abs(a - 90) < 1.2);
  const maxS = Math.max(...sides), minS = Math.min(...sides);
  const allEq = maxS - minS < 0.02 * Math.max(1e-9, maxS);
  const par1 = Math.abs(cross(norm(sub(p[1], p[0])), norm(sub(p[2], p[3])))) < 0.035;
  const par2 = Math.abs(cross(norm(sub(p[2], p[1])), norm(sub(p[3], p[0])))) < 0.035;
  const para = par1 && par2;
  let className = '四边形';
  if (allRight && allEq) className = '正方形';
  else if (allRight) className = '矩形';
  else if (allEq && para) className = '菱形';
  else if (para) className = '平行四边形';
  return { pts: p, labels: p.map(q => q.label), sides, angles, area, perimeter, allRight, allEq, para, className };
}

/* ---------- 历史记录（函数 / 圆锥曲线 / 几何 / 空间点） ---------- */

const cloneData = v => v == null ? v : JSON.parse(JSON.stringify(v));

function captureSnapshot() {
  return {
    mode: state.mode,
    tab: state.tab,
    functions: state.functions.map(f => ({ id: f.id, expr: f.expr, color: f.color, visible: f.visible })),
    activeFnId: state.activeFnId,
    curve: cloneData(state.curve),
    conicResult: cloneData(state.conicResult),
    conicType: state.conicType,
    conicParams: cloneData(state.conicParams),
    circleTangent: cloneData(state.circleTangent),
    calc: cloneData(state.calc),
    rotateExpr: state.rotateExpr,
    keepOriginal: state.keepOriginal,
    geom: cloneData(state.geom),
    spacePoints: cloneData(state.space.points),
    spaceNextLabel: state.space.nextLabel || 0
  };
}

function applySnapshot(snap) {
  try {
    const s = typeof snap === 'string' ? JSON.parse(snap) : snap;
    const fns = [];
    for (const f of (s.functions || [])) {
      if (!f || typeof f.expr !== 'string') continue;
      try {
        fns.push({ id: f.id || uid('f'), expr: f.expr, ast: parseExpression(f.expr), color: f.color || fnColor(fns.length), visible: f.visible !== false });
      } catch { /* skip broken */ }
    }
    state.functions = fns;
    state.activeFnId = fns.some(f => f.id === s.activeFnId) ? s.activeFnId : (fns[0] ? fns[0].id : null);
    state.curve = cloneData(s.curve) || null;
    state.conicResult = cloneData(s.conicResult) || null;
    state.circleTangent = cloneData(s.circleTangent) || null;
    state.tangentPicking = false;
    if (s.conicType) state.conicType = s.conicType;
    if (s.conicParams) state.conicParams = Object.assign(cloneData(state.conicParams), cloneData(s.conicParams));
    state.calc = cloneData(s.calc) || null;
    state.rotateExpr = typeof s.rotateExpr === 'string' ? s.rotateExpr : state.rotateExpr;
    state.keepOriginal = typeof s.keepOriginal === 'boolean' ? s.keepOriginal : true;
    if (s.geom) {
      state.geom = Object.assign({ points: [], shapes: [], marks: [], transforms: [], alpha: null, nextLabel: 0, snap: true, showLabels: true, horizontalBase: true }, cloneData(s.geom));
      if (!Array.isArray(state.geom.shapes)) state.geom.shapes = [];
      if (!Array.isArray(state.geom.marks)) state.geom.marks = [];
      if (!Array.isArray(state.geom.transforms)) state.geom.transforms = [];
    }
    if (Array.isArray(s.spacePoints)) {
      state.space.points = cloneData(s.spacePoints);
      state.space.nextLabel = Number.isFinite(s.spaceNextLabel) ? s.spaceNextLabel : state.space.points.length;
    }
    state.pending = []; state.preview = null; state.markFirst = null; state.transformTarget = null; state.hover = null;
    syncDerivedPoints();
    if (!getPtVisibleSelection()) state.selected = null;
    if (s.mode && s.mode !== state.mode && ['plane', 'space', 'blank'].includes(s.mode)) setMode(s.mode);
    if (s.mode !== 'space' && s.tab && s.tab !== state.tab && ['function', 'conic', 'geometry'].includes(s.tab)) setTab(s.tab);
    if (s.mode && ['plane', 'space', 'blank'].includes(s.mode)) state.mode = s.mode;
    if (s.tab && ['function', 'conic', 'geometry'].includes(s.tab)) state.tab = s.tab;
    syncSnapToggles();
    const input = $('#exprInput');
    const act = activeFn();
    if (input && act) input.value = act.expr;
    updateTransformUI();
    updateTangentUI();
    renderAllPanels();
    draw();
    saveSoon();
    return true;
  } catch (err) {
    toast('无法恢复历史状态', 'bad');
    return false;
  }
}

function pushHistory() {
  state.history.push(captureSnapshot());
  if (state.history.length > 60) state.history.shift();
  state.future = [];
  updateHistoryButtons();
}
function getPtVisibleSelection() {
  const s = state.selected;
  if (!s) return false;
  if (s.kind === 'point') return !!getPt(s.id);
  if (s.kind === 'shape') return !!getShape(s.id);
  if (s.kind === 'mark') return state.geom.marks.some(m => m.id === s.id);
  return false;
}
function undo() {
  if (!state.history.length) return;
  state.future.push(captureSnapshot());
  const snap = state.history.pop();
  if (applySnapshot(snap)) {
    toast('已撤回上一步', '');
  } else {
    state.history.push(snap);
  }
  updateHistoryButtons();
}
function redo() {
  if (!state.future.length) return;
  state.history.push(captureSnapshot());
  const snap = state.future.pop();
  if (applySnapshot(snap)) {
    toast('已重做', '');
  } else {
    state.future.push(snap);
  }
  updateHistoryButtons();
}
function updateHistoryButtons() {
  const u = $('#undoBtn'), r = $('#redoBtn');
  if (u) u.disabled = !state.history.length;
  if (r) r.disabled = !state.future.length;
}

/* ---------- 绘制辅助 ---------- */

function screenPoly(pts) { return pts.map(w2s); }
function drawPolyline(pts, color, width = 2.2, fill = null, dash = []) {
  if (pts.length < 2) return;
  ctx.save();
  ctx.lineWidth = width; ctx.strokeStyle = color; ctx.lineJoin = 'round'; ctx.lineCap = 'round';
  ctx.setLineDash(dash);
  ctx.beginPath();
  ctx.moveTo(pts[0].x, pts[0].y);
  for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y);
  if (fill) { ctx.closePath(); ctx.fillStyle = fill; ctx.fill(); }
  ctx.stroke();
  ctx.restore();
}
function drawLineWorld(a, b, color, width, dash = [], extend = 1e4) {
  const d = sub(b, a);
  const l = Math.hypot(d.x, d.y) || 1;
  const u = { x: d.x / l, y: d.y / l };
  const p1 = w2s({ x: a.x - u.x * extend, y: a.y - u.y * extend });
  const p2 = w2s({ x: a.x + u.x * extend, y: a.y + u.y * extend });
  ctx.save();
  ctx.strokeStyle = color; ctx.lineWidth = width; ctx.setLineDash(dash);
  ctx.beginPath(); ctx.moveTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y); ctx.stroke();
  ctx.restore();
}
function drawRayWorld(o, through, color, width, dash = [], len = 1e4) {
  const u = norm(sub(through, o));
  const p1 = w2s(o), p2 = w2s({ x: o.x + u.x * len, y: o.y + u.y * len });
  ctx.save();
  ctx.strokeStyle = color; ctx.lineWidth = width; ctx.setLineDash(dash);
  ctx.beginPath(); ctx.moveTo(p1.x, p1.y); ctx.lineTo(p2.x, p2.y); ctx.stroke();
  ctx.restore();
}

function drawRightAngleWorld(v, a, b, color, sizePx = 11) {
  const pv = w2s(v), pa = w2s(a), pb = w2s(b);
  const u = norm(sub(pa, pv)), w = norm(sub(pb, pv));
  const q1 = { x: pv.x + u.x * sizePx, y: pv.y + u.y * sizePx };
  const q2 = { x: q1.x + w.x * sizePx, y: q1.y + w.y * sizePx };
  const q3 = { x: pv.x + w.x * sizePx, y: pv.y + w.y * sizePx };
  ctx.save();
  ctx.strokeStyle = color; ctx.lineWidth = 1.35; ctx.lineJoin = 'miter';
  ctx.beginPath(); ctx.moveTo(q1.x, q1.y); ctx.lineTo(q2.x, q2.y); ctx.lineTo(q3.x, q3.y); ctx.stroke();
  ctx.restore();
}

function drawTicksWorld(a, b, count, color, size = 6, alpha = 1) {
  const pa = w2s(a), pb = w2s(b);
  const d = sub(pb, pa), l = Math.hypot(d.x, d.y) || 1;
  const u = { x: d.x / l, y: d.y / l }, n = { x: -u.y, y: u.x };
  const m = mid(pa, pb);
  const gap = 5.5;
  ctx.save();
  ctx.globalAlpha = alpha;
  ctx.strokeStyle = color; ctx.lineWidth = 1.7; ctx.lineCap = 'round';
  for (let i = 0; i < count; i++) {
    const off = (i - (count - 1) / 2) * gap;
    const cx = m.x + u.x * off, cy = m.y + u.y * off;
    ctx.beginPath();
    ctx.moveTo(cx - n.x * size, cy - n.y * size);
    ctx.lineTo(cx + n.x * size, cy + n.y * size);
    ctx.stroke();
  }
  ctx.restore();
}

function drawAngleArcsWorld(v, a, b, count, color, r = 19) {
  const pv = w2s(v), pa = w2s(a), pb = w2s(b);
  let a1 = Math.atan2(pa.y - pv.y, pa.x - pv.x);
  let a2 = Math.atan2(pb.y - pv.y, pb.x - pv.x);
  let diff = a2 - a1;
  while (diff > Math.PI) diff -= TAU;
  while (diff < -Math.PI) diff += TAU;
  ctx.save();
  ctx.strokeStyle = color; ctx.lineWidth = 1.6; ctx.lineCap = 'round';
  for (let i = 0; i < count; i++) {
    ctx.beginPath();
    ctx.arc(pv.x, pv.y, r + i * 4.5, a1, a1 + diff, diff < 0);
    ctx.stroke();
  }
  ctx.restore();
}

function drawParallelMark(a, b, count, color) {
  const pa = w2s(a), pb = w2s(b);
  const d = sub(pb, pa), l = Math.hypot(d.x, d.y) || 1;
  const u = { x: d.x / l, y: d.y / l }, n = { x: -u.y, y: u.x };
  const m = mid(pa, pb);
  ctx.save();
  ctx.strokeStyle = color; ctx.lineWidth = 1.5; ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  for (let i = 0; i < count; i++) {
    const off = (i - (count - 1) / 2) * 6;
    const c = { x: m.x + u.x * off, y: m.y + u.y * off };
    ctx.beginPath();
    ctx.moveTo(c.x - u.x * 4 + n.x * 4, c.y - u.y * 4 + n.y * 4);
    ctx.lineTo(c.x + u.x * 2, c.y + u.y * 2);
    ctx.lineTo(c.x - u.x * 4 - n.x * 4, c.y - u.y * 4 - n.y * 4);
    ctx.stroke();
  }
  ctx.restore();
}

function centroidOf(pts) {
  return { x: pts.reduce((s, p) => s + p.x, 0) / pts.length, y: pts.reduce((s, p) => s + p.y, 0) / pts.length };
}

/* ---------- 几何图形绘制 ---------- */

function drawGeometry() {
  const g = state.geom;
  syncDerivedPoints();
  if (!g.points.length && !g.shapes.length && !g.marks.length) {
    drawGeoEmpty();
    return;
  }
  // 图形
  for (const s of g.shapes) {
    if (!s.visible) continue;
    drawShapeBase(s);
  }
  // 变换像与原图的联系
  drawTransformLinks();
  // 基础几何记号
  for (const s of g.shapes) {
    if (!s.visible) continue;
    drawShapeMarks(s);
  }
  drawDerivedMarks();
  drawAlphaHighlight();
  // 全等 / 相似
  for (const m of g.marks) {
    if (!m.visible) continue;
    drawRelationMark(m);
  }
  // 变换目标高亮
  if (state.transformTarget) {
    const tc = state.tool === 'reflect' ? 'rgba(190,18,60,.75)' : 'rgba(37,99,235,.75)';
    if (state.transformTarget.kind === 'shape') {
      const s = getShape(state.transformTarget.id);
      if (s) drawShapeHover(s, tc);
    } else {
      const p = getPt(state.transformTarget.id);
      if (p) {
        const sp = w2s(p);
        ctx.save();
        ctx.beginPath(); ctx.arc(sp.x, sp.y, 12, 0, TAU);
        ctx.strokeStyle = tc; ctx.lineWidth = 3; ctx.setLineDash([3, 3]); ctx.stroke();
        ctx.restore();
      }
    }
  }
  // 选中图形（放在点下面，避免盖住顶点）
  if (state.selected && state.selected.kind === 'shape') {
    const s = getShape(state.selected.id);
    if (s) drawShapeSelection(s);
  }
  // 点
  for (const p of g.points) {
    if (!p.visible) continue;
    const sp = w2s(p);
    if (sp.x < -40 || sp.x > W + 40 || sp.y < -40 || sp.y > H + 40) continue;
    const isSel = state.selected && state.selected.kind === 'point' && state.selected.id === p.id;
    if (isSel) {
      ctx.save();
      ctx.beginPath(); ctx.arc(sp.x, sp.y, 9, 0, TAU);
      ctx.strokeStyle = 'rgba(245,158,11,.55)'; ctx.lineWidth = 4; ctx.stroke();
      ctx.restore();
    }
    ctx.save();
    ctx.beginPath(); ctx.arc(sp.x, sp.y, 4.4, 0, TAU);
    ctx.fillStyle = p.color || GEO_COLORS.point; ctx.fill();
    ctx.strokeStyle = '#fffdf8'; ctx.lineWidth = 1.8; ctx.stroke();
    ctx.restore();
    if (g.showLabels) {
      ctx.save();
      ctx.fillStyle = '#334155';
      ctx.font = 'bold 11px "Cambria Math",Georgia,serif';
      ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
      const off = pointLabelOffset(p);
      ctx.fillText(p.label, sp.x + off.x, sp.y + off.y);
      ctx.restore();
    }
  }
  // 悬停
  if (state.hover) {
    if (state.hover.kind === 'shape') {
      const s = getShape(state.hover.id);
      if (s) drawShapeHover(s);
    } else if (state.hover.kind === 'point') {
      const p = getPt(state.hover.id);
      if (p) {
        const sp = w2s(p);
        ctx.save(); ctx.beginPath(); ctx.arc(sp.x, sp.y, 8, 0, TAU);
        ctx.strokeStyle = 'rgba(15,118,110,.35)'; ctx.lineWidth = 2; ctx.stroke(); ctx.restore();
      }
    }
  }
  if (state.selected && state.selected.kind === 'mark') {
    const m = g.marks.find(x => x.id === state.selected.id);
    if (m) {
      const tm = triangleMetrics(getShape(m.a));
      if (tm) {
        const c = w2s(centroidOf(tm.pts));
        ctx.save(); ctx.beginPath(); ctx.arc(c.x, c.y, 24, 0, TAU);
        ctx.strokeStyle = 'rgba(245,158,11,.35)'; ctx.lineWidth = 2; ctx.setLineDash([3, 4]); ctx.stroke(); ctx.restore();
      }
    }
  }
  // 待标记的第一个三角形
  if (state.markFirst) {
    const s = getShape(state.markFirst);
    if (s) drawShapeHover(s, 'rgba(245,158,11,.9)');
  }
}

function pointLabelOffset(p) {
  const shapes = state.geom.shapes.filter(s => s.points.includes(p.id) && s.visible);
  if (!shapes.length) return { x: 8, y: -7 };
  let cx = 0, cy = 0, n = 0;
  for (const s of shapes) {
    const pts = shapePoints(s);
    if (s.type === 'triangle' || s.type === 'quad') {
      const c = centroidOf(pts); cx += c.x; cy += c.y; n++;
    }
  }
  if (!n) return { x: 8, y: -7 };
  const c = w2s({ x: cx / n, y: cy / n });
  const sp = w2s(p);
  const u = norm({ x: sp.x - c.x, y: sp.y - c.y });
  return { x: u.x * 13 + (u.x >= 0 ? 2 : -10), y: u.y * 13 - 2 };
}

function drawShapeBase(s) {
  const color = shapeColor(s);
  if (s.type === 'triangle' || s.type === 'quad') {
    const pts = screenPoly(shapePoints(s));
    if (pts.length >= 3) {
      ctx.save();
      ctx.beginPath(); ctx.moveTo(pts[0].x, pts[0].y);
      for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y);
      ctx.closePath();
      ctx.fillStyle = hexA(color, .055); ctx.fill();
      ctx.strokeStyle = color; ctx.lineWidth = 2.1; ctx.lineJoin = 'round'; ctx.stroke();
      ctx.restore();
    }
  } else if (s.type === 'circle') {
    const pts = shapePoints(s);
    if (pts.length >= 2) {
      const c = w2s(pts[0]), r = dist(pts[0], pts[1]) * scale2d();
      ctx.save();
      ctx.beginPath(); ctx.arc(c.x, c.y, r, 0, TAU);
      ctx.fillStyle = hexA(color, .035); ctx.fill();
      ctx.strokeStyle = color; ctx.lineWidth = 2.1; ctx.stroke();
      // 半径虚线
      ctx.setLineDash([4, 5]); ctx.strokeStyle = hexA(color, .5); ctx.lineWidth = 1;
      const rp = w2s(pts[1]);
      ctx.beginPath(); ctx.moveTo(c.x, c.y); ctx.lineTo(rp.x, rp.y); ctx.stroke();
      ctx.restore();
      const m = mid(c, rp);
      ctx.save();
      ctx.fillStyle = color; ctx.font = 'italic 10px "Cambria Math",Georgia,serif';
      ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
      ctx.fillText('r', m.x + 4, m.y - 4);
      ctx.restore();
    }
  } else if (s.type === 'angle') {
    const p = shapePoints(s);
    if (p.length >= 3) {
      drawPolyline([p[1], p[0]].map(w2s), color, 2.1);
      drawPolyline([p[1], p[2]].map(w2s), color, 2.1);
      drawAngleArcsWorld(p[1], p[0], p[2], 1, color, 22);
      if (!(state.geom.alpha && state.geom.alpha.shapeId === s.id)) {
        const mark = deg(angleAt(p[1], p[0], p[2]));
        const pv = w2s(p[1]), pa = w2s(p[0]), pb = w2s(p[2]);
        const u1 = norm(sub(pa, pv)), u2 = norm(sub(pb, pv));
        let d = norm({ x: u1.x + u2.x, y: u1.y + u2.y });
        if (Math.hypot(d.x, d.y) < 1e-9) d = perp(u1);
        chip(`∠${p[0].label}${p[1].label}${p[2].label} = ${fmt(mark, 2)}°`, pv.x + d.x * 54, pv.y + d.y * 54, '#92400e', 'rgba(255,249,237,.95)', 'center');
      }
    }
  } else if (s.type === 'segment') {
    const p = shapePoints(s);
    if (p.length >= 2) drawPolyline(p.map(w2s), color, 2.1);
  } else if (s.type === 'ray') {
    const p = shapePoints(s);
    if (p.length >= 2) drawRayWorld(p[0], p[1], color, 2.1);
  } else if (s.type === 'line') {
    const p = shapePoints(s);
    if (p.length >= 2) drawLineWorld(p[0], p[1], color, 2.1);
  } else if (s.type === 'perp-bisector') {
    const p = shapePoints(s);
    if (p.length >= 2) {
      const m = mid(p[0], p[1]);
      const n = perp(sub(p[1], p[0]));
      drawLineWorld({ x: m.x - n.x, y: m.y - n.y }, { x: m.x + n.x, y: m.y + n.y }, GEO_COLORS.bisector, 1.7, [7, 5]);
      drawRightAngleWorld(m, p[0], { x: m.x + n.x, y: m.y + n.y }, GEO_COLORS.bisector, 9);
      drawTicksWorld(p[0], m, 1, GEO_COLORS.bisector, 4.5, .9);
      drawTicksWorld(m, p[1], 1, GEO_COLORS.bisector, 4.5, .9);
      const sm = w2s(m);
      chip('垂直平分线', sm.x + 10, sm.y - 26, '#92400e', 'rgba(255,249,237,.94)');
    }
  } else if (s.type === 'angle-bisector') {
    const p = shapePoints(s);
    if (p.length >= 3) {
      const o = p[0], a = p[1], b = p[2];
      const u = norm(sub(a, o)), v = norm(sub(b, o));
      let d = norm({ x: u.x + v.x, y: u.y + v.y });
      if (Math.hypot(d.x, d.y) < 1e-9) d = perp(u);
      drawRayWorld(o, { x: o.x + d.x, y: o.y + d.y }, GEO_COLORS.bisector, 1.8, [7, 5], 5.2);
      // 两侧等角弧
      drawAngleArcsWorld(o, a, { x: o.x + d.x, y: o.y + d.y }, 1, GEO_COLORS.bisector, 24);
      drawAngleArcsWorld(o, { x: o.x + d.x, y: o.y + d.y }, b, 1, GEO_COLORS.bisector, 24);
      const lp = w2s({ x: o.x + d.x * 2.6, y: o.y + d.y * 2.6 });
      chip('角平分线', lp.x + 9, lp.y - 12, '#92400e', 'rgba(255,249,237,.94)');
    }
  }
}

function equalGroups(values, close) {
  const groups = [], used = new Array(values.length).fill(false);
  for (let i = 0; i < values.length; i++) {
    if (used[i]) continue;
    const group = [i];
    for (let j = i + 1; j < values.length; j++) {
      if (!used[j] && close(values[i], values[j])) { group.push(j); used[j] = true; }
    }
    if (group.length > 1) { used[i] = true; groups.push(group); }
  }
  return groups;
}

function drawEqualSideMarks(pts, sides, color, size = 5.5) {
  const groups = equalGroups(sides, (a, b) => Math.abs(a - b) < 0.018 * Math.max(1e-9, Math.max(a, b)));
  groups.forEach((grp, gi) => {
    for (const idx of grp) drawTicksWorld(pts[idx], pts[(idx + 1) % pts.length], gi + 1, color, size, .85);
  });
}

function drawEqualAngleMarks(pts, angles, color, radius = 17) {
  const n = pts.length;
  const groups = equalGroups(angles, (a, b) => Math.abs(a - b) < 1.2);
  groups.forEach((grp, gi) => {
    // 所有角都是直角时用直角符号即可，避免与方框记号重叠
    if (grp.every(i => Math.abs(angles[i] - 90) < 1.2)) return;
    for (const idx of grp) {
      drawAngleArcsWorld(pts[idx], pts[(idx + 1) % n], pts[(idx + n - 1) % n], gi + 1, color, radius);
    }
  });
}

function drawShapeMarks(s) {
  const color = shapeColor(s);
  if (s.type === 'triangle') {
    const m = triangleMetrics(s);
    if (!m) return;
    drawEqualSideMarks(m.pts, m.sides, color);
    drawEqualAngleMarks(m.pts, m.angles, color, 16);
    // 直角
    for (let i = 0; i < 3; i++) {
      if (Math.abs(m.angles[i] - 90) < 1.2) {
        drawRightAngleWorld(m.pts[i], m.pts[(i + 1) % 3], m.pts[(i + 2) % 3], color, 10);
      }
    }
  } else if (s.type === 'quad') {
    const m = quadMetrics(s);
    if (!m) return;
    // 平行标记
    let c1 = 0, c2 = 0;
    if (Math.abs(cross(norm(sub(m.pts[1], m.pts[0])), norm(sub(m.pts[2], m.pts[3])))) < 0.04) c1 = 1;
    if (Math.abs(cross(norm(sub(m.pts[2], m.pts[1])), norm(sub(m.pts[3], m.pts[0])))) < 0.04) c2 = 1;
    if (c1) { drawParallelMark(m.pts[0], m.pts[1], 1, color); drawParallelMark(m.pts[2], m.pts[3], 1, color); }
    if (c2) { drawParallelMark(m.pts[1], m.pts[2], 2, color); drawParallelMark(m.pts[3], m.pts[0], 2, color); }
    drawEqualSideMarks(m.pts, m.sides, color, 5);
    drawEqualAngleMarks(m.pts, m.angles, color, 16);
    // 直角
    for (let i = 0; i < 4; i++) {
      if (Math.abs(m.angles[i] - 90) < 1.2) drawRightAngleWorld(m.pts[i], m.pts[(i + 1) % 4], m.pts[(i + 3) % 4], color, 9);
    }
  }
}

function drawDerivedMarks() {
  for (const p of state.geom.points) {
    if (!p.visible || !p.derived || p.derived.type !== 'midpoint') continue;
    const a = getPt(p.derived.a), b = getPt(p.derived.b);
    if (!a || !b) continue;
    drawTicksWorld(a, p, 1, '#b45309', 4.5, .9);
    drawTicksWorld(p, b, 1, '#b45309', 4.5, .9);
  }
}

function drawAlphaHighlight() {
  const info = getAlphaInfo();
  if (!info) return;
  const pv = w2s(info.vertex), pa = w2s(info.prev), pb = w2s(info.next);
  const a1 = Math.atan2(pa.y - pv.y, pa.x - pv.x);
  const a2 = Math.atan2(pb.y - pv.y, pb.x - pv.x);
  let diff = a2 - a1;
  while (diff > Math.PI) diff -= TAU;
  while (diff < -Math.PI) diff += TAU;
  const r = 38;
  ctx.save();
  ctx.beginPath();
  ctx.moveTo(pv.x, pv.y);
  ctx.arc(pv.x, pv.y, r, a1, a1 + diff, diff < 0);
  ctx.closePath();
  ctx.fillStyle = 'rgba(217,119,6,.10)'; ctx.fill();
  ctx.restore();
  drawAngleArcsWorld(info.vertex, info.prev, info.next, 2, '#d97706', r + 2);
  const u1 = norm(sub(pa, pv)), u2 = norm(sub(pb, pv));
  let d = norm({ x: u1.x + u2.x, y: u1.y + u2.y });
  if (Math.hypot(d.x, d.y) < 1e-9) d = perp(u1);
  chip(`α = ${fmt(info.value, 2)}°`, pv.x + d.x * (r + 22), pv.y + d.y * (r + 22), '#92400e', 'rgba(255,249,237,.95)', 'center');
}

function objectCenter(kind, id) {
  if (kind === 'point') {
    const p = getPt(id);
    return p ? { x: p.x, y: p.y } : null;
  }
  const s = getShape(id);
  if (!s) return null;
  const pts = shapePoints(s);
  if (!pts.length) return null;
  return centroidOf(pts);
}

function drawTransformLinks() {
  for (const t of (state.geom.transforms || [])) {
    if (!t || t.imageKind === t.sourceKind && t.imageId === t.sourceId) continue;
    const a = objectCenter(t.sourceKind, t.sourceId);
    const b = objectCenter(t.imageKind, t.imageId);
    if (!a || !b) continue;
    const pa = w2s(a), pb = w2s(b);
    const color = t.color || '#2563eb';
    ctx.save();
    ctx.strokeStyle = hexA(color, .55); ctx.lineWidth = 1.2; ctx.setLineDash([4, 5]);
    ctx.beginPath(); ctx.moveTo(pa.x, pa.y); ctx.lineTo(pb.x, pb.y); ctx.stroke();
    ctx.restore();
    for (const p of [pa, pb]) {
      ctx.save();
      ctx.beginPath(); ctx.arc(p.x, p.y, 3, 0, TAU);
      ctx.fillStyle = '#fffdf9'; ctx.fill();
      ctx.strokeStyle = color; ctx.lineWidth = 1.3; ctx.stroke();
      ctx.restore();
    }
    const label = t.type === 'rotate'
      ? `旋转 ${fmt(t.angle, 2)}°`
      : '轴对称';
    chip(label, (pa.x + pb.x) / 2, (pa.y + pb.y) / 2 - 13, color, 'rgba(255,253,249,.95)', 'center');
  }
}

function drawShapeHover(s, color = 'rgba(15,118,110,.55)') {
  if (!s) return;
  if (s.type === 'triangle' || s.type === 'quad') {
    const pts = screenPoly(shapePoints(s));
    if (pts.length >= 3) {
      ctx.save();
      drawPolyline(pts.concat([pts[0]]), color, 4, hexA(color, .08));
      ctx.restore();
    }
  } else if (s.type === 'circle') {
    const p = shapePoints(s);
    if (p.length >= 2) {
      const c = w2s(p[0]), r = dist(p[0], p[1]) * scale2d();
      ctx.save(); ctx.beginPath(); ctx.arc(c.x, c.y, r, 0, TAU);
      ctx.strokeStyle = color; ctx.lineWidth = 4; ctx.stroke(); ctx.restore();
    }
  } else {
    drawSelectedOutline(s, color, 4);
  }
}

function drawSelectedOutline(s, color, width = 5) {
  const pts = shapePoints(s);
  if (!pts.length) return;
  if (s.type === 'segment') drawPolyline(pts.map(w2s), color, width);
  else if (s.type === 'ray') drawRayWorld(pts[0], pts[1], color, width);
  else if (s.type === 'line') drawLineWorld(pts[0], pts[1], color, width);
  else if (s.type === 'perp-bisector') {
    const m = mid(pts[0], pts[1]), n = perp(sub(pts[1], pts[0]));
    drawLineWorld({ x: m.x - n.x, y: m.y - n.y }, { x: m.x + n.x, y: m.y + n.y }, color, width);
  } else if (s.type === 'angle-bisector') {
    const u = norm(sub(pts[1], pts[0])), v = norm(sub(pts[2], pts[0]));
    let d = norm({ x: u.x + v.x, y: u.y + v.y });
    if (Math.hypot(d.x, d.y) < 1e-9) d = perp(u);
    drawRayWorld(pts[0], { x: pts[0].x + d.x, y: pts[0].y + d.y }, color, width, [], 5.2);
  } else if (s.type === 'angle') {
    drawPolyline([pts[1], pts[0]].map(w2s), color, width);
    drawPolyline([pts[1], pts[2]].map(w2s), color, width);
  }
}

function drawShapeSelection(s) {
  if (!s.visible) return;
  if (s.type === 'triangle' || s.type === 'quad') {
    const pts = screenPoly(shapePoints(s));
    if (pts.length >= 3) {
      ctx.save();
      drawPolyline(pts.concat([pts[0]]), 'rgba(245,158,11,.9)', 4.5, 'rgba(245,158,11,.045)');
      ctx.restore();
    }
  } else if (s.type === 'circle') {
    const p = shapePoints(s);
    if (p.length >= 2) {
      const c = w2s(p[0]), r = dist(p[0], p[1]) * scale2d();
      ctx.save(); ctx.beginPath(); ctx.arc(c.x, c.y, r, 0, TAU);
      ctx.strokeStyle = 'rgba(245,158,11,.85)'; ctx.lineWidth = 4.5; ctx.stroke(); ctx.restore();
    }
  } else drawSelectedOutline(s, 'rgba(245,158,11,.85)', 4.5);
}

function drawRelationMark(m) {
  const A = getShape(m.a), B = getShape(m.b);
  if (!A || !B) return;
  const ma = triangleMetrics(A), mb = triangleMetrics(B);
  if (!ma || !mb) return;
  const still = matchTriangles(A, B, m.type);
  if (!still || !still.ok) {
    const ca = w2s(centroidOf(ma.pts)), cb = w2s(centroidOf(mb.pts));
    ctx.save();
    ctx.strokeStyle = 'rgba(156,163,175,.6)'; ctx.lineWidth = 1.2; ctx.setLineDash([3, 5]);
    ctx.beginPath(); ctx.moveTo(ca.x, ca.y); ctx.lineTo(cb.x, cb.y); ctx.stroke();
    ctx.restore();
    chip(m.type === 'congruent' ? '全等关系已改变' : '相似关系已改变', ca.x, ca.y - 17, '#6b7280', 'rgba(249,250,251,.95)', 'center');
    chip(m.type === 'congruent' ? '全等关系已改变' : '相似关系已改变', cb.x, cb.y - 17, '#6b7280', 'rgba(249,250,251,.95)', 'center');
    return;
  }
  const sel = state.selected && state.selected.kind === 'mark' && state.selected.id === m.id;
  const color = m.type === 'congruent' ? '#15803d' : '#b45309';
  const w = sel ? 2.2 : 1.7;
  for (let k = 0; k < 3; k++) {
    drawTicksWorld(ma.pts[k], ma.pts[(k + 1) % 3], k + 1, color, 7, 1);
    drawTicksWorld(mb.pts[m.map[k]], mb.pts[m.map[(k + 1) % 3]], k + 1, color, 7, 1);
    drawAngleArcsWorld(ma.pts[k], ma.pts[(k + 1) % 3], ma.pts[(k + 2) % 3], k + 1, color, 17 + 0);
    drawAngleArcsWorld(mb.pts[m.map[k]], mb.pts[m.map[(k + 1) % 3]], mb.pts[m.map[(k + 2) % 3]], k + 1, color, 17 + 0);
  }
  const ca = w2s(centroidOf(ma.pts)), cb = w2s(centroidOf(mb.pts));
  ctx.save();
  ctx.strokeStyle = hexA(color, .5); ctx.lineWidth = 1.2; ctx.setLineDash([4, 5]);
  ctx.beginPath(); ctx.moveTo(ca.x, ca.y); ctx.lineTo(cb.x, cb.y); ctx.stroke();
  ctx.restore();
  const sym = m.type === 'congruent' ? '≅' : '∽';
  chip(`${sym} ${m.type === 'congruent' ? '全等' : '相似'}${sel ? '' : ''}`, ca.x, ca.y - 17, color, 'rgba(255,253,249,.94)', 'center');
  chip(`${sym} ${m.type === 'congruent' ? '全等' : '相似'}`, cb.x, cb.y - 17, color, 'rgba(255,253,249,.94)', 'center');
}

function hexA(hex, a) {
  if (hex.startsWith('rgba')) return hex;
  const h = hex.replace('#', '');
  const n = parseInt(h.length === 3 ? h.split('').map(c => c + c).join('') : h, 16);
  return `rgba(${(n >> 16) & 255},${(n >> 8) & 255},${n & 255},${a})`;
}

function drawGeoEmpty() {
  ctx.save();
  const cx = W / 2, cy = H / 2;
  ctx.strokeStyle = 'rgba(15,118,110,.14)'; ctx.lineWidth = 1.2; ctx.setLineDash([5, 6]);
  ctx.beginPath(); ctx.arc(cx, cy, 74, 0, TAU); ctx.stroke();
  const pts = [0, 1, 2].map(i => ({ x: cx + Math.cos(-Math.PI / 2 + i * TAU / 3) * 74, y: cy + Math.sin(-Math.PI / 2 + i * TAU / 3) * 74 }));
  ctx.setLineDash([]); ctx.strokeStyle = 'rgba(15,118,110,.22)';
  ctx.beginPath(); ctx.moveTo(pts[0].x, pts[0].y); ctx.lineTo(pts[1].x, pts[1].y); ctx.lineTo(pts[2].x, pts[2].y); ctx.closePath(); ctx.stroke();
  for (const p of pts) { ctx.beginPath(); ctx.arc(p.x, p.y, 4, 0, TAU); ctx.fillStyle = 'rgba(15,118,110,.32)'; ctx.fill(); }
  ctx.fillStyle = 'rgba(91,83,68,.6)'; ctx.font = '13px "PingFang SC","Microsoft YaHei",sans-serif';
  ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  ctx.fillText('从左侧选择一个工具，在画布上点击开始作图', cx, cy + 92);
  ctx.font = '11px "PingFang SC","Microsoft YaHei",sans-serif';
  ctx.fillStyle = 'rgba(139,130,114,.65)';
  ctx.fillText('也可以点「全等示例」或「相似示例」快速查看标记效果', cx, cy + 116);
  ctx.restore();
}

/* ---------- 预览 ---------- */

function drawPendingPreview() {
  const p = state.pending;
  const cur = state.preview;
  if (!p.length && !cur) return;
  ctx.save();
  ctx.setLineDash([5, 5]);
  ctx.strokeStyle = 'rgba(15,118,110,.55)';
  ctx.lineWidth = 1.5;
  if (p.length) {
    for (const ref of p) {
      const sp = w2s(ref);
      ctx.beginPath(); ctx.arc(sp.x, sp.y, 4, 0, TAU);
      ctx.fillStyle = 'rgba(15,118,110,.5)'; ctx.fill();
    }
  }
  if (cur && p.length) {
    const a = p[0];
    if (['segment', 'line', 'ray', 'perp-bisector', 'midpoint'].includes(state.tool)) {
      if (state.tool === 'line') drawLineWorld(a, cur, 'rgba(15,118,110,.42)', 1.4, [5, 5]);
      else if (state.tool === 'ray') drawRayWorld(a, cur, 'rgba(15,118,110,.42)', 1.4, [5, 5]);
      else {
        const pa = w2s(a), pc = w2s(cur);
        ctx.beginPath(); ctx.moveTo(pa.x, pa.y); ctx.lineTo(pc.x, pc.y); ctx.stroke();
        if (state.tool === 'midpoint') {
          const mp = w2s(mid(a, cur));
          ctx.setLineDash([]);
          ctx.beginPath(); ctx.arc(mp.x, mp.y, 4.5, 0, TAU);
          ctx.fillStyle = 'rgba(180,83,9,.6)'; ctx.fill();
          ctx.setLineDash([5, 5]);
        }
      }
      ctx.setLineDash([5, 5]);
      const pc = w2s(cur);
      ctx.beginPath(); ctx.arc(pc.x, pc.y, 4, 0, TAU); ctx.fillStyle = 'rgba(15,118,110,.45)'; ctx.fill();
    } else if (state.tool === 'circle') {
      const pa = w2s(a), pc = w2s(cur), r = dist(a, cur) * scale2d();
      ctx.beginPath(); ctx.arc(pa.x, pa.y, r, 0, TAU); ctx.stroke();
    } else if (state.tool === 'angle-bisector') {
      drawRayWorld(a, cur, 'rgba(180,83,9,.42)', 1.4, [5, 5]);
      if (p.length === 2) {
        const o = p[0], u = norm(sub(p[1], o)), v = norm(sub(cur, o));
        let d = norm({ x: u.x + v.x, y: u.y + v.y });
        if (Math.hypot(d.x, d.y) < 1e-9) d = perp(u);
        drawRayWorld(o, { x: o.x + d.x, y: o.y + d.y }, 'rgba(180,83,9,.65)', 1.7, [5, 5], 5.2);
      }
    } else if (state.tool === 'angle' || state.tool === 'set-alpha') {
      if (p.length === 1) {
        const pa = w2s(a), pc = w2s(cur);
        ctx.beginPath(); ctx.moveTo(pa.x, pa.y); ctx.lineTo(pc.x, pc.y); ctx.stroke();
      } else if (p.length === 2) {
        const A = p[0], O = p[1], B = cur;
        drawPolyline([O, A].map(w2s), 'rgba(180,83,9,.55)', 1.5);
        drawPolyline([O, B].map(w2s), 'rgba(180,83,9,.55)', 1.5);
        if (Math.abs(cross(sub(A, O), sub(B, O))) > 1e-4) {
          drawAngleArcsWorld(O, A, B, 1, 'rgba(180,83,9,.55)', 22);
        }
      }
    } else if (state.tool === 'triangle') {
      if (p.length === 1) {
        const pa = w2s(a), pc = w2s(cur);
        ctx.beginPath(); ctx.moveTo(pa.x, pa.y); ctx.lineTo(pc.x, pc.y); ctx.stroke();
      } else if (p.length === 2) {
        const poly = [p[0], p[1], cur].map(w2s);
        drawPolyline(poly.concat([poly[0]]), 'rgba(15,118,110,.55)', 1.5, 'rgba(15,118,110,.04)', [5, 5]);
      }
    } else if (['right-triangle', 'isosceles-triangle', 'right-isosceles', 'equilateral'].includes(state.tool)) {
      const base = horizontalTriangleBase([p[0], cur]);
      const tri = autoTrianglePoints(base[0], base[1], state.tool);
      if (tri) {
        const poly = tri.map(w2s);
        drawPolyline(poly.concat([poly[0]]), 'rgba(15,118,110,.55)', 1.5, 'rgba(15,118,110,.04)', [5, 5]);
      }
    } else if (['square', 'rectangle', 'parallelogram', 'rhombus'].includes(state.tool)) {
      const quad = autoQuadPoints(p[0], cur, state.tool);
      if (quad) {
        const poly = quad.map(w2s);
        drawPolyline(poly.concat([poly[0]]), 'rgba(37,99,235,.5)', 1.5, 'rgba(37,99,235,.035)', [5, 5]);
      }
    }
  }
  ctx.restore();
}

/* ---------- 自动图形计算 ---------- */

function horizontalTriangleBase(refs) {
  if (!state.geom.horizontalBase || refs.length < 2) return refs.slice(0, 2);
  const y = refs[0].y;
  const x1 = Math.min(refs[0].x, refs[1].x);
  const x2 = Math.max(refs[0].x, refs[1].x);
  const keep = (ref, x) => ({ x, y, pid: Math.abs(ref.x - x) < 1e-9 && Math.abs(ref.y - y) < 1e-9 ? ref.pid : null });
  return [keep(refs[0], x1), keep(refs[1], x2)];
}

function resolveAutoBasePoint(ref, desired) {
  if (ref.pid) {
    const p = getPt(ref.pid);
    if (p && Math.abs(p.x - desired.x) < 1e-9 && Math.abs(p.y - desired.y) < 1e-9) return p;
  }
  return makePoint(desired.x, desired.y);
}

function upwardNormal(v) {
  let n = norm(perp(v));
  if (n.y < 0) n = mul(n, -1);
  return n;
}
function autoTrianglePoints(A, B, kind) {
  const v = sub(B, A), len = Math.hypot(v.x, v.y);
  if (len < 1e-6) return null;
  const n = upwardNormal(v);
  const m = mid(A, B);
  if (kind === 'right-triangle') return [A, B, { x: A.x + n.x * len * .72, y: A.y + n.y * len * .72 }];
  if (kind === 'isosceles-triangle') return [A, B, { x: m.x + n.x * len * .92, y: m.y + n.y * len * .92 }];
  if (kind === 'right-isosceles') return [A, B, { x: A.x + n.x * len, y: A.y + n.y * len }];
  if (kind === 'equilateral') return [A, B, { x: m.x + n.x * len * Math.sqrt(3) / 2, y: m.y + n.y * len * Math.sqrt(3) / 2 }];
  return null;
}
function autoQuadPoints(A, B, kind) {
  const v = sub(B, A), len = Math.hypot(v.x, v.y);
  if (len < 1e-6) return null;
  const n = upwardNormal(v);
  let C, D;
  if (kind === 'square') { C = add(B, mul(n, len)); D = add(A, mul(n, len)); }
  else if (kind === 'rectangle') { C = add(B, mul(n, len * .62)); D = add(A, mul(n, len * .62)); }
  else if (kind === 'parallelogram') {
    let shift = mul(rotate(v, 42 * DEG), .64);
    if (shift.y < 0) shift = mul(rotate(v, -42 * DEG), .64);
    C = add(B, shift); D = add(A, shift);
  } else if (kind === 'rhombus') {
    let shift = rotate(v, 58 * DEG);
    if (shift.y < 0) shift = rotate(v, -58 * DEG);
    C = add(B, shift); D = add(A, shift);
  } else return null;
  return [A, B, C, D];
}

/* ---------- 图形创建 ---------- */

function addShape(type, pts, kind) {
  const shape = { id: uid('s'), type, kind: kind || '', points: pts.map(p => p.id), color: '', visible: true };
  shape.color = shapeColor(shape);
  state.geom.shapes.push(shape);
  return shape;
}
function createTriangle(kind, A, B, C) {
  const pts = [A, B, C];
  const s = addShape('triangle', pts, kind);
  state.selected = { kind: 'shape', id: s.id };
  return s;
}
function createQuad(kind, A, B, C, D) {
  const s = addShape('quad', [A, B, C, D], kind);
  state.selected = { kind: 'shape', id: s.id };
  return s;
}

/* ---------- 全等 / 相似匹配 ---------- */

const TRANSFORM_COLORS = { rotate: '#2563eb', reflect: '#be123c' };

function createMidpoint(a, b, segmentId = null) {
  if (!a || !b) return null;
  if (dist(a, b) < 1e-6) { toast('两点重合，无法确定中点', 'warn'); return null; }
  const existing = state.geom.points.find(p => p.derived && p.derived.type === 'midpoint'
    && ((p.derived.a === a.id && p.derived.b === b.id) || (p.derived.a === b.id && p.derived.b === a.id)));
  if (existing) {
    state.selected = { kind: 'point', id: existing.id };
    toast(`中点 ${existing.label} 已经存在`, 'warn');
    return existing;
  }
  const p = makePoint((a.x + b.x) / 2, (a.y + b.y) / 2);
  p.derived = { type: 'midpoint', a: a.id, b: b.id, segmentId };
  p.color = '#b45309';
  state.selected = { kind: 'point', id: p.id };
  toast(`已作出 ${a.label}${b.label} 的中点 ${p.label}`, 'ok');
  return p;
}

function evalAngleExpression(expr) {
  const alpha = getAlphaValue();
  let s = String(expr == null ? '' : expr).trim();
  if (!s) throw new Error('请输入旋转角表达式');
  s = s.replace(/[°º]/g, '').replace(/[−–—]/g, '-').replace(/×/g, '*').replace(/÷/g, '/')
    .replace(/度/g, '').replace(/阿尔法/g, 'a').replace(/α|Α/g, 'a').replace(/\balpha\b/gi, 'a')
    .replace(/乘以|乘/g, '*').replace(/除以|除/g, '/').replace(/加/g, '+').replace(/减/g, '-');
  const needsAlpha = /[aA]/.test(s);
  if (needsAlpha && alpha === null) throw new Error('请先用「取角 α」把一个已有角设为 α');
  if (!/^[0-9aA+\-*/().\s]+$/.test(s)) throw new Error('旋转角只能包含数字、α、+ − × ÷ 和括号');
  s = s.replace(/[aA]/g, `(${alpha === null ? 0 : alpha})`);
  let ast;
  try { ast = parseExpression(s); }
  catch (err) { throw new Error('旋转角表达式有误：' + err.message); }
  const value = evalNode(ast, 0);
  if (!Number.isFinite(value)) throw new Error('旋转角表达式没有有效结果');
  return value;
}

function normalizeAngleDeg(v) {
  let a = ((v % 360) + 360) % 360;
  if (a > 180) a -= 360;
  return a;
}

function rotateCoords(p, c, angleDeg) {
  const t = angleDeg * DEG, dx = p.x - c.x, dy = p.y - c.y;
  return {
    x: c.x + dx * Math.cos(t) - dy * Math.sin(t),
    y: c.y + dx * Math.sin(t) + dy * Math.cos(t)
  };
}

function reflectCoords(p, a, b) {
  const v = sub(b, a);
  const len2 = dot(v, v);
  if (len2 < 1e-12) return { x: p.x, y: p.y };
  const t = dot(sub(p, a), v) / len2;
  const foot = { x: a.x + v.x * t, y: a.y + v.y * t };
  return { x: 2 * foot.x - p.x, y: 2 * foot.y - p.y };
}

function transformCoords(p, spec) {
  if (!spec) return { x: p.x, y: p.y };
  if (spec.type === 'rotate') return rotateCoords(p, spec.center, spec.angle);
  if (spec.type === 'reflect') return reflectCoords(p, spec.a, spec.b);
  return { x: p.x, y: p.y };
}

function completeAlphaAngle(refs) {
  if (!refs || refs.length < 3) return;
  const [A, O, B] = refs;
  if (refsClose(A, O) || refsClose(O, B) || refsClose(A, B)) {
    toast('三个点不能重合', 'warn');
    return;
  }
  if (Math.abs(cross(sub(A, O), sub(B, O))) < 1e-4) {
    toast('三点共线，无法确定一个角', 'warn');
    return;
  }
  pushHistory();
  const pa = resolveRef(A), po = resolveRef(O), pb = resolveRef(B);
  let shape = state.geom.shapes.find(s => s.type === 'angle'
    && s.points[0] === pa.id && s.points[1] === po.id && s.points[2] === pb.id);
  if (!shape) shape = addShape('angle', [pa, po, pb], 'angle');
  state.geom.alpha = { shapeId: shape.id, vertexIndex: 1 };
  state.selected = { kind: 'shape', id: shape.id };
  state.pending = []; state.preview = null;
  updateTransformUI();
  renderAllPanels(); draw(); saveSoon();
  const info = getAlphaInfo();
  toast(info ? `已取 ${info.label} = ${fmt(info.value, 2)}° 作为 α` : '已设置 α', 'ok');
}

function axisLineForShape(s) {
  if (!s) return null;
  const p = shapePoints(s);
  if (p.length < 2) return null;
  if (s.type === 'segment' || s.type === 'ray' || s.type === 'line') return [p[0], p[1]];
  if (s.type === 'perp-bisector') {
    const m = mid(p[0], p[1]), n = perp(sub(p[1], p[0]));
    return [{ x: m.x - n.x, y: m.y - n.y }, { x: m.x + n.x, y: m.y + n.y }];
  }
  if (s.type === 'angle-bisector') {
    const o = p[0], u = norm(sub(p[1], o)), v = norm(sub(p[2], o));
    let d = norm({ x: u.x + v.x, y: u.y + v.y });
    if (Math.hypot(d.x, d.y) < 1e-9) d = perp(u);
    return [o, { x: o.x + d.x, y: o.y + d.y }];
  }
  return null;
}

function axisAtClick(sp) {
  const s = lineShapeAt(sp);
  if (s && axisLineForShape(s)) return s;
  return null;
}

function applyTransformToTarget(spec) {
  const target = state.transformTarget;
  if (!target) { toast('请先选择要变换的图形或点', 'warn'); return; }
  const targetPoint = target.kind === 'point' ? getPt(target.id) : null;
  const targetShape = target.kind === 'shape' ? getShape(target.id) : null;
  if (!targetPoint && !targetShape) { toast('所选对象已不存在', 'warn'); return; }

  const src = targetPoint ? [targetPoint] : shapePoints(targetShape);
  if (!src.length) { toast('所选对象没有可变换的顶点', 'warn'); return; }
  const unique = [];
  const seen = new Set();
  for (const p of src) { if (!seen.has(p.id)) { seen.add(p.id); unique.push(p); } }
  const mapped = new Map(unique.map(p => [p.id, transformCoords(p, spec)]));
  const color = TRANSFORM_COLORS[spec.type] || '#2563eb';

  pushHistory();
  let imageKind = null, imageId = null;
  if (state.keepOriginal) {
    const newByOld = new Map();
    if (targetPoint) {
      const q = mapped.get(targetPoint.id);
      const np = makePoint(q.x, q.y, primeLabel(targetPoint.label));
      np.color = color;
      np.imageOf = targetPoint.id;
      imageKind = 'point'; imageId = np.id;
      state.selected = { kind: 'point', id: np.id };
    } else {
      for (const p of unique) {
        const q = mapped.get(p.id);
        const np = makePoint(q.x, q.y, primeLabel(p.label));
        np.color = color;
        np.imageOf = p.id;
        newByOld.set(p.id, np);
      }
      const img = addShape(targetShape.type, targetShape.points.map(id => newByOld.get(id)).filter(Boolean), targetShape.kind);
      img.color = color;
      img.imageOf = targetShape.id;
      imageKind = 'shape'; imageId = img.id;
      state.selected = { kind: 'shape', id: img.id };
    }
    state.geom.transforms = state.geom.transforms || [];
    state.geom.transforms.push({
      id: uid('t'), type: spec.type, sourceKind: target.kind, sourceId: target.id,
      imageKind, imageId, angle: spec.angle, color
    });
  } else {
    for (const p of unique) {
      const q = mapped.get(p.id);
      p.x = q.x; p.y = q.y;
    }
    state.selected = { kind: target.kind, id: target.id };
  }

  state.transformTarget = null;
  updateTransformUI();
  updateHint();
  renderAllPanels(); draw(); saveSoon();
  const angleText = spec.type === 'rotate' ? ` ${fmt(normalizeAngleDeg(spec.angle), 2)}°` : '';
  toast(state.keepOriginal
    ? `已生成${spec.type === 'rotate' ? '旋转' : '轴对称'}像${angleText}`
    : `已直接${spec.type === 'rotate' ? '旋转' : '轴对称'}原图${angleText}`, 'ok');
}

function updateTransformUI() {
  const readout = $('#alphaReadout');
  const preview = $('#rotatePreview');
  const input = $('#rotateExpr');
  if (!readout || !preview || !input) return;
  if (input.value !== state.rotateExpr && document.activeElement !== input) input.value = state.rotateExpr;
  const info = getAlphaInfo();
  if (info) {
    const alphaKind = info.shape.type === 'triangle' ? '三角形内角' : info.shape.type === 'quad' ? '四边形内角' : '三点角';
    readout.innerHTML = `<b>α = ${fmt(info.value, 2)}°</b><span>${esc(info.label)} · ${esc(alphaKind)}</span>`;
  } else {
    readout.innerHTML = '<span>未设置 · 用「取角 α」依次点边上一点、顶点、边上一点</span>';
  }
  try {
    const angle = evalAngleExpression(state.rotateExpr);
    const norm = normalizeAngleDeg(angle);
    preview.innerHTML = `<b>旋转角 = ${fmt(angle, 2)}°</b>${Math.abs(angle) > 360 ? `（等价 ${fmt(norm, 2)}°）` : ''}<span>${esc(state.rotateExpr)}</span>`;
    preview.classList.remove('bad');
  } catch (err) {
    preview.innerHTML = `<span>${esc(err.message)}</span>`;
    preview.classList.add('bad');
  }
  const keep = $('#keepOriginal');
  if (keep) keep.checked = !!state.keepOriginal;
  $$('.angle-chip').forEach(b => b.classList.toggle('active', b.dataset.angle === state.rotateExpr));
}

const PERMS = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];

function matchTriangles(A, B, mode) {
  const ma = triangleMetrics(A), mb = triangleMetrics(B);
  if (!ma || !mb) return null;
  let best = null;
  for (const perm of PERMS) {
    let score = 0, maxRel = 0, maxAng = 0;
    const ratios = [];
    for (let k = 0; k < 3; k++) {
      const sa = ma.sides[k], sb = mb.sides[perm[k]];
      const denom = Math.max(sa, sb, 1e-9);
      const rel = Math.abs(sa - sb) / denom;
      maxRel = Math.max(maxRel, rel);
      ratios.push(sb / Math.max(1e-9, sa));
      const angDiff = Math.abs(ma.angles[k] - mb.angles[perm[k]]);
      maxAng = Math.max(maxAng, angDiff);
      score += mode === 'congruent' ? rel : angDiff;
    }
    if (!best || score < best.score) best = { perm, score, maxRel, maxAng, ratios };
  }
  const tolerance = mode === 'congruent' ? 0.02 : 0.035;
  const ok = mode === 'congruent'
    ? best.maxRel <= tolerance
    : best.maxAng <= 2.2 && (Math.max(...best.ratios) - Math.min(...best.ratios)) / Math.max(...best.ratios) <= 0.04;
  return { ...best, ok, ma, mb };
}

function addRelationMark(mode, A, B) {
  const r = matchTriangles(A, B, mode);
  if (!r) return false;
  const name = mode === 'congruent' ? '全等' : '相似';
  if (!r.ok) {
    const why = mode === 'congruent'
      ? `三组对应边不完全相等（最大相对误差 ${fmt(r.maxRel * 100, 1)}%），未添加全等标记。`
      : `对应角不完全相等（最大角差 ${fmt(r.maxAng, 1)}°），未添加相似标记。`;
    toast(why, 'warn');
    return false;
  }
  const exists = state.geom.marks.find(m => m.type === mode && ((m.a === A.id && m.b === B.id) || (m.a === B.id && m.b === A.id)));
  if (exists) {
    state.selected = { kind: 'mark', id: exists.id };
    toast(`这两个三角形已经有${name}标记`, 'warn');
    return true;
  }
  const m = {
    id: uid('m'), type: mode, a: A.id, b: B.id, map: r.perm,
    color: mode === 'congruent' ? '#15803d' : '#b45309', visible: true
  };
  state.geom.marks.push(m);
  state.selected = { kind: 'mark', id: m.id };
  const ratio = r.ma.perimeter ? r.mb.perimeter / r.ma.perimeter : 1;
  toast(mode === 'congruent' ? '已标记全等：三组对应边、三组对应角已用相同记号标出。' : `已标记相似：对应角相等，相似比约为 ${fmt(ratio, 3)}。`, 'ok');
  return true;
}

/* ---------- 命中测试 ---------- */

function hitTestPoint(sp, tol = 11) {
  syncDerivedPoints();
  let best = null, bd = tol;
  for (const p of state.geom.points) {
    if (!p.visible) continue;
    const q = w2s(p), d = Math.hypot(q.x - sp.x, q.y - sp.y);
    if (d < bd) { bd = d; best = p; }
  }
  return best;
}

function lineShapeAt(sp) {
  const shapes = state.geom.shapes;
  for (let i = shapes.length - 1; i >= 0; i--) {
    const s = shapes[i];
    if (!s.visible) continue;
    const pts = shapePoints(s);
    if (s.type === 'segment' && pts.length >= 2) {
      if (distToSegment(sp, w2s(pts[0]), w2s(pts[1])) < 9) return s;
    } else if (s.type === 'ray' && pts.length >= 2) {
      if (distToRay(sp, w2s(pts[0]), w2s(pts[1])) < 9) return s;
    } else if (s.type === 'line' && pts.length >= 2) {
      if (distToLine(sp, w2s(pts[0]), w2s(pts[1])) < 9) return s;
    } else if (s.type === 'perp-bisector' && pts.length >= 2) {
      const m = mid(pts[0], pts[1]), n = perp(sub(pts[1], pts[0]));
      if (distToLine(sp, w2s({ x: m.x - n.x, y: m.y - n.y }), w2s({ x: m.x + n.x, y: m.y + n.y })) < 9) return s;
    } else if (s.type === 'angle-bisector' && pts.length >= 3) {
      const o = pts[0], u = norm(sub(pts[1], o)), v = norm(sub(pts[2], o));
      let d = norm({ x: u.x + v.x, y: u.y + v.y });
      if (Math.hypot(d.x, d.y) < 1e-9) d = perp(u);
      if (distToRay(sp, w2s(o), w2s({ x: o.x + d.x, y: o.y + d.y })) < 9) return s;
    }
  }
  return null;
}

function hitTestShape(sp) {
  const shapes = state.geom.shapes;
  for (let i = shapes.length - 1; i >= 0; i--) {
    const s = shapes[i];
    if (!s.visible) continue;
    const pts = shapePoints(s);
    if (s.type === 'triangle' || s.type === 'quad') {
      if (pointInPoly(s2w(sp), pts)) return s;
    } else if (s.type === 'circle') {
      if (pts.length >= 2) {
        const c = w2s(pts[0]), r = dist(pts[0], pts[1]) * scale2d();
        if (Math.abs(Math.hypot(sp.x - c.x, sp.y - c.y) - r) < 9) return s;
      }
    } else if (s.type === 'segment' && pts.length >= 2) {
      if (distToSegment(sp, w2s(pts[0]), w2s(pts[1])) < 8) return s;
    } else if (s.type === 'ray' && pts.length >= 2) {
      if (distToRay(sp, w2s(pts[0]), w2s(pts[1])) < 8) return s;
    } else if (s.type === 'line' && pts.length >= 2) {
      if (distToLine(sp, w2s(pts[0]), w2s(pts[1])) < 8) return s;
    } else if (s.type === 'perp-bisector' && pts.length >= 2) {
      const m = mid(pts[0], pts[1]), n = perp(sub(pts[1], pts[0]));
      if (distToLine(sp, w2s({ x: m.x - n.x, y: m.y - n.y }), w2s({ x: m.x + n.x, y: m.y + n.y })) < 9) return s;
    } else if (s.type === 'angle' && pts.length >= 3) {
      const o = w2s(pts[1]);
      if (distToSegment(sp, w2s(pts[0]), o) < 8 || distToSegment(sp, w2s(pts[2]), o) < 8) return s;
    } else if (s.type === 'angle-bisector' && pts.length >= 3) {
      const o = pts[0], u = norm(sub(pts[1], o)), v = norm(sub(pts[2], o));
      let d = norm({ x: u.x + v.x, y: u.y + v.y });
      if (Math.hypot(d.x, d.y) < 1e-9) d = perp(u);
      if (distToRay(sp, w2s(o), w2s({ x: o.x + d.x, y: o.y + d.y })) < 9) return s;
    }
  }
  return null;
}
function distToRay(p, o, a) {
  const v = sub(a, o), w = sub(p, o);
  const t = dot(w, v) / Math.max(1e-9, dot(v, v));
  if (t < 0) return dist(p, o);
  return dist(p, { x: o.x + v.x * t, y: o.y + v.y * t });
}

function triangleAt(sp) {
  const world = s2w(sp);
  const tris = state.geom.shapes.filter(s => s.visible && s.type === 'triangle');
  for (let i = tris.length - 1; i >= 0; i--) {
    if (pointInPoly(world, shapePoints(tris[i]))) return tris[i];
  }
  return null;
}

/* ============================================================
   界面渲染
   ============================================================ */

const TAB_NAMES = { function: '函数', conic: '圆锥曲线', geometry: '几何作图' };
const MODE_NAMES = { plane: '平面直角坐标系', space: '空间直角坐标系', blank: '空白平面' };
const TOOL_NAMES = {
  select: '选择 / 拖动', point: '点', segment: '线段', ray: '射线', line: '直线',
  triangle: '一般三角形', 'right-triangle': '直角三角形', 'isosceles-triangle': '等腰三角形',
  'right-isosceles': '等腰直角三角形', equilateral: '等边三角形', square: '正方形',
  rectangle: '矩形', parallelogram: '平行四边形', rhombus: '菱形', circle: '圆',
  'perp-bisector': '垂直平分线', 'angle-bisector': '角平分线', angle: '三点定角', midpoint: '线段中点',
  rotate: '旋转变换', reflect: '轴对称', 'set-alpha': '取角 α（三点）',
  congruent: '全等标记', similar: '相似标记'
};

function setMode(mode) {
  state.mode = mode;
  state.pending = []; state.preview = null; state.markFirst = null; state.transformTarget = null; state.hover = null;
  $$('.mode-btn').forEach(b => {
    const on = b.dataset.mode === mode;
    b.classList.toggle('active', on);
    b.setAttribute('aria-selected', on ? 'true' : 'false');
  });
  const space = mode === 'space';
  $('#mainTabs').hidden = space;
  $('#tabBody').hidden = space;
  $('#spacePanel').hidden = !space;
  $('#analysisSection').hidden = space || state.tab === 'geometry';
  $('#selectionSection').hidden = space || state.tab !== 'geometry';
  const badge = $('#canvasBadge');
  badge.classList.toggle('space', space);
  badge.classList.toggle('blank', mode === 'blank');
  badge.querySelector('b').textContent = MODE_NAMES[mode];
  $('#canvasModeText').textContent = space ? '旋转观察 · 空间点投影'
    : state.tab === 'function' ? '函数图像'
    : state.tab === 'conic' ? '圆锥曲线'
    : '几何作图';
  $('#panelTag').textContent = space ? '空间' : state.tab === 'function' ? '代数' : state.tab === 'conic' ? '曲线' : '作图';
  $('#rightTag').textContent = space ? '空间' : state.tab === 'function' ? '函数' : state.tab === 'conic' ? '圆锥曲线' : '几何';
  updateModeStatus();
  updateHint();
  renderObjectList();
  renderAnalysis();
  renderSelection();
  updateTransformUI();
  updateToolbarVisibility();
  updateZoomLabel();
  draw();
  saveSoon();
}

function updateModeStatus() {
  const el = $('#modeStatus');
  if (!el) return;
  const mode = state.mode === 'space' ? '空间' : state.mode === 'blank' ? '空白' : '平面';
  const tab = state.mode === 'space' ? '坐标' : TAB_NAMES[state.tab];
  el.textContent = `${mode} · ${tab}模式`;
}

function setTab(tab) {
  if (state.mode === 'space') return;
  state.tab = tab;
  state.pending = []; state.preview = null; state.markFirst = null; state.transformTarget = null;
  $$('.tab').forEach(b => b.classList.toggle('active', b.dataset.tab === tab));
  $$('.tab-pane').forEach(p => p.classList.toggle('active', p.dataset.pane === tab));
  $('#analysisSection').hidden = tab === 'geometry';
  $('#selectionSection').hidden = tab !== 'geometry';
  $('#panelTag').textContent = tab === 'function' ? '代数' : tab === 'conic' ? '曲线' : '作图';
  $('#rightTag').textContent = tab === 'function' ? '函数' : tab === 'conic' ? '圆锥曲线' : '几何';
  $('#canvasModeText').textContent = tab === 'function' ? '函数图像' : tab === 'conic' ? '圆锥曲线' : '几何作图';
  state.analysisMode = tab === 'conic' ? 'conic' : 'function';
  if (tab !== 'conic') state.tangentPicking = false;
  updateModeStatus();
  updateHint();
  updateTangentUI();
  renderObjectList();
  renderAnalysis();
  renderSelection();
  updateTransformUI();
  updateToolbarVisibility();
  draw();
  saveSoon();
}

function updateToolbarVisibility() {
  const geom = state.mode !== 'space' && state.tab === 'geometry';
  const undoBtn = $('#undoBtn'), redoBtn = $('#redoBtn'), delBtn = $('#deleteBtn');
  if (undoBtn) undoBtn.hidden = false;
  if (redoBtn) redoBtn.hidden = false;
  if (delBtn) delBtn.hidden = !geom;
  updateHistoryButtons();
  if (delBtn) delBtn.disabled = !geom || !state.selected;
}

function setTool(tool) {
  state.tool = tool;
  state.pending = []; state.preview = null; state.markFirst = null; state.transformTarget = null;
  $$('.tool').forEach(b => b.classList.toggle('active', b.dataset.tool === tool));
  updateHint();
  updateTransformUI();
  draw();
}

function updateHint() {
  const foot = $('#footHint');
  const hint = $('#hintCard');
  if (!foot || !hint) return;
  if (state.mode === 'space') {
    foot.innerHTML = '<b>提示：</b>拖动旋转 · 滚轮缩放 · 点击「原点」复位';
    hint.innerHTML = '空间直角坐标系按 x / y / z 三轴绘制。左侧输入坐标添加空间点，拖动空白处旋转观察方向。';
    return;
  }
  if (state.tab === 'function') {
    foot.innerHTML = '<b>提示：</b>拖动平移 · 滚轮缩放 · Enter 绘制';
    hint.innerHTML = '<b>函数研究：</b>输入表达式并绘制；选中某条曲线后用左侧「求导」看切线，用「定积分」显示积分区域。画布支持多条函数叠加。';
    return;
  }
  if (state.tab === 'conic') {
    foot.innerHTML = '<b>提示：</b>设置参数 → 生成曲线 · 滚轮缩放';
    hint.innerHTML = '<b>圆锥曲线：</b>圆、椭圆、抛物线与双曲线共用中心参数；生成后右侧会列出焦点、离心率、准线或渐近线。';
    return;
  }
  if (state.tool === 'rotate' || state.tool === 'reflect') {
    const first = state.tool === 'rotate' ? '旋转' : '轴对称';
    const second = state.tool === 'rotate' ? '一个点作为旋转中心' : '一条直线 / 线段 / 射线作为对称轴';
    if (!state.transformTarget) {
      foot.innerHTML = `<b>提示：</b>${first}：先点击要变换的点或图形`;
      hint.innerHTML = `<b>${first}：</b>先点击要变换的点或图形，再点击${second}。${state.keepOriginal ? '默认保留原图并生成带撇号的像。' : '当前设置为直接变换原图。'}`;
    } else {
      foot.innerHTML = `<b>提示：</b>已选对象 · 点击${second}`;
      hint.innerHTML = `<b>${first}：</b>已选好要变换的对象，现在点击${second}。<br>旋转角：<b>${esc(state.rotateExpr)}</b>${state.tool === 'rotate' ? '（角度按逆时针为正）' : ''}`;
    }
    return;
  }
  if (state.tool === 'set-alpha') {
    foot.innerHTML = '<b>提示：</b>取角 α：依次点击边上一点、顶点、边上一点';
    hint.innerHTML = '<b>取角 α（三点法）：</b>这是唯一的取角方式。依次点击边上一点、顶点、边上一点，第三个点后会直接建立并引用这个角。之后移动三点，α 会实时更新。';
    return;
  }
  const map = {
    select: ['拖动顶点或整个图形；空白处拖动平移。', '点击选中对象；拖动顶点改变形状。按住 Alt 可临时关闭网格吸附。'],
    point: ['点击放置一个点；靠近已有顶点会自动吸附。', '点会被后续线段、三角形等复用，便于构造共享顶点。'],
    segment: ['依次点击两个端点，创建线段。', '依次点击两个点。靠近已有顶点时会复用该点。'],
    ray: ['先点击端点，再点击射线方向上的点。', '射线从第一个点出发，穿过第二个点无限延伸。'],
    line: ['点击两个点，创建一条无限延伸的直线。', '直线经过两个点，向两端无限延伸。'],
    triangle: ['依次点击三个顶点，创建一般三角形。', '点击三个不共线的点；系统自动标注顶点字母。'],
    'right-triangle': ['点击两个点作为一条直角边，自动补出直角顶点。', '第二个点确定直角边；拖动顶点后，直角记号会按实际角度更新。'],
    'isosceles-triangle': ['点击底边两个端点，自动补出等腰顶点。', '自动生成的顶点位于底边中垂线上；也可拖动调整。'],
    'right-isosceles': ['点击一条直角边的两个端点，自动补出等腰直角顶点。', '第一个点是直角顶点，两个直角边等长。'],
    equilateral: ['点击底边两个端点，自动补出等边三角形。', '自动按 √3/2 的底边高度生成顶点。'],
    square: ['点击一条边的两个端点，自动补出正方形。', '以所点线段为边，向上生成正方形。'],
    rectangle: ['点击一条边的两个端点，自动补出矩形。', '以所点线段为长，向上生成矩形。'],
    parallelogram: ['点击一条边的两个端点，自动补出平行四边形。', '以所点线段为边，斜边自动生成。'],
    rhombus: ['点击一条边的两个端点，自动补出菱形。', '四条边等长；拖动顶点后等边记号会更新。'],
    circle: ['先点击圆心，再点击圆周上一点。', '半径等于两次点击的距离；可拖动圆上的点改变半径。'],
    'perp-bisector': ['依次点击线段的两个端点，生成垂直平分线。', '平分线经过中点且与线段垂直，并标出直角与等分记号。'],
    'angle-bisector': ['依次点击顶点、第一条边上一点、第二条边上一点。', '角平分线会标出两侧相等的角弧。'],
    angle: ['依次点击边上一点、顶点、边上一点，确定一个角。', '建立后会显示角度；选中后可以把该角设为 α，用于含参旋转。'],
    midpoint: ['点击一条线段直接作中点；也可以依次点击两个点。', '中点是派生点，会随线段端点移动，并用等分刻线标出。'],
    rotate: ['先点击要旋转的点 / 图形，再点击一个点作为旋转中心。', '旋转角支持 α 表达式。默认生成带撇号的旋转像，原图保留。'],
    reflect: ['先点击要变换的点 / 图形，再点击一条直线作为对称轴。', '支持直线、线段、射线、垂直平分线或角平分线作为对称轴。'],
    'set-alpha': ['依次点击边上一点、顶点、边上一点，第三个点后直接设为 α。', '这是唯一的取角方式。α 会随三点位置实时更新，可用于 180°−2α、90°−α 等旋转角。'],
    congruent: ['依次点击两个三角形，检查并标记全等。', '系统自动寻找顶点对应关系；三组对应边相等时添加相同刻度与角弧。'],
    similar: ['依次点击两个三角形，检查并标记相似。', '系统自动寻找顶点对应关系；对应角相等时添加相同角弧并显示相似比。']
  };
  const m = map[state.tool] || map.select;
  foot.innerHTML = `<b>提示：</b>${m[0]}`;
  hint.innerHTML = `<b>${TOOL_NAMES[state.tool] || '选择'}：</b>${m[1]}`;
  if (state.geom.horizontalBase && ['right-triangle', 'isosceles-triangle', 'right-isosceles', 'equilateral'].includes(state.tool)) {
    hint.innerHTML += '<br><span style="color:#0f766e">底边水平已开启：第二次点击只决定长度，底边高度沿用第一次点击的位置。</span>';
  }
}

function syncSnapToggles() {
  const snap = $('#snapToggle'), labels = $('#labelToggle'), hb = $('#horizontalBase');
  if (snap) snap.checked = !!state.geom.snap;
  if (labels) labels.checked = !!state.geom.showLabels;
  if (hb) hb.checked = state.geom.horizontalBase !== false;
}

function renderObjectList() {
  const box = $('#objectList');
  const meta = $('#objMeta');
  if (!box) return;
  let items = [];
  if (state.mode === 'space') {
    items = state.space.points.map(p => ({
      kind: 'space', id: p.id, color: '#0f766e', visible: p.visible !== false,
      name: `${p.label}  (${fmt(p.x, 2)}, ${fmt(p.y, 2)}, ${fmt(p.z, 2)})`, sub: '空间点'
    }));
  } else if (state.tab === 'function') {
    items = state.functions.map((f, i) => ({
      kind: 'fn', id: f.id, color: f.color, visible: f.visible,
      name: `f${subscript(i + 1)}(x) = ${f.expr}`, sub: f.id === state.activeFnId ? '当前函数' : '函数'
    }));
  } else if (state.tab === 'conic') {
    if (state.curve) items.push({
      kind: 'curve', id: 'curve', color: '#7c3aed', visible: state.curve.visible !== false,
      name: state.curve.equation, sub: state.curve.kind === 'circle' ? '圆' : state.curve.kind === 'ellipse' ? '椭圆' : state.curve.kind === 'parabola' ? '抛物线' : '双曲线'
    });
  } else {
    for (const s of state.geom.shapes) {
      items.push({ kind: 'shape', id: s.id, color: shapeColor(s), visible: s.visible, name: shapeLabel(s), sub: s.type === 'angle' ? '角' : s.imageOf ? '变换像' : '图形' });
    }
    for (const m of state.geom.marks) {
      const A = getShape(m.a), B = getShape(m.b);
      items.push({ kind: 'mark', id: m.id, color: m.color, visible: m.visible, name: `${m.type === 'congruent' ? '≅ 全等' : '∽ 相似'}：${A ? shapeLabel(A).split(' ').slice(-1)[0] : ''} / ${B ? shapeLabel(B).split(' ').slice(-1)[0] : ''}`, sub: '关系标记' });
    }
    for (const p of state.geom.points) {
      const sub = p.derived && p.derived.type === 'midpoint'
        ? `中点 · ${(getPt(p.derived.a) || {}).label || '?'}${(getPt(p.derived.b) || {}).label || '?'}`
        : p.imageOf ? `像点 · (${fmt(p.x, 2)}, ${fmt(p.y, 2)})` : `(${fmt(p.x, 2)}, ${fmt(p.y, 2)})`;
      items.push({ kind: 'point', id: p.id, color: p.color || GEO_COLORS.point, visible: p.visible, name: p.label, sub });
    }
  }
  if (meta) meta.textContent = String(items.length);
  if (!items.length) {
    box.innerHTML = '<div class="empty-list">当前画布还没有对象</div>';
    return;
  }
  box.innerHTML = items.map(it => {
    const sel = state.selected && state.selected.kind === it.kind && state.selected.id === it.id;
    const active = it.kind === 'fn' && it.id === state.activeFnId;
    return `<div class="obj-item ${sel || active ? 'selected' : ''} ${it.visible === false ? 'hidden' : ''}" data-kind="${it.kind}" data-id="${esc(it.id)}">
      <span class="obj-swatch" style="background:${it.color}"></span>
      <span class="obj-name" title="${esc(it.name)}">${esc(it.name)}<br><small>${esc(it.sub || '')}</small></span>
      <span class="obj-actions">
        <button class="icon-btn" data-act="vis" title="显示 / 隐藏">${eyeIcon()}</button>
        <button class="icon-btn del" data-act="del" title="删除">${trashIcon()}</button>
      </span>
    </div>`;
  }).join('');
}

function eyeIcon() { return '<svg viewBox="0 0 24 24"><path d="M2 12s3.6-6 10-6 10 6 10 6-3.6 6-10 6S2 12 2 12z"/><circle cx="12" cy="12" r="2.4"/></svg>'; }
function trashIcon() { return '<svg viewBox="0 0 24 24"><path d="M4 7h16M9 7V4h6v3M7 7l1 13h8l1-13"/></svg>'; }

function renderAnalysis() {
  const box = $('#analysisBox');
  const meta = $('#analysisMeta');
  const section = $('#analysisSection');
  if (!box) return;
  section.hidden = state.mode === 'space' || state.tab === 'geometry';
  if (section.hidden) return;

  if (state.tab === 'conic') {
    const c = state.conicResult;
    if (!c) {
      meta.textContent = '等待生成';
      box.innerHTML = '<div class="analysis-empty">设置参数并点击「生成并绘制曲线」，这里会显示标准方程、焦点、离心率、准线与渐近线。</div>';
      return;
    }
    meta.textContent = c.kind === 'circle' ? '圆' : c.kind === 'ellipse' ? '椭圆' : c.kind === 'parabola' ? '抛物线' : '双曲线';
    let html = `<div class="analysis-title"><span class="tag teal">${c.kind === 'circle' ? 'CIRCLE' : c.kind === 'ellipse' ? 'ELLIPSE' : c.kind === 'parabola' ? 'PARABOLA' : 'HYPERBOLA'}</span>标准方程</div>`;
    html += `<div class="math-line">${escMath(c.equation)}</div>`;
    if (c.general) html += `<div class="math-line" style="font-size:11.5px;color:#7a6f5c;margin-top:2px">一般式：${escMath(c.general)}</div>`;
    html += '<div class="metric-grid">' + c.props.map(([k, v]) => `<div class="metric"><span>${esc(k)}</span><b class="math" title="${esc(v)}">${esc(v)}</b></div>`).join('') + '</div>';
    if (c.kind === 'circle' && state.circleTangent) {
      const t = state.circleTangent;
      html += `<div style="margin-top:12px"><div class="analysis-title"><span class="tag" style="background:#ffe4ea;color:#be123c">TANGENT</span>切线方程</div>`;
      html += `<div class="math-line" style="font-size:11.5px">${t.lines.map(line => `${line.label ? esc(line.label) + '：' : ''}${escMath(line.equation)}`).join('<br>')}</div>`;
      html += '</div>';
    }
    html += `<button class="btn" data-copy="${esc(c.equation)}" style="margin-top:8px">复制方程</button>`;
    box.innerHTML = html;
    return;
  }

  const fn = activeFn();
  if (!fn) {
    meta.textContent = '等待绘制';
    box.innerHTML = '<div class="analysis-empty">输入函数或方程，点击「绘制」或按 Enter。支持 y=…、f(x)=…、普通表达式，以及圆的标准式 / 一般式方程。</div>';
    return;
  }
  meta.textContent = '函数';
  let html = `<div class="analysis-title"><span class="tag">FUNCTION</span>当前函数</div>`;
  html += `<div class="math-line">f(x) = ${escMath(toStr(fn.ast))}</div>`;
  html += '<div class="metric-grid"><div class="metric"><span>颜色</span><b style="color:' + fn.color + '">f' + subscript(state.functions.indexOf(fn) + 1) + '(x)</b></div><div class="metric"><span>状态</span><b>' + (fn.visible ? '已显示' : '已隐藏') + '</b></div></div>';

  const calc = state.calc && state.calc.fnId === fn.id ? state.calc : null;
  if (calc && calc.deriv) {
    const d = calc.deriv;
    html += `<div style="margin-top:11px"><div class="analysis-title"><span class="tag amber">DERIVATIVE</span>导函数解析式</div>`;
    html += `<div class="math-line">f′(x) = ${escMath(d.expr)}</div>`;
    html += `<div class="metric-grid">
      <div class="metric"><span>x₀</span><b>${fmt(d.x0)}</b></div>
      <div class="metric"><span>f(x₀)</span><b>${fmt(d.y0)}</b></div>
      <div class="metric"><span>f′(x₀)</span><b>${fmt(d.slope, 5)}</b></div>
      <div class="metric"><span>切线</span><b class="math">${escMath(d.tangent)}</b></div>
    </div></div>`;
  }
  if (calc && calc.integral) {
    const it = calc.integral;
    html += `<div style="margin-top:11px"><div class="analysis-title"><span class="tag">INTEGRAL</span>定积分 / 不定积分</div>`;
    if (it.singular) {
      html += '<div class="analysis-empty" style="color:#92400e">区间内存在不连续点或奇点，数值积分无法给出稳定结果。</div>';
    } else {
      html += `<div class="math-line">∫<sub>${fmt(it.a)}</sub><sup>${fmt(it.b)}</sup> f(x) dx ≈ <b>${fmt(it.value, 6)}</b></div>`;
    }
    if (it.antideriv) {
      html += `<div class="math-line" style="margin-top:5px">∫ f(x) dx = ${escMath(it.antideriv)} + C</div>`;
    } else {
      html += '<div class="analysis-empty" style="margin-top:5px">该函数暂未找到初等原函数，仍可用数值方式计算定积分。</div>';
    }
    html += `<div class="metric-grid"><div class="metric"><span>积分区间</span><b>${fmt(it.a)} → ${fmt(it.b)}</b></div><div class="metric"><span>方法</span><b>Simpson</b></div></div></div>`;
  }
  box.innerHTML = html;
}

function prettyLineCoefficients(A, B, C) {
  const scales = [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 25, 30, 40, 50, 60, 80, 100];
  for (const k of scales) {
    const ai = Math.round(A * k), bi = Math.round(B * k), ci = Math.round(C * k);
    if (Math.abs(A * k - ai) < 2e-5 && Math.abs(B * k - bi) < 2e-5 && Math.abs(C * k - ci) < 2e-5) {
      const gcd = (x, y) => y ? gcd(y, x % y) : Math.abs(x);
      let g = gcd(gcd(ai, bi), ci) || 1;
      return [ai / g, bi / g, ci / g];
    }
  }
  return null;
}

function lineEquation(a, b) {
  let A = b.y - a.y, B = a.x - b.x, C = b.x * a.y - a.x * b.y;
  if (A < -1e-9 || (Math.abs(A) < 1e-9 && B < 0)) { A = -A; B = -B; C = -C; }
  const pretty = prettyLineCoefficients(A, B, C);
  if (pretty) {
    A = pretty[0]; B = pretty[1]; C = pretty[2];
  } else {
    const l = Math.hypot(A, B) || 1;
    A /= l; B /= l; C /= l;
  }
  let s = '';
  if (Math.abs(A) > 1e-9) s = `${fmtCoef(A)}x`;
  if (Math.abs(B) > 1e-9) {
    if (s) s += ` ${fmtSigned(B)}y`;
    else s = `${fmtCoef(B)}y`;
  }
  if (Math.abs(C) > 1e-9) s += ` ${fmtSigned(C)}`;
  if (!s) s = '0';
  return `${s} = 0`;
}
function fmtCoef(v) {
  if (Math.abs(v - 1) < 5e-4) return '';
  if (Math.abs(v + 1) < 5e-4) return '−';
  return fmt(v);
}

function renderSelection() {
  syncDerivedPoints();
  const box = $('#selectionBox');
  const meta = $('#selMeta');
  const section = $('#selectionSection');
  if (!box) return;
  const show = state.mode !== 'space' && state.tab === 'geometry';
  section.hidden = !show;
  if (!show) return;
  const sel = state.selected;
  if (!sel) {
    meta.textContent = '未选择';
    box.innerHTML = '<div class="analysis-empty">在画布或对象列表中选择一个图形，查看边长、角度、面积与方程。</div>';
    const del = $('#deleteBtn'); if (del) del.disabled = true;
    return;
  }
  const del = $('#deleteBtn'); if (del) del.disabled = false;
  if (sel.kind === 'point') {
    const p = getPt(sel.id);
    if (!p) { state.selected = null; return renderSelection(); }
    meta.textContent = '点 ' + p.label;
    const related = state.geom.shapes.filter(s => s.points.includes(p.id)).map(s => shapeLabel(s));
    const mid = p.derived && p.derived.type === 'midpoint' ? {
      a: getPt(p.derived.a), b: getPt(p.derived.b)
    } : null;
    box.innerHTML = `<div class="sel-title">点 ${esc(p.label)} <span class="pill">${mid ? 'MIDPOINT' : p.imageOf ? 'IMAGE' : 'POINT'}</span></div>
      <div class="sel-sub">${mid ? '线段中点：由两端点唯一确定，拖动端点时自动同步。' : p.imageOf ? '该点是变换得到的像点。' : '拖动该点可以改变所有与它相连的图形。'}</div>
      <div class="measure-row"><span>x 坐标</span><b>${fmt(p.x, 4)}</b></div>
      <div class="measure-row"><span>y 坐标</span><b>${fmt(p.y, 4)}</b></div>
      ${mid ? `<div class="measure-row"><span>所属线段</span><b class="txt">${esc((mid.a ? mid.a.label : '?') + (mid.b ? mid.b.label : '?'))} 的中点</b></div>` : ''}
      <div class="measure-row"><span>关联图形</span><b class="txt">${related.length ? esc(related.join('、')) : '—'}</b></div>`;
    if (mid && mid.a && mid.b) {
      box.innerHTML += `<div class="mark-note">已知 ${esc(mid.a.label)}、${esc(mid.b.label)}，${esc(p.label)} 满足 ${esc(mid.a.label + p.label)} = ${esc(p.label + mid.b.label)}。</div>`;
    }
    return;
  }
  if (sel.kind === 'shape') {
    const s = getShape(sel.id);
    if (!s) { state.selected = null; return renderSelection(); }
    meta.textContent = '图形';
    box.innerHTML = shapeDetailHTML(s);
    return;
  }
  if (sel.kind === 'mark') {
    const m = state.geom.marks.find(x => x.id === sel.id);
    if (!m) { state.selected = null; return renderSelection(); }
    meta.textContent = m.type === 'congruent' ? '全等' : '相似';
    const A = getShape(m.a), B = getShape(m.b);
    const ma = A && triangleMetrics(A), mb = B && triangleMetrics(B);
    if (!ma || !mb) { box.innerHTML = '<div class="analysis-empty">关系标记的三角形已不存在。</div>'; return; }
    const orderA = ma.labels.join('');
    const orderB = m.map.map(i => mb.labels[i]).join('');
    const sym = m.type === 'congruent' ? '≅' : '∽';
    const ratio = mb.perimeter / ma.perimeter;
    let html = `<div class="sel-title">${sym} ${m.type === 'congruent' ? '全等标记' : '相似标记'} <span class="pill">${m.type === 'congruent' ? 'CONGRUENT' : 'SIMILAR'}</span></div>
      <div class="math-line">△${esc(orderA)} ${sym} △${esc(orderB)}</div>`;
    html += `<div class="measure-row"><span>对应边</span><b class="txt">${ma.sides.map((v, i) => `${fmt(v, 2)} ↔ ${fmt(mb.sides[m.map[i]], 2)}`).join('；')}</b></div>`;
    html += `<div class="measure-row"><span>对应角</span><b class="txt">${ma.angles.map((v, i) => `${fmt(v, 1)}° ↔ ${fmt(mb.angles[m.map[i]], 1)}°`).join('；')}</b></div>`;
    html += `<div class="measure-row"><span>${m.type === 'congruent' ? '边长比' : '相似比 k'}</span><b>${fmt(ratio, 4)}</b></div>`;
    const still = matchTriangles(A, B, m.type);
    if (!still || !still.ok) {
      html += `<div class="mark-note" style="background:#fff7ed;border-color:#fed7aa;color:#9a3412">图形已被拖动，当前不再满足${m.type === 'congruent' ? '全等' : '相似'}条件；画布上会以灰色提示“关系已改变”。</div>`;
    }
    html += `<div class="mark-note ${m.type === 'similar' ? 'sim' : ''}">相同数量的短刻线表示对应边，相同数量的角弧表示对应角。整体拖动图形时关系保持不变。</div>`;
    box.innerHTML = html;
    return;
  }
}

function shapeDetailHTML(s) {
  const head = `<div class="sel-title">${esc(shapeLabel(s))} <span class="pill">${s.type === 'triangle' ? 'TRIANGLE' : s.type === 'quad' ? 'QUADRILATERAL' : s.type === 'circle' ? 'CIRCLE' : s.type === 'angle' ? 'ANGLE' : s.type === 'segment' ? 'SEGMENT' : s.type === 'ray' ? 'RAY' : s.type === 'line' ? 'LINE' : 'CONSTRUCTION'}</span>${s.imageOf ? '<span class="pill" style="color:#2563eb;background:#eaf1ff">变换像</span>' : ''}</div>`;
  if (s.type === 'triangle') {
    const m = triangleMetrics(s);
    if (!m) return head;
    return head + `<div class="sel-sub">${esc(m.className)} · 顶点 ${esc(m.labels.join('、'))}</div>
      <div class="measure-row"><span>边长 AB / BC / CA</span><b>${fmt(m.sides[2], 3)} / ${fmt(m.sides[0], 3)} / ${fmt(m.sides[1], 3)}</b></div>
      <div class="measure-row"><span>∠A / ∠B / ∠C</span><b>${fmt(m.angles[0], 2)}° / ${fmt(m.angles[1], 2)}° / ${fmt(m.angles[2], 2)}°</b></div>
      <div class="measure-row"><span>周长</span><b>${fmt(m.perimeter, 3)}</b></div>
      <div class="measure-row"><span>面积</span><b>${fmt(m.area, 3)}</b></div>
      <div class="measure-row"><span>判定</span><b class="txt">${m.eq ? '三边相等' : m.iso ? '两边相等' : '三边不等'}${m.right ? ' · 含直角' : ''}</b></div>
      ${CONSTRAINED_TRIANGLE_KINDS.includes(s.kind) ? '<div class="mark-note">拖动任一顶点时，以对边中点为基准等比缩放，形状和角度保持不变。</div>' : ''}
      ${apexEditorHTML(s)}`;
  }
  if (s.type === 'quad') {
    const m = quadMetrics(s);
    if (!m) return head;
    const diag1 = dist(m.pts[0], m.pts[2]), diag2 = dist(m.pts[1], m.pts[3]);
    return head + `<div class="sel-sub">${esc(m.className)} · 顶点 ${esc(m.labels.join('、'))}</div>
      <div class="measure-row"><span>四条边</span><b>${m.sides.map(v => fmt(v, 2)).join(' / ')}</b></div>
      <div class="measure-row"><span>四个角</span><b>${m.angles.map(v => fmt(v, 1) + '°').join(' / ')}</b></div>
      <div class="measure-row"><span>对角线</span><b>${fmt(diag1, 3)} / ${fmt(diag2, 3)}</b></div>
      <div class="measure-row"><span>周长</span><b>${fmt(m.perimeter, 3)}</b></div>
      <div class="measure-row"><span>面积</span><b>${fmt(m.area, 3)}</b></div>
      ${CONSTRAINED_QUAD_KINDS.includes(s.kind) ? '<div class="mark-note">拖动任一顶点时，以对角顶点为位似中心等比缩放，形状保持不变。</div>' : ''}
      ${quadAngleEditorHTML(s)}`;
  }
  if (s.type === 'angle') {
    const p = shapePoints(s);
    if (p.length < 3) return head;
    const value = deg(angleAt(p[1], p[0], p[2]));
    const isAlpha = state.geom.alpha && state.geom.alpha.shapeId === s.id;
    return head + `<div class="sel-sub">顺序：边上一点 ${esc(p[0].label)} → 顶点 ${esc(p[1].label)} → 边上一点 ${esc(p[2].label)}</div>
      <div class="math-line">∠${esc(p[0].label + p[1].label + p[2].label)} = ${fmt(value, 3)}°</div>
      <div class="measure-row"><span>顶点</span><b>${esc(p[1].label)} (${fmt(p[1].x, 2)}, ${fmt(p[1].y, 2)})</b></div>
      <div class="measure-row"><span>两边</span><b class="txt">${esc(p[1].label + p[0].label)} / ${esc(p[1].label + p[2].label)}</b></div>
      <div class="apex-hint">${isAlpha ? '这个角当前就是 α。' : '用「取角 α」工具依次点击这三个点，即可把它设为 α。'}</div>`;
  }
  if (s.type === 'circle') {
    const p = shapePoints(s);
    if (p.length < 2) return head;
    const r = dist(p[0], p[1]);
    return head + `<div class="sel-sub">圆心 ${esc(p[0].label)}，半径由 ${esc(p[0].label)}${esc(p[1].label)} 确定</div>
      <div class="measure-row"><span>半径 r</span><b>${fmt(r, 3)}</b></div>
      <div class="measure-row"><span>周长 2πr</span><b>${fmt(TAU * r, 3)}</b></div>
      <div class="measure-row"><span>面积 πr²</span><b>${fmt(Math.PI * r * r, 3)}</b></div>
      <div class="measure-row"><span>方程</span><b class="txt">(x − ${fmt(p[0].x, 2)})² + (y − ${fmt(p[0].y, 2)})² = ${fmt(r * r, 3)}</b></div>`;
  }
  if (s.type === 'segment' || s.type === 'ray' || s.type === 'line') {
    const p = shapePoints(s);
    if (p.length < 2) return head;
    const len = dist(p[0], p[1]);
    let html = head + `<div class="sel-sub">由 ${esc(p[0].label)}、${esc(p[1].label)} 两点确定</div>
      <div class="measure-row"><span>两点距离</span><b>${fmt(len, 3)}</b></div>`;
    if (s.type !== 'segment') html += `<div class="measure-row"><span>方程</span><b class="txt">${esc(lineEquation(p[0], p[1]))}</b></div>`;
    if (s.type === 'ray') html += `<div class="measure-row"><span>方向</span><b class="txt">${esc(p[0].label)} → ${esc(p[1].label)}</b></div>`;
    return html;
  }
  if (s.type === 'perp-bisector') {
    const p = shapePoints(s);
    if (p.length < 2) return head;
    const m = mid(p[0], p[1]);
    const n = perp(sub(p[1], p[0]));
    return head + `<div class="sel-sub">线段 ${esc(p[0].label + p[1].label)} 的垂直平分线</div>
      <div class="measure-row"><span>中点</span><b>(${fmt(m.x, 3)}, ${fmt(m.y, 3)})</b></div>
      <div class="measure-row"><span>方程</span><b class="txt">${esc(lineEquation(m, { x: m.x + n.x, y: m.y + n.y }))}</b></div>
      <div class="measure-row"><span>性质</span><b class="txt">到两端点距离相等</b></div>`;
  }
  if (s.type === 'angle-bisector') {
    const p = shapePoints(s);
    if (p.length < 3) return head;
    const u = norm(sub(p[1], p[0])), v = norm(sub(p[2], p[0]));
    let d = norm({ x: u.x + v.x, y: u.y + v.y });
    if (Math.hypot(d.x, d.y) < 1e-9) d = perp(u);
    return head + `<div class="sel-sub">∠${esc(p[1].label + p[0].label + p[2].label)} 的角平分线</div>
      <div class="measure-row"><span>顶点</span><b>${esc(p[0].label)} (${fmt(p[0].x, 2)}, ${fmt(p[0].y, 2)})</b></div>
      <div class="measure-row"><span>被分角</span><b>${fmt(deg(angleAt(p[0], p[1], p[2])), 2)}°</b></div>
      <div class="measure-row"><span>方程</span><b class="txt">${esc(lineEquation(p[0], { x: p[0].x + d.x, y: p[0].y + d.y }))}</b></div>`;
  }
  return head;
}

function renderAllPanels() {
  syncDerivedPoints();
  renderObjectList();
  renderAnalysis();
  renderSelection();
  updateTransformUI();
  updateToolbarVisibility();
}

/* ============================================================
   函数 / 圆锥曲线操作
   ============================================================ */

function normalizeFunctionInput(raw) {
  let s = String(raw || '').trim()
    .replace(/[−–—]/g, '-')
    .replace(/[（]/g, '(').replace(/[）]/g, ')')
    .replace(/[＝]/g, '=')
    .replace(/²/g, '^2');
  s = s.replace(/^y\s*=\s*/i, '');
  s = s.replace(/^[a-zA-Z]\s*\(\s*x\s*\)\s*=\s*/i, '');
  s = s.trim();
  if (!s) throw new Error('等号后面没有表达式');
  if (s.includes('=')) throw new Error('暂不支持这种隐式方程；圆方程可直接输入 (x−h)²+(y−k)²=r²');
  return s;
}

function coefficientOfToken(token) {
  if (token === '' || token === '+') return 1;
  if (token === '-') return -1;
  const n = parseFloat(token);
  return Number.isFinite(n) ? n : 0;
}

function parseCircleEquation(raw) {
  if (typeof raw !== 'string' || !raw.includes('=')) return null;
  let s = raw.trim()
    .replace(/[−–—]/g, '-')
    .replace(/[（]/g, '(').replace(/[）]/g, ')')
    .replace(/²/g, '^2')
    .replace(/[＝]/g, '=')
    .replace(/\s+/g, '');
  if (/^(y|[a-zA-Z]\(x\))=/i.test(s)) return null;
  let m = s.match(/^\(x([+-]\d+(?:\.\d+)?)?\)\^2\+\(y([+-]\d+(?:\.\d+)?)?\)\^2=(\d+(?:\.\d+)?)$/);
  if (m) {
    const h = -parseFloat(m[1] || '0');
    const k = -parseFloat(m[2] || '0');
    const r2 = parseFloat(m[3]);
    if (!(r2 > 0)) return null;
    return { h, k, r: Math.sqrt(r2), source: raw };
  }
  const parts = s.split('=');
  if (parts.length !== 2) return null;
  let body = parts[0], rhs = parts[1];
  if (rhs !== '0') {
    if (!/^[+-]?\d+(?:\.\d+)?$/.test(rhs)) return null;
    body += rhs.startsWith('-') ? '+' + rhs.slice(1) : '-' + rhs;
  }
  body = body.replace(/\*/g, '');
  const terms = body.replace(/-/g, '+-').split('+').filter(Boolean);
  if (!terms.length) return null;
  let A = 0, B = 0, D = 0, E = 0, F = 0;
  for (const term of terms) {
    let mm;
    if ((mm = term.match(/^([+-]?\d*\.?\d*)x\^2$/))) A += coefficientOfToken(mm[1]);
    else if ((mm = term.match(/^([+-]?\d*\.?\d*)y\^2$/))) B += coefficientOfToken(mm[1]);
    else if ((mm = term.match(/^([+-]?\d*\.?\d*)x$/))) D += coefficientOfToken(mm[1]);
    else if ((mm = term.match(/^([+-]?\d*\.?\d*)y$/))) E += coefficientOfToken(mm[1]);
    else if ((mm = term.match(/^([+-]?\d*\.?\d*)$/))) F += coefficientOfToken(mm[1]);
    else return null;
  }
  if (Math.abs(A) < 1e-9 || Math.abs(B) < 1e-9 || Math.abs(A - B) > 1e-6) return null;
  const h = -D / (2 * A), k = -E / (2 * A);
  const r2 = h * h + k * k - F / A;
  if (!(r2 > 1e-8)) return null;
  return { h, k, r: Math.sqrt(r2), source: raw };
}

function applyCircleEquation(raw) {
  const c = parseCircleEquation(raw);
  if (!c) {
    toast('无法识别为圆方程。支持 (x−h)²+(y−k)²=r² 与 x²+y²+Dx+Ey+F=0', 'warn');
    return false;
  }
  pushHistory();
  state.conicType = 'circle';
  state.conicParams.circle = { h: c.h, k: c.k, r: c.r };
  state.circleTangent = null;
  state.tangentPicking = false;
  $$('.conic-type').forEach(b => b.classList.toggle('active', b.dataset.conic === 'circle'));
  renderConicFields();
  generateConic(false);
  const eqInput = $('#circleEqInput');
  if (eqInput) eqInput.value = raw;
  return true;
}

function addFunctionFromInput() {
  const input = $('#exprInput');
  const raw = input.value.trim();
  if (!raw) { toast('请输入函数或方程', 'warn'); input.focus(); return; }
  if (parseCircleEquation(raw)) {
    applyCircleEquation(raw);
    input.focus();
    return;
  }
  let exprText;
  try { exprText = normalizeFunctionInput(raw); }
  catch (err) { toast(err.message, 'warn'); input.focus(); return; }
  let ast;
  try { ast = parseExpression(exprText); }
  catch (err) { toast('表达式有误：' + err.message, 'bad'); input.focus(); return; }
  const existing = state.functions.find(f => f.expr.replace(/\s+/g, '') === exprText.replace(/\s+/g, ''));
  if (existing) {
    state.activeFnId = existing.id;
    state.analysisMode = 'function';
    state.calc = null;
    resetCalcHints();
    setTab('function');
    renderAnalysis();
    toast('这条函数已经在画布上了，已切换为当前函数。', 'ok');
    draw(); saveSoon();
    return;
  }
  const fn = {
    id: uid('f'), expr: exprText, ast, color: fnColor(state.functions.length),
    visible: true
  };
  pushHistory();
  state.functions.push(fn);
  if (state.functions.length > 6) {
    const removed = state.functions.shift();
    if (state.activeFnId === removed.id) state.activeFnId = null;
    state.functions.forEach((f, i) => { f.color = fnColor(i); });
  }
  state.activeFnId = fn.id;
  state.calc = null;
  resetCalcHints();
  state.analysisMode = 'function';
  if (state.tab !== 'function') setTab('function');
  renderObjectList(); renderAnalysis(); draw(); saveSoon();
}

function resetCalcHints() {
  const d = $('#derivHint'), i = $('#integralHint');
  if (d) d.innerHTML = '点击 ↗ 计算当前函数的 f′(x₀) 与切线方程。';
  if (i) i.innerHTML = '用自适应 Simpson 法计算定积分，并给出可符号化的原函数。';
}

function selectFunction(id) {
  if (!state.functions.some(f => f.id === id)) return;
  state.activeFnId = id;
  const fn = activeFn();
  $('#exprInput').value = fn.expr;
  state.calc = null;
  resetCalcHints();
  state.analysisMode = 'function';
  if (state.mode === 'space') setMode('plane');
  if (state.tab !== 'function') setTab('function');
  renderObjectList(); renderAnalysis(); draw(); saveSoon();
}

function computeDerivative() {
  const fn = activeFn();
  if (!fn) { toast('请先绘制一条函数', 'warn'); return; }
  const x0 = parseFloat($('#x0Input').value);
  if (!Number.isFinite(x0)) { toast('x₀ 需要是有效数字', 'warn'); return; }
  let expr, newAst;
  try {
    newAst = simplify(differentiate(fn.ast));
    expr = toStr(newAst);
  } catch {
    expr = '（符号求导失败，使用数值结果）';
    newAst = null;
  }
  const f = x => evalNode(fn.ast, x);
  const y0 = f(x0);
  const slope = numericDerivative(f, x0);
  const tangent = tangentEquation(slope, x0, y0);
  pushHistory();
  state.calc = Object.assign({}, state.calc, {
    fnId: fn.id,
    deriv: { expr, x0, y0, slope, tangent }
  });
  state.analysisMode = 'function';
  const tanToggle = $('#showTangent');
  if (tanToggle) tanToggle.checked = true;
  const hint = $('#derivHint');
  if (hint) hint.innerHTML = `<b>f′(x) = ${esc(expr)}</b><br>f′(${fmt(x0)}) = ${fmt(slope, 5)} · 切线 ${esc(tangent)}`;
  renderAnalysis();
  if (state.mode === 'space') setMode('plane');
  draw(); saveSoon();
  if (!Number.isFinite(y0) || !Number.isFinite(slope)) toast('该 x₀ 不在函数定义域内，或函数在此处不可导。', 'warn');
  else toast('已求导，并在画布上标出切线。', 'ok');
}

function tangentEquation(k, x0, y0) {
  if (!Number.isFinite(k) || !Number.isFinite(x0) || !Number.isFinite(y0)) return '—';
  const b = y0 - k * x0;
  if (Math.abs(k) < 1e-10) return `y = ${fmt(y0)}`;
  let kStr;
  if (Math.abs(k - 1) < 1e-10) kStr = 'x';
  else if (Math.abs(k + 1) < 1e-10) kStr = '−x';
  else kStr = `${fmt(k)}x`;
  if (Math.abs(b) < 1e-10) return `y = ${kStr}`;
  return `y = ${kStr} ${b > 0 ? '+' : '−'} ${fmt(Math.abs(b))}`;
}

function computeIntegral() {
  const fn = activeFn();
  if (!fn) { toast('请先绘制一条函数', 'warn'); return; }
  const a = parseFloat($('#aInput').value), b = parseFloat($('#bInput').value);
  if (!Number.isFinite(a) || !Number.isFinite(b)) { toast('积分上下限需要是有效数字', 'warn'); return; }
  const f = x => evalNode(fn.ast, x);
  const r = autoIntegrate(f, a, b);
  let antideriv = null;
  try {
    const anti = integrateNode(fn.ast);
    if (anti) antideriv = toStr(simplify(anti));
  } catch { antideriv = null; }
  pushHistory();
  state.calc = Object.assign({}, state.calc, {
    fnId: fn.id,
    integral: { a, b, value: r.value, singular: r.singular, antideriv }
  });
  state.analysisMode = 'function';
  const areaToggle = $('#showArea');
  if (areaToggle) areaToggle.checked = true;
  const hint = $('#integralHint');
  if (hint) {
    let msg = r.singular
      ? '区间内存在不连续点或奇点，未能得到稳定的定积分值。'
      : `<b>∫<sub>${esc(fmt(a))}</sub><sup>${esc(fmt(b))}</sup> f(x) dx ≈ ${esc(fmt(r.value, 6))}</b>`;
    msg += antideriv
      ? `<br>不定积分：∫ f(x) dx = ${esc(antideriv)} + C`
      : '<br>不定积分：暂未找到初等原函数。';
    hint.innerHTML = msg;
  }
  renderAnalysis();
  if (state.mode === 'space') setMode('plane');
  draw(); saveSoon();
  if (r.singular) toast('区间内存在奇点，未得到稳定的积分值。', 'warn');
  else toast('已计算定积分与不定积分。', 'ok');
}

/* ---------- 圆锥曲线表单 ---------- */

function renderConicFields() {
  const box = $('#conicFields');
  if (!box) return;
  const type = state.conicType;
  $$('.conic-type').forEach(b => b.classList.toggle('active', b.dataset.conic === type));
  const p = state.conicParams[type];
  let html = '<div class="param-grid">';
  html += `<div class="f"><label>中心 h</label><input data-ck="h" value="${esc(p.h)}" inputmode="decimal"></div>`;
  html += `<div class="f"><label>中心 k</label><input data-ck="k" value="${esc(p.k)}" inputmode="decimal"></div>`;
  if (type === 'circle') {
    html += `<div class="f wide"><label>半径 r</label><input data-ck="r" value="${esc(p.r)}" inputmode="decimal"></div>`;
  } else if (type === 'ellipse') {
    html += `<div class="f"><label>半轴 a</label><input data-ck="a" value="${esc(p.a)}" inputmode="decimal"></div>`;
    html += `<div class="f"><label>半轴 b</label><input data-ck="b" value="${esc(p.b)}" inputmode="decimal"></div>`;
  } else if (type === 'parabola') {
    html += `<div class="f"><label>焦准距 p</label><input data-ck="p" value="${esc(p.p)}" inputmode="decimal"></div>`;
    html += `<div class="f"><label>开口方向</label><select data-ck="orient">
      <option value="right" ${p.orient === 'right' ? 'selected' : ''}>向右</option>
      <option value="left" ${p.orient === 'left' ? 'selected' : ''}>向左</option>
      <option value="up" ${p.orient === 'up' ? 'selected' : ''}>向上</option>
      <option value="down" ${p.orient === 'down' ? 'selected' : ''}>向下</option>
    </select></div>`;
  } else {
    html += `<div class="f"><label>实半轴 a</label><input data-ck="a" value="${esc(p.a)}" inputmode="decimal"></div>`;
    html += `<div class="f"><label>虚半轴 b</label><input data-ck="b" value="${esc(p.b)}" inputmode="decimal"></div>`;
    html += `<div class="f wide"><label>开口方向</label><select data-ck="orient">
      <option value="horizontal" ${p.orient === 'horizontal' ? 'selected' : ''}>左右开口（横轴）</option>
      <option value="vertical" ${p.orient === 'vertical' ? 'selected' : ''}>上下开口（纵轴）</option>
    </select></div>`;
  }
  html += '</div>';
  box.innerHTML = html;
  $$('[data-ck]', box).forEach(el => {
    el.addEventListener('input', () => {
      const key = el.dataset.ck;
      const val = el.tagName === 'SELECT' ? el.value : (parseFloat(el.value) || 0);
      state.conicParams[type][key] = val;
      if (type === 'circle' && state.circleTangent) {
        state.circleTangent = null;
        updateTangentUI();
      }
      updateConicPreview();
      saveSoon();
    });
  });
  updateConicPreview();
  const tools = $('#circleTools');
  if (tools) tools.hidden = type !== 'circle';
  updateTangentUI();
}

function updateConicPreview() {
  const target = $('#conicFormula');
  if (!target) return;
  try {
    const c = buildConic(state.conicType, state.conicParams[state.conicType]);
    target.innerHTML = `<b>标准方程</b><div class="mono">${esc(c.equation)}</div><div style="margin-top:3px;color:#9a8f7a">${c.props.slice(0, 2).map(([k, v]) => esc(k) + '：' + esc(v)).join(' · ')}</div>`;
  } catch (err) {
    target.innerHTML = `<span style="color:#b91c1c">${esc(err.message)}</span>`;
  }
}

function generateConic(recordHistory = true) {
  try {
    const c = buildConic(state.conicType, state.conicParams[state.conicType]);
    c.visible = true;
    if (recordHistory) pushHistory();
    state.curve = c;
    state.conicResult = c;
    state.circleTangent = null;
    state.tangentPicking = false;
    state.analysisMode = 'conic';
    if (state.mode === 'space') setMode('plane');
    if (state.tab !== 'conic') setTab('conic');
    fitCurve(c);
    if (c.kind === 'circle') {
      const tx = $('#tangentX'), ty = $('#tangentY');
      if (tx) tx.value = fmt(c.h + c.r, 3);
      if (ty) ty.value = fmt(c.k, 3);
    }
    renderObjectList(); renderAnalysis(); updateTangentUI(); draw(); saveSoon();
    toast('已生成' + (c.kind === 'circle' ? '圆' : c.kind === 'ellipse' ? '椭圆' : c.kind === 'parabola' ? '抛物线' : '双曲线') + '，右侧可查看全部性质。', 'ok');
  } catch (err) {
    toast(err.message, 'bad');
  }
}

/* ---------- 圆的切线 ---------- */

function computeCircleTangent(point) {
  const c = state.curve;
  if (!c || c.kind !== 'circle') { toast('请先生成一个圆', 'warn'); return false; }
  const q = { x: Number(point.x), y: Number(point.y) };
  if (!Number.isFinite(q.x) || !Number.isFinite(q.y)) { toast('切点坐标无效', 'warn'); return false; }
  const dx = q.x - c.h, dy = q.y - c.k;
  const d = Math.hypot(dx, dy);
  if (d < 1e-8) { toast('圆心处不能作切线', 'warn'); return false; }
  const tol = Math.max(8 / Math.max(1e-6, scale2d()), c.r * 0.004);
  let kind, tangentPoints = [], lines = [], picked = q;
  if (Math.abs(d - c.r) <= tol) {
    const ux = dx / d, uy = dy / d;
    const T = { x: c.h + ux * c.r, y: c.k + uy * c.r };
    const dir = { x: -uy, y: ux };
    picked = T;
    kind = 'on';
    tangentPoints = [T];
    lines = [{ p1: T, p2: { x: T.x + dir.x, y: T.y + dir.y }, equation: lineEquation(T, { x: T.x + dir.x, y: T.y + dir.y }) }];
  } else if (d > c.r) {
    const theta = Math.atan2(dy, dx);
    const phi = Math.acos(clamp(c.r / d, -1, 1));
    for (const [sign, label] of [[1, 'T₁'], [-1, 'T₂']]) {
      const a = theta + sign * phi;
      const T = { x: c.h + c.r * Math.cos(a), y: c.k + c.r * Math.sin(a) };
      tangentPoints.push(T);
      lines.push({ p1: q, p2: T, equation: lineEquation(q, T), label });
    }
    kind = 'external';
  } else {
    toast('点在圆内，过该点没有圆的切线', 'warn');
    state.tangentPicking = false;
    updateTangentUI();
    return false;
  }
  pushHistory();
  state.circleTangent = { point: picked, original: q, kind, tangentPoints, lines };
  state.tangentPicking = false;
  updateTangentUI(); renderAnalysis(); draw(); saveSoon();
  toast(kind === 'on' ? '已过圆上一点作切线。' : '已过圆外一点作两条切线。', 'ok');
  return true;
}

function drawCircleTangent() {
  const c = state.curve, t = state.circleTangent;
  if (!c || c.kind !== 'circle' || !t || !Array.isArray(t.lines) || !t.lines.length) return;
  const center = { x: c.h, y: c.k };
  for (const line of t.lines) {
    drawLineWorld(line.p1, line.p2, '#e11d48', 1.7, [7, 5]);
  }
  for (const T of (t.tangentPoints || [])) {
    drawPolyline([w2s(center), w2s(T)], 'rgba(225,29,72,.42)', 1.1, null, [3, 4]);
  }
  t.tangentPoints.forEach((T, i) => {
    const p = w2s(T);
    ctx.save();
    ctx.beginPath(); ctx.arc(p.x, p.y, 3.6, 0, TAU);
    ctx.fillStyle = '#e11d48'; ctx.fill();
    ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.4; ctx.stroke();
    ctx.restore();
    chip(t.kind === 'on' ? 'T' : (i === 0 ? 'T₁' : 'T₂'), p.x + 9, p.y - 10, '#be123c', 'rgba(255,247,249,.95)');
  });
  if (t.kind === 'external') {
    const p = w2s(t.original);
    ctx.save();
    ctx.beginPath(); ctx.arc(p.x, p.y, 4, 0, TAU);
    ctx.fillStyle = '#9f1239'; ctx.fill();
    ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.4; ctx.stroke();
    ctx.restore();
    chip('P', p.x + 9, p.y - 10, '#9f1239', 'rgba(255,247,249,.95)');
  }
}

function updateTangentUI() {
  const wrap = $('#circleTools');
  if (wrap) wrap.hidden = state.conicType !== 'circle';
  const pick = $('#tangentPick');
  if (pick) {
    pick.classList.toggle('active', !!state.tangentPicking);
    pick.textContent = state.tangentPicking ? '点击画布选择一点…（再次点击取消）' : '在画布上选一点作切线';
  }
  const res = $('#tangentResult');
  if (!res) return;
  const c = state.curve;
  if (!c || c.kind !== 'circle') {
    res.innerHTML = '先生成圆，再选择圆上一点或圆外一点。';
    return;
  }
  const t = state.circleTangent;
  if (!t || !t.lines || !t.lines.length) {
    res.innerHTML = '在圆上取一点得到 <b>一条切线</b>；在圆外取一点得到 <b>两条切线</b>。';
    return;
  }
  const eqs = t.lines.map(line => `<div><b>${line.label || '切线'}</b>：${escMath(line.equation)}</div>`).join('');
  if (t.kind === 'on') {
    res.innerHTML = `<div class="tangent-eq"><b>切点</b> T(${fmt(t.point.x, 3)}, ${fmt(t.point.y, 3)})<div>${eqs}</div><div class="small">半径 OT ⊥ 切线</div></div>`;
  } else {
    const dx = t.original.x - c.h, dy = t.original.y - c.k;
    const len = Math.sqrt(Math.max(0, dx * dx + dy * dy - c.r * c.r));
    res.innerHTML = `<div class="tangent-eq"><b>圆外点</b> P(${fmt(t.original.x, 3)}, ${fmt(t.original.y, 3)})<div>${eqs}</div><div class="small">切线长 = ${fmt(len, 3)}</div></div>`;
  }
}

/* ---------- 空间点 ---------- */

function renderSpacePointList() {
  const box = $('#spacePointList');
  if (!box) return;
  if (!state.space.points.length) {
    box.innerHTML = '<div class="empty-list" style="color:#b0a58f">还没有空间点</div>';
    return;
  }
  box.innerHTML = state.space.points.map(p => `<div class="space-point"><span>${esc(p.label)}</span><b>(${fmt(p.x, 2)}, ${fmt(p.y, 2)}, ${fmt(p.z, 2)})</b><button data-space-del="${p.id}" title="删除">×</button></div>`).join('');
}

function addSpacePoint() {
  const x = parseFloat($('#sx').value), y = parseFloat($('#sy').value), z = parseFloat($('#sz').value);
  if (!Number.isFinite(x) || !Number.isFinite(y) || !Number.isFinite(z)) { toast('请输入三个有效数字', 'warn'); return; }
  if (Math.abs(x) > 20 || Math.abs(y) > 20 || Math.abs(z) > 20) { toast('坐标建议在 −20 到 20 之间', 'warn'); return; }
  if (state.space.points.length >= 30) { toast('空间点最多添加 30 个', 'warn'); return; }
  pushHistory();
  const n = state.space.nextLabel || 0;
  const letters = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
  const label = letters[n % 26] + (Math.floor(n / 26) || '');
  state.space.nextLabel = n + 1;
  state.space.points.push({ id: uid('sp'), x, y, z, label, visible: true });
  renderSpacePointList(); renderObjectList(); draw(); saveSoon();
  toast(`已添加空间点 ${label}(${fmt(x, 2)}, ${fmt(y, 2)}, ${fmt(z, 2)})`, 'ok');
}

function removeSpacePoint(id, record = true) {
  if (record) pushHistory();
  state.space.points = state.space.points.filter(p => p.id !== id);
  renderSpacePointList(); renderObjectList(); draw(); saveSoon();
}

/* ============================================================
   画布交互
   ============================================================ */

function eventPos(e) {
  const r = canvas.getBoundingClientRect();
  return { x: e.clientX - r.left, y: e.clientY - r.top };
}
function snapWorld(sp, alt = false) {
  const p = hitTestPoint(sp, 13);
  if (p) return { x: p.x, y: p.y, pid: p.id };
  const w = s2w(sp);
  if (state.geom.snap && !alt) {
    const g = .5;
    return { x: Math.round(w.x / g) * g, y: Math.round(w.y / g) * g, pid: null };
  }
  return { x: w.x, y: w.y, pid: null };
}
function resolveRef(ref) {
  if (ref.pid) {
    const p = getPt(ref.pid);
    if (p) return p;
  }
  return makePoint(ref.x, ref.y);
}
function refsClose(a, b) { return Math.abs(a.x - b.x) < 1e-4 && Math.abs(a.y - b.y) < 1e-4; }

function handleToolClick(sp) {
  const tool = state.tool;
  if (tool === 'select') { selectAt(sp); return; }
  if (tool === 'midpoint') {
    const seg = lineShapeAt(sp);
    if (state.pending.length === 0 && seg && seg.type === 'segment') {
      const pts = shapePoints(seg);
      if (pts.length >= 2) {
        pushHistory();
        createMidpoint(pts[0], pts[1], seg.id);
        renderAllPanels(); draw(); saveSoon();
        return;
      }
    }
    const ref = snapWorld(sp, false);
    state.pending.push({ x: ref.x, y: ref.y, pid: ref.pid });
    if (state.pending.length < 2) {
      draw();
      toast('再点击线段的另一个端点', '');
      return;
    }
    const refs = state.pending.slice();
    state.pending = []; state.preview = null;
    completeShape('midpoint', refs);
    return;
  }
  if (tool === 'set-alpha') {
    const ref = snapWorld(sp, false);
    state.pending.push({ x: ref.x, y: ref.y, pid: ref.pid });
    if (state.pending.length < 3) {
      draw();
      toast(state.pending.length === 1 ? '已选边上一点，请点击顶点。' : '已选顶点，请点击另一边上的点。', '');
      return;
    }
    const refs = state.pending.slice();
    state.pending = []; state.preview = null;
    completeAlphaAngle(refs);
    return;
  }
  if (tool === 'rotate' || tool === 'reflect') {
    if (!state.transformTarget) {
      const p = hitTestPoint(sp, 12);
      const s = p ? null : hitTestShape(sp);
      if (!p && !s) { toast('请先点击要变换的点或图形', 'warn'); return; }
      state.transformTarget = p ? { kind: 'point', id: p.id } : { kind: 'shape', id: s.id };
      state.selected = { kind: state.transformTarget.kind, id: state.transformTarget.id };
      updateHint(); renderAllPanels(); draw();
      toast(tool === 'rotate' ? '已选图形，请点击一个点作为旋转中心。' : '已选图形，请点击一条直线 / 线段 / 射线作为对称轴。', '');
      return;
    }
    if (tool === 'rotate') {
      const center = hitTestPoint(sp, 13);
      if (!center) { toast('旋转中心必须是已有的点；可先作出一个点再旋转。', 'warn'); return; }
      let angle;
      try { angle = evalAngleExpression(state.rotateExpr); }
      catch (err) { toast(err.message, 'warn'); return; }
      applyTransformToTarget({ type: 'rotate', center: { x: center.x, y: center.y }, angle });
    } else {
      const axis = axisAtClick(sp);
      if (!axis) { toast('请点击一条直线、线段、射线或平分线作为对称轴。', 'warn'); return; }
      const line = axisLineForShape(axis);
      if (!line) { toast('这条线不能作为对称轴。', 'warn'); return; }
      applyTransformToTarget({ type: 'reflect', a: line[0], b: line[1] });
    }
    return;
  }
  if (tool === 'congruent' || tool === 'similar') {
    const tri = triangleAt(sp);
    if (!tri) { toast('请点击一个三角形内部', 'warn'); return; }
    if (!state.markFirst) {
      state.markFirst = tri.id;
      state.selected = { kind: 'shape', id: tri.id };
      renderSelection(); draw();
      toast('已选择第一个三角形，请再点击另一个三角形。', '');
      return;
    }
    if (state.markFirst === tri.id) { toast('请选择另一个三角形', 'warn'); return; }
    const A = getShape(state.markFirst);
    state.markFirst = null;
    if (!A) { toast('第一个三角形已不存在', 'warn'); return; }
    pushHistory();
    addRelationMark(tool, A, tri);
    state.pending = [];
    renderAllPanels(); draw(); saveSoon();
    return;
  }

  const ref = snapWorld(sp, false);
  if (tool === 'point') {
    if (ref.pid) {
      state.selected = { kind: 'point', id: ref.pid };
      renderAllPanels(); draw();
      return;
    }
    pushHistory();
    const p = makePoint(ref.x, ref.y);
    state.selected = { kind: 'point', id: p.id };
    renderAllPanels(); draw(); saveSoon();
    return;
  }

  const need = tool === 'triangle' || tool === 'angle-bisector' || tool === 'angle' ? 3 : 2;
  state.pending.push({ x: ref.x, y: ref.y, pid: ref.pid });
  if (state.pending.length < need) {
    draw();
    return;
  }
  const refs = state.pending.slice();
  state.pending = [];
  state.preview = null;
  completeShape(tool, refs);
}

function completeShape(tool, refs) {
  for (let i = 0; i < refs.length; i++) for (let j = i + 1; j < refs.length; j++) {
    if (refsClose(refs[i], refs[j])) { toast('所点的点不能重合', 'warn'); draw(); return; }
  }
  if (tool === 'midpoint') {
    pushHistory();
    const A = resolveRef(refs[0]), B = resolveRef(refs[1]);
    createMidpoint(A, B);
  } else if (tool === 'segment' || tool === 'ray' || tool === 'line') {
    pushHistory();
    const A = resolveRef(refs[0]), B = resolveRef(refs[1]);
    const s = addShape(tool, [A, B]);
    state.selected = { kind: 'shape', id: s.id };
    toast(`已创建${tool === 'segment' ? '线段' : tool === 'ray' ? '射线' : '直线'} ${A.label}${B.label}`, 'ok');
  } else if (tool === 'perp-bisector') {
    pushHistory();
    const A = resolveRef(refs[0]), B = resolveRef(refs[1]);
    const s = addShape('perp-bisector', [A, B]);
    state.selected = { kind: 'shape', id: s.id };
    toast(`已创建 ${A.label}${B.label} 的垂直平分线`, 'ok');
  } else if (tool === 'circle') {
    pushHistory();
    const O = resolveRef(refs[0]), A = resolveRef(refs[1]);
    if (dist(O, A) < 1e-4) { toast('半径不能为 0', 'warn'); return; }
    const s = addShape('circle', [O, A]);
    state.selected = { kind: 'shape', id: s.id };
    toast(`已创建圆 ${O.label}（半径 ${fmt(dist(O, A), 3)}）`, 'ok');
  } else if (tool === 'angle-bisector') {
    const [O, A, B] = refs;
    if (Math.abs(cross(sub(A, O), sub(B, O))) < 1e-4) { toast('三点共线，无法确定角', 'warn'); draw(); return; }
    pushHistory();
    const po = resolveRef(O), pa = resolveRef(A), pb = resolveRef(B);
    const s = addShape('angle-bisector', [po, pa, pb]);
    state.selected = { kind: 'shape', id: s.id };
    toast(`已创建 ∠${pa.label}${po.label}${pb.label} 的角平分线`, 'ok');
  } else if (tool === 'angle') {
    const [A, O, B] = refs;
    if (Math.abs(cross(sub(A, O), sub(B, O))) < 1e-4) { toast('三点共线，无法确定一个角', 'warn'); draw(); return; }
    pushHistory();
    const pa = resolveRef(A), po = resolveRef(O), pb = resolveRef(B);
    const s = addShape('angle', [pa, po, pb], 'angle');
    state.selected = { kind: 'shape', id: s.id };
    toast(`已建立 ∠${pa.label}${po.label}${pb.label}`, 'ok');
  } else if (tool === 'triangle') {
    if (Math.abs(cross(sub(refs[1], refs[0]), sub(refs[2], refs[0]))) < 1e-4) { toast('三点共线，无法组成三角形', 'warn'); draw(); return; }
    pushHistory();
    const A = resolveRef(refs[0]), B = resolveRef(refs[1]), C = resolveRef(refs[2]);
    createTriangle('triangle', A, B, C);
    toast('已创建三角形，可拖动顶点调整。', 'ok');
  } else if (['right-triangle', 'isosceles-triangle', 'right-isosceles', 'equilateral'].includes(tool)) {
    const base = horizontalTriangleBase(refs);
    const pos = autoTrianglePoints(base[0], base[1], tool);
    if (!pos) { toast('两个点距离太近', 'warn'); return; }
    pushHistory();
    const A = resolveAutoBasePoint(refs[0], base[0]), B = resolveAutoBasePoint(refs[1], base[1]);
    const C = makePoint(pos[2].x, pos[2].y);
    createTriangle(tool, A, B, C);
    toast(`已创建${TOOL_NAMES[tool]}，可拖动顶点调整。`, 'ok');
  } else if (['square', 'rectangle', 'parallelogram', 'rhombus'].includes(tool)) {
    const pos = autoQuadPoints(refs[0], refs[1], tool);
    if (!pos) { toast('两个点距离太近', 'warn'); return; }
    pushHistory();
    const A = resolveRef(refs[0]), B = resolveRef(refs[1]);
    const C = makePoint(pos[2].x, pos[2].y), D = makePoint(pos[3].x, pos[3].y);
    createQuad(tool, A, B, C, D);
    toast(`已创建${TOOL_NAMES[tool]}，可拖动顶点调整。`, 'ok');
  }
  renderAllPanels();
  draw();
  saveSoon();
}

function selectAt(sp) {
  const p = hitTestPoint(sp, 12);
  if (p) {
    state.selected = { kind: 'point', id: p.id };
    renderAllPanels(); draw();
    return p;
  }
  const s = hitTestShape(sp);
  if (s) {
    state.selected = { kind: 'shape', id: s.id };
    renderAllPanels(); draw();
    return s;
  }
  state.selected = null;
  renderAllPanels(); draw();
  return null;
}

function cancelPending() {
  const had = state.pending.length || state.markFirst || state.transformTarget;
  state.pending = []; state.preview = null; state.markFirst = null; state.transformTarget = null;
  if (had) { updateHint(); updateTransformUI(); draw(); toast('已取消当前操作'); }
  else if (state.selected) { state.selected = null; renderAllPanels(); draw(); }
}

function deleteSelected() {
  const sel = state.selected;
  if (!sel) return;
  if (sel.kind === 'shape' || sel.kind === 'point' || sel.kind === 'mark') {
    pushHistory();
    deleteGeomObjectSilent(sel.kind, sel.id);
    state.selected = null;
    renderAllPanels(); draw(); saveSoon();
    toast('已删除选中对象');
  }
}

function deleteGeomObjectSilent(kind, id) {
  if (kind === 'mark') {
    state.geom.marks = state.geom.marks.filter(m => m.id !== id);
    return;
  }
  if (kind === 'shape') {
    state.geom.marks = state.geom.marks.filter(m => m.a !== id && m.b !== id);
    state.geom.shapes = state.geom.shapes.filter(s => s.id !== id);
    state.geom.transforms = (state.geom.transforms || []).filter(t => t.sourceId !== id && t.imageId !== id);
    if (state.geom.alpha && state.geom.alpha.shapeId === id) state.geom.alpha = null;
    return;
  }
  if (kind === 'point') {
    const deadPoints = new Set([id]);
    let changed = true;
    while (changed) {
      changed = false;
      for (const p of state.geom.points) {
        if (p.derived && (deadPoints.has(p.derived.a) || deadPoints.has(p.derived.b)) && !deadPoints.has(p.id)) {
          deadPoints.add(p.id);
          changed = true;
        }
      }
    }
    const deadShapes = new Set(state.geom.shapes.filter(s => s.points.some(pid => deadPoints.has(pid))).map(s => s.id));
    state.geom.marks = state.geom.marks.filter(m => !deadShapes.has(m.a) && !deadShapes.has(m.b));
    state.geom.shapes = state.geom.shapes.filter(s => !deadShapes.has(s.id));
    state.geom.points = state.geom.points.filter(p => !deadPoints.has(p.id));
    state.geom.transforms = (state.geom.transforms || []).filter(t =>
      !(t.sourceKind === 'point' && deadPoints.has(t.sourceId)) &&
      !(t.imageKind === 'point' && deadPoints.has(t.imageId)) &&
      !(t.sourceKind === 'shape' && deadShapes.has(t.sourceId)) &&
      !(t.imageKind === 'shape' && deadShapes.has(t.imageId))
    );
    if (state.geom.alpha && deadShapes.has(state.geom.alpha.shapeId)) state.geom.alpha = null;
  }
}

function deleteObject(kind, id) {
  if (kind === 'fn') {
    const idx = state.functions.findIndex(f => f.id === id);
    if (idx < 0) return;
    pushHistory();
    state.functions.splice(idx, 1);
    state.functions.forEach((f, i) => { f.color = fnColor(i); });
    if (state.activeFnId === id) {
      state.activeFnId = state.functions[0] ? state.functions[0].id : null;
      state.calc = null;
      resetCalcHints();
      if (state.activeFnId) $('#exprInput').value = activeFn().expr;
    }
    renderObjectList(); renderAnalysis(); draw(); saveSoon();
    return;
  }
  if (kind === 'curve') {
    if (!state.curve) return;
    pushHistory();
    state.curve = null; state.conicResult = null;
    state.circleTangent = null; state.tangentPicking = false;
    updateTangentUI(); renderObjectList(); renderAnalysis(); draw(); saveSoon();
    return;
  }
  if (kind === 'space') { pushHistory(); removeSpacePoint(id, false); return; }
  pushHistory();
  deleteGeomObjectSilent(kind, id);
  if (state.selected && state.selected.id === id) state.selected = null;
  renderAllPanels(); draw(); saveSoon();
}

function toggleVisibility(kind, id) {
  let obj = null;
  if (kind === 'fn') obj = state.functions.find(x => x.id === id);
  else if (kind === 'curve') obj = state.curve;
  else if (kind === 'shape') obj = getShape(id);
  else if (kind === 'point') obj = getPt(id);
  else if (kind === 'mark') obj = state.geom.marks.find(x => x.id === id);
  else if (kind === 'space') obj = state.space.points.find(x => x.id === id);
  if (!obj) return;
  pushHistory();
  if (kind === 'fn') obj.visible = !obj.visible;
  else if (kind === 'curve') obj.visible = obj.visible === false;
  else if (kind === 'shape' || kind === 'point' || kind === 'mark') obj.visible = !obj.visible;
  else if (kind === 'space') obj.visible = obj.visible === false;
  renderObjectList(); renderSelection(); draw(); saveSoon();
}

/* ---------- 指针事件 ---------- */

const CONSTRAINED_TRIANGLE_KINDS = ['isosceles-triangle', 'right-isosceles', 'equilateral'];
const CONSTRAINED_QUAD_KINDS = ['square', 'rectangle', 'parallelogram', 'rhombus'];

function constrainedTriangleForPoint(pointId) {
  const sel = state.selected;
  if (sel && sel.kind === 'shape') {
    const s = getShape(sel.id);
    if (s && s.type === 'triangle' && CONSTRAINED_TRIANGLE_KINDS.includes(s.kind) && s.points.includes(pointId)) return s;
  }
  const candidates = state.geom.shapes.filter(s => s.visible && s.type === 'triangle'
    && CONSTRAINED_TRIANGLE_KINDS.includes(s.kind) && s.points.includes(pointId));
  return candidates.length ? candidates[candidates.length - 1] : null;
}

function constrainedQuadForPoint(pointId) {
  const sel = state.selected;
  if (sel && sel.kind === 'shape') {
    const s = getShape(sel.id);
    if (s && s.type === 'quad' && CONSTRAINED_QUAD_KINDS.includes(s.kind) && s.points.includes(pointId)) return s;
  }
  const candidates = state.geom.shapes.filter(s => s.visible && s.type === 'quad'
    && CONSTRAINED_QUAD_KINDS.includes(s.kind) && s.points.includes(pointId));
  return candidates.length ? candidates[candidates.length - 1] : null;
}

function onPointerDown(e) {
  if (e.button !== 0) return;
  const sp = eventPos(e);
  canvas.setPointerCapture(e.pointerId);
  if (state.mode === 'space') {
    state.drag = { type: 'orbit', sx: sp.x, sy: sp.y, yaw: state.space.yaw, pitch: state.space.pitch, moved: false };
    return;
  }
  if (state.tangentPicking) {
    state.drag = { type: 'tangent-pick', sx: sp.x, sy: sp.y, moved: false };
    return;
  }
  if (state.tool === 'select') {
    const p = hitTestPoint(sp, 12);
    if (p) {
      const prevSel = state.selected;
      const ct = p.derived ? null : constrainedTriangleForPoint(p.id);
      const cq = p.derived ? null : constrainedQuadForPoint(p.id);
      const preferQuad = !!(cq && prevSel && prevSel.kind === 'shape' && prevSel.id === cq.id);
      state.selected = { kind: 'point', id: p.id };
      if (ct && !preferQuad) {
        const pts = shapePoints(ct);
        const others = pts.filter(q => q.id !== p.id);
        const anchor = mid(others[0], others[1]);
        state.drag = {
          type: 'constrained', shapeId: ct.id, pointId: p.id, sx: sp.x, sy: sp.y,
          anchor, orig: pts.map(q => ({ id: q.id, x: q.x, y: q.y })), moved: false, pushed: false
        };
      } else if (cq) {
        const pts = shapePoints(cq);
        const idx = cq.points.indexOf(p.id);
        const anchorPt = pts[(idx + 2) % 4];
        state.drag = {
          type: 'constrained-quad', shapeId: cq.id, pointId: p.id, sx: sp.x, sy: sp.y,
          anchor: { x: anchorPt.x, y: anchorPt.y },
          orig: pts.map(q => ({ id: q.id, x: q.x, y: q.y })), moved: false, pushed: false
        };
      } else {
        state.drag = p.derived
          ? { type: 'derived', id: p.id, sx: sp.x, sy: sp.y, moved: false }
          : {
            type: 'point', id: p.id, sx: sp.x, sy: sp.y,
            ox: p.x, oy: p.y, moved: false, pushed: false
          };
      }
      renderAllPanels(); draw();
      return;
    }
    const s = hitTestShape(sp);
    if (s) {
      state.selected = { kind: 'shape', id: s.id };
      const pts = shapePoints(s);
      const orig = {};
      pts.forEach(pt => { orig[pt.id] = { x: pt.x, y: pt.y }; });
      state.drag = {
        type: 'shape', id: s.id, sx: sp.x, sy: sp.y,
        orig, moved: false, pushed: false
      };
      renderAllPanels(); draw();
      return;
    }
    state.selected = null;
    state.drag = { type: 'pan', sx: sp.x, sy: sp.y, panX: state.view.panX, panY: state.view.panY, moved: false };
    renderAllPanels(); draw();
    return;
  }
  state.drag = { type: 'click', sx: sp.x, sy: sp.y, moved: false };
}

function onPointerMove(e) {
  const sp = eventPos(e);
  updateCoords(sp);
  if (!state.drag) {
    if (state.mode === 'space') return;
    if (state.tangentPicking) { canvas.style.cursor = 'crosshair'; return; }
    const hover = state.tool === 'select' ? (hitTestPoint(sp, 12) ? { kind: 'point', id: hitTestPoint(sp, 12).id } : (hitTestShape(sp) ? { kind: 'shape', id: hitTestShape(sp).id } : null))
      : state.tool === 'congruent' || state.tool === 'similar' ? (() => { const t = triangleAt(sp); return t ? { kind: 'shape', id: t.id } : null; })()
      : null;
    const changed = (hover && !state.hover) || (!hover && state.hover) || (hover && state.hover && (hover.kind !== state.hover.kind || hover.id !== state.hover.id));
    state.hover = hover;
    canvas.style.cursor = hover ? 'pointer' : state.tool === 'select' ? 'grab' : 'crosshair';
    if (['select', 'point', 'segment', 'ray', 'line', 'triangle', 'right-triangle', 'isosceles-triangle', 'right-isosceles', 'equilateral', 'square', 'rectangle', 'parallelogram', 'rhombus', 'circle', 'perp-bisector', 'angle-bisector', 'angle', 'set-alpha', 'midpoint'].includes(state.tool)) {
      state.preview = snapWorld(sp, e.altKey);
      draw();
    } else if (changed) draw();
    return;
  }
  const d = state.drag;
  if (d.type === 'tangent-pick') {
    if (Math.hypot(sp.x - d.sx, sp.y - d.sy) > 2) d.moved = true;
    return;
  }
  if (d.type === 'orbit') {
    state.space.yaw = d.yaw - (sp.x - d.sx) * .008;
    state.space.pitch = clamp(d.pitch + (sp.y - d.sy) * .006, -.05, 1.25);
    d.moved = true;
    draw(); saveSoon();
    return;
  }
  if (d.type === 'pan') {
    const dx = sp.x - d.sx, dy = sp.y - d.sy;
    if (Math.abs(dx) + Math.abs(dy) > 3) d.moved = true;
    state.view.panX = d.panX + dx;
    state.view.panY = d.panY + dy;
    draw();
    return;
  }
  if (d.type === 'constrained') {
    if (!d.moved && Math.hypot(sp.x - d.sx, sp.y - d.sy) > 2) {
      d.moved = true;
      if (!d.pushed) { pushHistory(); d.pushed = true; }
    }
    if (!d.moved) return;
    const shape = getShape(d.shapeId);
    const dragged = getPt(d.pointId);
    if (!shape || !dragged) return;
    let target = snapWorld(sp, e.altKey);
    if (target.pid === d.pointId) {
      const w = s2w(sp); target = { x: w.x, y: w.y, pid: null };
    }
    const oldPoint = d.orig.find(q => q.id === d.pointId);
    if (!oldPoint) return;
    const oldLen = Math.hypot(oldPoint.x - d.anchor.x, oldPoint.y - d.anchor.y);
    const newLen = Math.hypot(target.x - d.anchor.x, target.y - d.anchor.y);
    if (oldLen < 1e-6 || !Number.isFinite(newLen)) return;
    // 以对边中点为基准做位似缩放：保持所有角与边的比例，只改变大小
    const k = clamp(newLen / oldLen, 0.12, 20);
    for (const q of d.orig) {
      const p = getPt(q.id);
      if (!p) continue;
      p.x = d.anchor.x + (q.x - d.anchor.x) * k;
      p.y = d.anchor.y + (q.y - d.anchor.y) * k;
    }
    state.selected = { kind: 'shape', id: d.shapeId };
    state.preview = null;
    renderSelection(); draw(); saveSoon();
    return;
  }
  if (d.type === 'constrained-quad') {
    if (!d.moved && Math.hypot(sp.x - d.sx, sp.y - d.sy) > 2) {
      d.moved = true;
      if (!d.pushed) { pushHistory(); d.pushed = true; }
    }
    if (!d.moved) return;
    const shape = getShape(d.shapeId);
    const dragged = getPt(d.pointId);
    if (!shape || !dragged) return;
    let target = snapWorld(sp, e.altKey);
    if (target.pid === d.pointId) {
      const w = s2w(sp); target = { x: w.x, y: w.y, pid: null };
    }
    const oldPoint = d.orig.find(q => q.id === d.pointId);
    if (!oldPoint) return;
    const oldLen = Math.hypot(oldPoint.x - d.anchor.x, oldPoint.y - d.anchor.y);
    const newLen = Math.hypot(target.x - d.anchor.x, target.y - d.anchor.y);
    if (oldLen < 1e-6 || !Number.isFinite(newLen)) return;
    // 以对角顶点为位似中心：正方形/矩形/平行四边形/菱形保持形状，只改变大小
    const k = clamp(newLen / oldLen, 0.1, 20);
    for (const q of d.orig) {
      const p = getPt(q.id);
      if (!p) continue;
      p.x = d.anchor.x + (q.x - d.anchor.x) * k;
      p.y = d.anchor.y + (q.y - d.anchor.y) * k;
    }
    state.selected = { kind: 'shape', id: d.shapeId };
    state.preview = null;
    renderSelection(); draw(); saveSoon();
    return;
  }
  if (d.type === 'point') {
    const p = getPt(d.id);
    if (!p) return;
    if (!d.moved && Math.hypot(sp.x - d.sx, sp.y - d.sy) > 2) {
      d.moved = true;
      if (!d.pushed) { pushHistory(); d.pushed = true; }
    }
    if (!d.moved) return;
    const target = snapWorld(sp, e.altKey);
    p.x = target.x; p.y = target.y;
    state.preview = null;
    renderSelection(); draw(); saveSoon();
    return;
  }
  if (d.type === 'shape') {
    if (!d.moved && Math.hypot(sp.x - d.sx, sp.y - d.sy) > 2) {
      d.moved = true;
      if (!d.pushed) { pushHistory(); d.pushed = true; }
    }
    if (!d.moved) return;
    const start = s2w({ x: d.sx, y: d.sy });
    const now = s2w(sp);
    const dx = now.x - start.x, dy = now.y - start.y;
    for (const pid in d.orig) {
      const p = getPt(pid);
      if (!p) continue;
      if (state.geom.snap && !e.altKey) {
        p.x = Math.round((d.orig[pid].x + dx) * 2) / 2;
        p.y = Math.round((d.orig[pid].y + dy) * 2) / 2;
      } else {
        p.x = d.orig[pid].x + dx;
        p.y = d.orig[pid].y + dy;
      }
    }
    renderSelection(); draw(); saveSoon();
    return;
  }
  if (d.type === 'click') {
    if (Math.hypot(sp.x - d.sx, sp.y - d.sy) > 6) d.moved = true;
    state.preview = snapWorld(sp, e.altKey);
    draw();
  }
}

function onPointerUp(e) {
  const sp = eventPos(e);
  const d = state.drag;
  state.drag = null;
  if (!d) return;
  if (d.type === 'tangent-pick') {
    if (!d.moved) computeCircleTangent(s2w(sp));
    state.tangentPicking = false;
    canvas.style.cursor = 'grab';
    updateTangentUI(); saveSoon(); draw();
    return;
  }
  if (d.type === 'pan' && !d.moved) {
    state.selected = null; renderAllPanels(); draw();
  }
  if (d.type === 'click' && !d.moved) {
    handleToolClick(sp);
  }
  if (['orbit', 'pan', 'point', 'shape', 'constrained', 'constrained-quad'].includes(d.type)) saveSoon();
  if (['point', 'shape', 'constrained', 'constrained-quad'].includes(d.type)) updateTransformUI();
  updateToolbarVisibility();
  draw();
}

function onWheel(e) {
  e.preventDefault();
  if (state.mode === 'space') {
    state.space.zoom = clamp(state.space.zoom * (e.deltaY < 0 ? 1.1 : .91), .35, 5);
    updateZoomLabel(); draw(); saveSoon();
    return;
  }
  zoomAt(e.offsetX, e.offsetY, e.deltaY < 0 ? 1.12 : .89);
  saveSoon();
}

function updateCoords(sp) {
  const el = $('#coordReadout');
  if (!el) return;
  if (state.mode === 'space') {
    el.textContent = '拖动旋转 · 滚轮缩放';
    return;
  }
  const p = s2w(sp);
  el.innerHTML = `x = ${fmt(p.x, 2)} &nbsp;·&nbsp; y = ${fmt(p.y, 2)}`;
}

/* ============================================================
   示例 / 清空 / 导出
   ============================================================ */

function clearGeometry(silent = false) {
  if (!state.geom.points.length && !state.geom.shapes.length && !state.geom.marks.length) {
    if (!silent) toast('画布上还没有几何图形');
    return;
  }
  if (!silent) pushHistory();
  state.geom.points = [];
  state.geom.shapes = [];
  state.geom.marks = [];
  state.geom.transforms = [];
  state.geom.alpha = null;
  state.geom.nextLabel = 0;
  state.selected = null;
  state.pending = []; state.markFirst = null; state.transformTarget = null; state.preview = null;
  updateTransformUI(); renderAllPanels(); draw(); saveSoon();
  if (!silent) toast('已清空几何作图（可撤销）');
}

function loadDemo(kind) {
  if (state.mode === 'space') setMode('plane');
  if (state.tab !== 'geometry') setTab('geometry');
  pushHistory();
  clearGeometry(true);
  const add = (x, y) => makePoint(x, y);
  if (kind === 'congruent') {
    const A = add(-5.5, -1), B = add(-2, -1), C = add(-5.5, 2.5);
    const D = add(1, -1), E = add(4.5, -1), F = add(1, 2.5);
    createTriangle('right-isosceles', A, B, C);
    createTriangle('right-isosceles', D, E, F);
    const t1 = state.geom.shapes[0], t2 = state.geom.shapes[1];
    addRelationMark('congruent', t1, t2);
    fitAll();
    toast('全等示例：两个等腰直角三角形，对应边与对应角用相同记号标出。', 'ok');
  } else {
    const A = add(-5.5, -2), B = add(-2.5, -2), C = add(-5.5, 1);
    const D = add(1, -1.5), E = add(3.5, -1.5), F = add(1, 1);
    createTriangle('right-isosceles', A, B, C);
    createTriangle('right-isosceles', D, E, F);
    const t1 = state.geom.shapes[0], t2 = state.geom.shapes[1];
    addRelationMark('similar', t1, t2);
    fitAll();
    toast('相似示例：两个相似三角形，三个对应角用相同角弧标出。', 'ok');
  }
  renderAllPanels(); draw(); saveSoon();
}

function exportPNG() {
  draw();
  canvas.toBlob(blob => {
    if (!blob) { toast('导出失败，请重试', 'bad'); return; }
    const a = document.createElement('a');
    const d = new Date();
    const stamp = `${d.getFullYear()}${String(d.getMonth() + 1).padStart(2, '0')}${String(d.getDate()).padStart(2, '0')}-${String(d.getHours()).padStart(2, '0')}${String(d.getMinutes()).padStart(2, '0')}`;
    a.href = URL.createObjectURL(blob);
    a.download = `函数与几何-${stamp}.png`;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 2000);
    toast('已导出当前画布 PNG', 'ok');
  }, 'image/png');
}

function copyText(text) {
  if (navigator.clipboard && window.isSecureContext) {
    navigator.clipboard.writeText(text).then(() => toast('已复制到剪贴板', 'ok')).catch(() => fallbackCopy(text));
  } else fallbackCopy(text);
}
function fallbackCopy(text) {
  const ta = document.createElement('textarea');
  ta.value = text; ta.style.position = 'fixed'; ta.style.opacity = '0';
  document.body.appendChild(ta); ta.select();
  try { document.execCommand('copy'); toast('已复制到剪贴板', 'ok'); }
  catch { toast('复制失败，请手动选择', 'warn'); }
  ta.remove();
}

/* ============================================================
   持久化
   ============================================================ */

/* ============================================================
   图片识别：OCR + 文本解析
   ============================================================ */

const TESSERACT_CDN = 'https://cdn.jsdelivr.net/npm/tesseract.js@5.1.1/dist/tesseract.min.js';
let ocrFile = null;
let ocrPreviewUrl = null;
let ocrEnginePromise = null;

function openOcr() {
  const modal = $('#ocrModal');
  if (!modal) return;
  modal.hidden = false;
  document.body.classList.add('modal-open');
  setTimeout(() => {
    const t = $('#ocrText');
    if (t && !t.value.trim()) t.focus();
  }, 50);
}
function closeOcr() {
  const modal = $('#ocrModal');
  if (!modal) return;
  modal.hidden = true;
  document.body.classList.remove('modal-open');
}
function setOcrStatus(text, kind = '') {
  const el = $('#ocrStatus');
  if (!el) return;
  el.textContent = text;
  el.classList.remove('ok', 'bad');
  if (kind) el.classList.add(kind);
}
function setOcrProgress(v) {
  const bar = $('#ocrProgress');
  if (!bar) return;
  const on = v !== null && v !== undefined;
  bar.classList.toggle('on', on);
  const i = bar.querySelector('i');
  if (i) i.style.width = on ? `${clamp(v, 0, 1) * 100}%` : '0';
}
function setOcrFile(file) {
  if (!file) return;
  if (!/^image\//.test(file.type)) { toast('请选择图片文件', 'warn'); return; }
  if (file.size > 12 * 1024 * 1024) { toast('图片建议小于 12 MB', 'warn'); return; }
  ocrFile = file;
  if (ocrPreviewUrl) URL.revokeObjectURL(ocrPreviewUrl);
  ocrPreviewUrl = URL.createObjectURL(file);
  const img = $('#ocrPreview'), prompt = $('#ocrDropPrompt'), name = $('#ocrFileName');
  if (img) { img.src = ocrPreviewUrl; img.hidden = false; }
  if (prompt) prompt.hidden = true;
  if (name) name.textContent = `${file.name} · ${(file.size / 1024).toFixed(0)} KB`;
  const ta = $('#ocrText');
  if (ta) ta.value = '';
  setOcrStatus('图片已载入。点击「开始识别」，或直接在右侧编辑文字。');
  setOcrProgress(null);
}

function loadTesseract() {
  if (window.Tesseract) return Promise.resolve(window.Tesseract);
  if (ocrEnginePromise) return ocrEnginePromise;
  ocrEnginePromise = new Promise((resolve, reject) => {
    const s = document.createElement('script');
    s.src = TESSERACT_CDN;
    s.async = true;
    s.onload = () => window.Tesseract ? resolve(window.Tesseract) : reject(new Error('OCR 引擎未初始化'));
    s.onerror = () => { ocrEnginePromise = null; reject(new Error('无法加载 OCR 引擎')); };
    document.head.appendChild(s);
  });
  return ocrEnginePromise;
}

async function runOcr() {
  if (!ocrFile) { toast('请先选择一张图片', 'warn'); setOcrStatus('请先选择图片。'); return; }
  const btn = $('#ocrRun');
  if (btn) { btn.disabled = true; btn.textContent = '识别中…'; }
  setOcrStatus('正在加载 OCR 引擎（首次约 10–60 秒）…');
  setOcrProgress(0.02);
  let worker = null;
  try {
    const Tesseract = await loadTesseract();
    const lang = $('#ocrLang') ? $('#ocrLang').value : 'chi_sim+eng';
    setOcrStatus('正在初始化识别语言…');
    worker = await Tesseract.createWorker(lang, 1, {
      logger: m => {
        if (!m) return;
        if (m.status === 'recognizing text') {
          setOcrProgress(m.progress || 0);
          setOcrStatus(`正在识别文字… ${Math.round((m.progress || 0) * 100)}%`);
        } else if (m.status) {
          setOcrStatus(`识别引擎：${m.status}…`);
        }
      }
    });
    setOcrStatus('正在识别图片文字…');
    const { data } = await worker.recognize(ocrFile);
    const text = normalizeOcrText((data && data.text ? data.text : '').trim());
    const ta = $('#ocrText');
    if (ta) ta.value = text;
    if (text) {
      setOcrStatus('识别完成。请在右侧核对文字，再点击「从文字生成」。', 'ok');
      setOcrProgress(1);
    } else {
      setOcrStatus('没有识别到文字。可以换一张更清晰的图片，或直接手动输入。', 'bad');
      setOcrProgress(null);
    }
  } catch (err) {
    setOcrStatus('OCR 失败：' + (err && err.message ? err.message : '引擎不可用') + '。可直接把题目文字粘贴到右侧生成。', 'bad');
    setOcrProgress(null);
  } finally {
    if (worker) { try { await worker.terminate(); } catch { /* ignore */ } }
    if (btn) { btn.disabled = false; btn.textContent = '开始识别'; }
  }
}

function normalizeOcrText(text) {
  return String(text || '')
    .replace(/\r\n?/g, '\n')
    .replace(/[\uFF10-\uFF19]/g, c => String.fromCharCode(c.charCodeAt(0) - 0xFEE0))
    .replace(/[\uFF21-\uFF3A\uFF41-\uFF5A]/g, c => String.fromCharCode(c.charCodeAt(0) - 0xFEE0))
    .replace(/[−–—﹣]/g, '-')
    .replace(/[×·・]/g, '*')
    .replace(/÷/g, '/')
    .replace(/([a-zA-Z0-9)])\s*["“”'′]\s*(\d+)/g, '$1^$2')
    .replace(/[²]/g, '^2').replace(/[³]/g, '^3').replace(/[⁴]/g, '^4')
    .replace(/[⁵]/g, '^5').replace(/[⁶]/g, '^6')
    .replace(/π/g, 'pi')
    .replace(/[，]/g, ',')
    .replace(/[：]/g, ':')
    .replace(/[；]/g, ';')
    .replace(/\u3000/g, ' ');
}

function normalizeMathExpr(raw) {
  let s = String(raw || '')
    .replace(/[。；;]+$/g, '')
    .replace(/[，,]\s*[^0-9a-zA-Z+\-*/^().]+$/g, '')
    .replace(/√\s*\(([^)]+)\)/g, 'sqrt($1)')
    .replace(/√\s*([a-zA-Z0-9.]+)/g, 'sqrt($1)')
    .replace(/\b(sin|cos|tan|ln|log|sqrt|abs|exp)\s*([a-zA-Z0-9.]+)/gi, '$1($2)')
    .replace(/[^0-9a-zA-Z+\-*/^().,\s]/g, '')
    .replace(/\s+/g, '');
  return s;
}

function ocrExtractFunctions(text) {
  const found = [];
  const chunks = String(text || '').split(/\n|;/);
  for (let raw of chunks) {
    let line = raw.trim()
      .replace(/^[\s（(]*[0-9①-⑳]+[.、)）]?\s*/, '')
      .replace(/^函数\s*[:：]?\s*/, '');
    if (!line) continue;
    const m = line.match(/^(?:y|f\s*\(\s*x\s*\))\s*[:=]\s*(.+)$/i);
    if (!m) continue;
    let expr = normalizeMathExpr(m[1]);
    if (!expr) continue;
    try {
      parseExpression(expr);
      if (!found.some(f => f.replace(/\s+/g, '') === expr)) found.push(expr);
    } catch { /* 忽略无法解析的行 */ }
  }
  return found;
}

const OCR_SHAPE_DEFS = [
  { word: '等腰直角三角形', type: 'triangle', kind: 'right-isosceles', n: 3 },
  { word: '等边三角形', type: 'triangle', kind: 'equilateral', n: 3 },
  { word: '等腰三角形', type: 'triangle', kind: 'isosceles-triangle', n: 3 },
  { word: '直角三角形', type: 'triangle', kind: 'right-triangle', n: 3 },
  { word: '三角形', type: 'triangle', kind: 'triangle', n: 3 },
  { word: '正方形', type: 'quad', kind: 'square', n: 4 },
  { word: '平行四边形', type: 'quad', kind: 'parallelogram', n: 4 },
  { word: '长方形', type: 'quad', kind: 'rectangle', n: 4 },
  { word: '矩形', type: 'quad', kind: 'rectangle', n: 4 },
  { word: '菱形', type: 'quad', kind: 'rhombus', n: 4 }
];

function ocrExtractGeometry(text) {
  const points = new Map();
  const shapes = [];
  const seen = new Set();
  const pointRe = /([A-Za-z])\s*[（(]\s*(-?\d+(?:\.\d+)?)\s*[,，]\s*(-?\d+(?:\.\d+)?)\s*[)）]/g;
  let pm;
  while ((pm = pointRe.exec(text))) {
    points.set(pm[1].toUpperCase(), { x: parseFloat(pm[2]), y: parseFloat(pm[3]) });
  }

  const lines = String(text || '').split(/\n/);
  for (const raw of lines) {
    const line = raw.replace(/\s+/g, '');
    if (!line) continue;

    for (const def of OCR_SHAPE_DEFS) {
      const re = new RegExp(def.word + '\\s*[:：]?\\s*([A-Z]{' + def.n + '})');
      const m = line.match(re);
      if (m) {
        const labels = m[1].split('');
        const key = def.kind + ':' + labels.join('');
        if (!seen.has(key)) {
          seen.add(key);
          shapes.push({ type: def.type, kind: def.kind, labels });
        }
        break;
      }
    }

    const seg = line.match(/(线段|射线|直线)\s*([A-Z]{2})/);
    if (seg) {
      const type = seg[1] === '线段' ? 'segment' : seg[1] === '射线' ? 'ray' : 'line';
      const labels = seg[2].split('');
      const key = type + ':' + labels.join('');
      if (!seen.has(key)) { seen.add(key); shapes.push({ type, kind: '', labels }); }
    }

    const perp = line.match(/垂直平分线\s*([A-Z]{2})/);
    if (perp) {
      const labels = perp[1].split('');
      const key = 'perp:' + labels.join('');
      if (!seen.has(key)) { seen.add(key); shapes.push({ type: 'perp-bisector', kind: '', labels }); }
    }

    const circle = line.match(/圆(?:心)?\s*([A-Z])/);
    if (circle) {
      const radius = line.match(/半径\s*(?:为|=|:)?\s*(\d+(?:\.\d+)?)/);
      const key = 'circle:' + circle[1];
      if (!seen.has(key)) {
        seen.add(key);
        shapes.push({ type: 'circle', kind: '', center: circle[1], r: radius ? parseFloat(radius[1]) : 2 });
      }
    }
  }
  return { points, shapes };
}

function ocrAutoLabel() {
  const used = usedPointLabels();
  for (const c of 'ABCDEFGHIJKLMNOPQRSTUVWXYZ') if (!used.has(c)) return c;
  return nextLabel();
}

function ocrApplyData(text, replace) {
  const normalized = normalizeOcrText(text);
  const functions = ocrExtractFunctions(normalized);
  const geo = ocrExtractGeometry(normalized);
  if (!functions.length && !geo.shapes.length && !geo.points.size) {
    setOcrStatus('没有识别到可生成的函数或几何图形。可以按示例格式修改文字后重试。', 'bad');
    toast('没有识别到可生成的内容', 'warn');
    return false;
  }

  pushHistory();
  if (replace) {
    state.functions = [];
    state.activeFnId = null;
    state.calc = null;
    clearGeometry(true);
  }

  // 函数
  let addedFns = 0;
  for (const expr of functions) {
    if (state.functions.some(f => f.expr.replace(/\s+/g, '') === expr)) continue;
    let ast;
    try { ast = parseExpression(expr); } catch { continue; }
    if (state.functions.length >= 6) {
      const removed = state.functions.shift();
      if (state.activeFnId === removed.id) state.activeFnId = null;
    }
    const fn = { id: uid('f'), expr, ast, color: fnColor(state.functions.length), visible: true };
    state.functions.push(fn);
    state.activeFnId = fn.id;
    addedFns++;
  }
  state.calc = null;
  resetCalcHints();
  if (addedFns) {
    const input = $('#exprInput');
    const active = activeFn();
    if (input && active) input.value = active.expr;
  }

  // 坐标点
  const pointsBefore = state.geom.points.length;
  for (const [label, co] of geo.points) {
    if (state.geom.points.some(p => p.label === label)) continue;
    makePoint(co.x, co.y, label);
  }
  const addedPoints = state.geom.points.length - pointsBefore;

  const find = label => state.geom.points.find(p => p.label === label) || null;
  let slot = 0;
  const nextSlot = () => {
    const x = -10 + (slot % 3) * 9;
    const y = 8 - Math.floor(slot / 3) * 7;
    slot++;
    return { x, y };
  };
  const ensure = (label, x, y) => find(label) || makePoint(x, y, label);

  let addedShapes = 0;
  for (const def of geo.shapes) {
    if (def.type === 'circle') {
      const center = find(def.center) || ensure(def.center, nextSlot().x, 0);
      const r = Math.max(0.2, def.r || 2);
      let through = state.geom.points.find(p => Math.abs(dist(center, p) - r) < 1e-9 && p.id !== center.id);
      if (!through) {
        const label = ocrAutoLabel();
        through = makePoint(center.x + r, center.y, label);
      }
      addShape('circle', [center, through]);
      addedShapes++;
      continue;
    }

    const labels = def.labels;
    if (def.type === 'triangle') {
      let pts = labels.map(find);
      if (!pts.every(Boolean)) {
        const loc = nextSlot();
        let A = pts[0] || makePoint(loc.x, loc.y, labels[0]);
        let B = pts[1] || makePoint(loc.x + 4, loc.y, labels[1]);
        let pos;
        if (def.kind !== 'triangle') pos = autoTrianglePoints(A, B, def.kind);
        if (!pos) pos = [A, B, { x: A.x + 2.5, y: A.y + 3.5 }];
        let C = pts[2] || makePoint(pos[2].x, pos[2].y, labels[2]);
        pts = [A, B, C];
      }
      if (new Set(pts.map(p => p.id)).size === 3) { addShape('triangle', pts, def.kind); addedShapes++; }
      continue;
    }

    if (def.type === 'quad') {
      let pts = labels.map(find);
      if (!pts.every(Boolean)) {
        const loc = nextSlot();
        let A = pts[0] || makePoint(loc.x, loc.y, labels[0]);
        let B = pts[1] || makePoint(loc.x + 4, loc.y, labels[1]);
        const pos = autoQuadPoints(A, B, def.kind) || [
          A, B, { x: B.x, y: B.y + 3 }, { x: A.x, y: A.y + 3 }
        ];
        pts = [A, B, pts[2] || makePoint(pos[2].x, pos[2].y, labels[2]), pts[3] || makePoint(pos[3].x, pos[3].y, labels[3])];
      }
      if (new Set(pts.map(p => p.id)).size === 4) { addShape('quad', pts, def.kind); addedShapes++; }
      continue;
    }

    if (def.type === 'segment' || def.type === 'ray' || def.type === 'line' || def.type === 'perp-bisector') {
      let pts = labels.map(find);
      if (!pts.every(Boolean)) {
        const loc = nextSlot();
        pts = [pts[0] || makePoint(loc.x, loc.y, labels[0]), pts[1] || makePoint(loc.x + 4, loc.y, labels[1])];
      }
      if (new Set(pts.map(p => p.id)).size === 2) { addShape(def.type, pts); addedShapes++; }
    }
  }

  if (state.mode === 'space') setMode('plane');
  if (addedShapes) {
    setTab('geometry');
    state.selected = null;
    fitAll();
  } else if (addedFns) {
    setTab('function');
  } else if (addedPoints) {
    setTab('geometry');
    state.selected = null;
    fitAll();
  }
  renderAllPanels(); draw(); saveSoon();
  closeOcr();
  const bits = [];
  if (addedFns) bits.push(`${addedFns} 条函数`);
  if (addedShapes) bits.push(`${addedShapes} 个几何图形`);
  if (addedPoints) bits.push(`${addedPoints} 个坐标点`);
  if (!bits.length) bits.push('没有新增对象');
  toast('已从文字生成：' + bits.join('、'), 'ok');
  return true;
}

function fillOcrExample() {
  const ta = $('#ocrText');
  if (!ta) return;
  ta.value = [
    'y = x^2 - 2x + 1',
    'y = sin(x)',
    '等腰三角形 ABC',
    'A(-5, -2) B(1, -2) C(-2, 4)',
    '圆 O 半径 2',
    'O(5, 2)'
  ].join('\n');
  setOcrStatus('示例文字已填入，可直接点击「从文字生成」。');
}

const STORAGE_KEY = 'fg-studio-v1';
let booted = false;

function syncUidCounter() {
  const ids = [];
  state.functions.forEach(f => ids.push(f.id));
  state.geom.points.forEach(p => ids.push(p.id));
  state.geom.shapes.forEach(s => ids.push(s.id));
  state.geom.marks.forEach(m => ids.push(m.id));
  (state.geom.transforms || []).forEach(t => ids.push(t.id));
  state.space.points.forEach(p => ids.push(p.id));
  let max = 0;
  for (const id of ids) {
    const m = /_(\d+)$/.exec(String(id || ''));
    if (m) max = Math.max(max, parseInt(m[1], 10));
  }
  uidCounter = Math.max(uidCounter, max + 1);
}

function saveSoon() {
  if (!booted) return;
  clearTimeout(state.saveTimer);
  state.saveTimer = setTimeout(saveState, 400);
}
function saveState() {
  if (!booted) return;
  try {
    const data = {
      v: 1,
      mode: state.mode,
      tab: state.tab,
      functions: state.functions.map(f => ({ id: f.id, expr: f.expr, color: f.color, visible: f.visible })),
      activeFnId: state.activeFnId,
      curve: state.curve,
      conicResult: state.conicResult,
      conicType: state.conicType,
      conicParams: state.conicParams,
      circleTangent: state.circleTangent,
      calc: state.calc,
      rotateExpr: state.rotateExpr,
      keepOriginal: state.keepOriginal,
      geom: state.geom,
      space: {
        yaw: state.space.yaw, pitch: state.space.pitch, zoom: state.space.zoom,
        panX: state.space.panX, panY: state.space.panY,
        points: state.space.points, nextLabel: state.space.nextLabel || 0
      }
    };
    localStorage.setItem(STORAGE_KEY, JSON.stringify(data));
  } catch (err) {
    // 存储空间不足或被禁用时静默失败，不影响使用
  }
}

function restoreState() {
  let data;
  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    if (!raw) return false;
    data = JSON.parse(raw);
  } catch { return false; }
  if (!data || typeof data !== 'object') return false;
  try {
    if (['plane', 'space', 'blank'].includes(data.mode)) state.mode = data.mode;
    if (['function', 'conic', 'geometry'].includes(data.tab)) state.tab = data.tab;
    if (['circle', 'ellipse', 'parabola', 'hyperbola'].includes(data.conicType)) state.conicType = data.conicType;
    if (data.conicParams && typeof data.conicParams === 'object') {
      for (const k of Object.keys(state.conicParams)) {
        if (data.conicParams[k]) state.conicParams[k] = Object.assign(state.conicParams[k], data.conicParams[k]);
      }
    }
    const fns = [];
    for (const f of (data.functions || [])) {
      if (!f || typeof f.expr !== 'string') continue;
      try {
        const ast = parseExpression(f.expr);
        fns.push({ id: f.id || uid('f'), expr: f.expr, ast, color: f.color || fnColor(fns.length), visible: f.visible !== false });
      } catch { /* 忽略损坏的旧表达式 */ }
    }
    state.functions = fns;
    state.activeFnId = fns.some(f => f.id === data.activeFnId) ? data.activeFnId : (fns[0] ? fns[0].id : null);
    if (data.curve && data.curve.kind) state.curve = data.curve;
    if (data.conicResult && data.conicResult.kind) state.conicResult = data.conicResult;
    if (data.circleTangent && Array.isArray(data.circleTangent.lines)) state.circleTangent = data.circleTangent;
    if (data.calc && typeof data.calc === 'object') state.calc = data.calc;
    if (typeof data.rotateExpr === 'string' && data.rotateExpr.trim()) state.rotateExpr = data.rotateExpr;
    if (typeof data.keepOriginal === 'boolean') state.keepOriginal = data.keepOriginal;
    if (data.geom && Array.isArray(data.geom.points)) {
      state.geom = Object.assign({ points: [], shapes: [], marks: [], transforms: [], alpha: null, nextLabel: 0, snap: true, showLabels: true, horizontalBase: true }, data.geom);
      if (!Array.isArray(state.geom.shapes)) state.geom.shapes = [];
      if (!Array.isArray(state.geom.marks)) state.geom.marks = [];
      if (!Array.isArray(state.geom.transforms)) state.geom.transforms = [];
      if (!state.geom.alpha || typeof state.geom.alpha !== 'object') state.geom.alpha = null;
      state.geom.snap = data.geom.snap !== false;
      state.geom.showLabels = data.geom.showLabels !== false;
      state.geom.horizontalBase = data.geom.horizontalBase !== false;
      if (typeof state.geom.nextLabel !== 'number') state.geom.nextLabel = state.geom.points.length;
      syncDerivedPoints();
    }
    if (data.space && Array.isArray(data.space.points)) {
      state.space.points = data.space.points.filter(p => Number.isFinite(p.x) && Number.isFinite(p.y) && Number.isFinite(p.z));
      state.space.yaw = Number.isFinite(data.space.yaw) ? data.space.yaw : state.space.yaw;
      state.space.pitch = Number.isFinite(data.space.pitch) ? data.space.pitch : state.space.pitch;
      state.space.zoom = Number.isFinite(data.space.zoom) ? data.space.zoom : 1;
      state.space.panX = Number.isFinite(data.space.panX) ? data.space.panX : 0;
      state.space.panY = Number.isFinite(data.space.panY) ? data.space.panY : 0;
      state.space.nextLabel = Number.isFinite(data.space.nextLabel) ? data.space.nextLabel : state.space.points.length;
    }
    return true;
  } catch (err) {
    return false;
  }
}

function seedDefaultFunction() {
  const expr = 'x^2 - 2x - 1';
  try {
    const ast = parseExpression(expr);
    const fn = { id: uid('f'), expr, ast, color: PALETTE[0], visible: true };
    state.functions = [fn];
    state.activeFnId = fn.id;
  } catch { /* 理论不会失败 */ }
}

/* ============================================================
   事件绑定与启动
   ============================================================ */

function bindUI() {
  $$('.mode-btn').forEach(b => b.addEventListener('click', () => setMode(b.dataset.mode)));
  $$('.tab').forEach(b => b.addEventListener('click', () => setTab(b.dataset.tab)));

  $('#plotBtn').addEventListener('click', addFunctionFromInput);
  $('#exprInput').addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); addFunctionFromInput(); } });
  $$('#exampleChips .chip').forEach(b => b.addEventListener('click', () => {
    $('#exprInput').value = b.dataset.expr;
    addFunctionFromInput();
  }));
  $('#derivBtn').addEventListener('click', computeDerivative);
  $('#x0Input').addEventListener('keydown', e => { if (e.key === 'Enter') computeDerivative(); });
  $('#integralBtn').addEventListener('click', computeIntegral);
  $('#aInput').addEventListener('keydown', e => { if (e.key === 'Enter') computeIntegral(); });
  $('#bInput').addEventListener('keydown', e => { if (e.key === 'Enter') computeIntegral(); });
  ['showTangent', 'showDerivative', 'showArea'].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.addEventListener('change', () => { draw(); saveSoon(); });
  });
  $$('.conic-type').forEach(b => b.addEventListener('click', () => {
    state.conicType = b.dataset.conic;
    $$('.conic-type').forEach(x => x.classList.toggle('active', x.dataset.conic === state.conicType));
    renderConicFields();
    saveSoon();
  }));
  $('#conicBtn').addEventListener('click', generateConic);
  $('#circleEqBtn').addEventListener('click', () => {
    const input = $('#circleEqInput');
    if (input) applyCircleEquation(input.value);
  });
  $('#circleEqInput').addEventListener('keydown', e => {
    if (e.key === 'Enter') {
      e.preventDefault();
      applyCircleEquation(e.target.value);
    }
  });
  $('#tangentDraw').addEventListener('click', () => {
    const x = parseFloat($('#tangentX').value), y = parseFloat($('#tangentY').value);
    if (!Number.isFinite(x) || !Number.isFinite(y)) { toast('请输入有效的切点坐标', 'warn'); return; }
    computeCircleTangent({ x, y });
  });
  $('#tangentPick').addEventListener('click', () => {
    if (!state.curve || state.curve.kind !== 'circle') { toast('请先生成一个圆', 'warn'); return; }
    state.tangentPicking = !state.tangentPicking;
    if (state.tangentPicking) {
      if (state.mode === 'space') setMode('plane');
      if (state.tab !== 'conic') setTab('conic');
      canvas.style.cursor = 'crosshair';
      toast('在画布上点击圆上一点或圆外一点。', '');
    } else {
      canvas.style.cursor = 'grab';
    }
    updateTangentUI(); draw();
  });

  $$('.tool').forEach(b => b.addEventListener('click', () => setTool(b.dataset.tool)));
  $('#rotateExpr').addEventListener('input', e => {
    state.rotateExpr = e.target.value;
    updateTransformUI();
    saveSoon();
  });
  $$('.angle-chip').forEach(b => b.addEventListener('click', () => {
    state.rotateExpr = b.dataset.angle;
    $('#rotateExpr').value = state.rotateExpr;
    updateTransformUI();
    saveSoon();
  }));
  $('#keepOriginal').addEventListener('change', e => {
    state.keepOriginal = e.target.checked;
    updateHint();
    saveSoon();
  });
  $('#setAlphaBtn').addEventListener('click', () => setTool('set-alpha'));
  $('#clearAlpha').addEventListener('click', () => {
    if (!state.geom.alpha) return;
    pushHistory();
    state.geom.alpha = null;
    updateTransformUI(); renderAllPanels(); draw(); saveSoon();
    toast('已清除 α 引用', '');
  });
  $('#snapToggle').addEventListener('change', e => { state.geom.snap = e.target.checked; saveSoon(); });
  $('#labelToggle').addEventListener('change', e => { state.geom.showLabels = e.target.checked; draw(); saveSoon(); });
  $('#horizontalBase').addEventListener('change', e => { state.geom.horizontalBase = e.target.checked; updateHint(); draw(); saveSoon(); });
  $('#demoCongruent').addEventListener('click', () => loadDemo('congruent'));
  $('#demoSimilar').addEventListener('click', () => loadDemo('similar'));
  $('#clearGeom').addEventListener('click', () => clearGeometry(false));

  $('#objectList').addEventListener('click', e => {
    const item = e.target.closest('.obj-item');
    if (!item) return;
    const kind = item.dataset.kind, id = item.dataset.id;
    const act = e.target.closest('button[data-act]');
    if (act) {
      e.stopPropagation();
      if (act.dataset.act === 'vis') toggleVisibility(kind, id);
      else deleteObject(kind, id);
      return;
    }
    if (kind === 'fn') selectFunction(id);
    else if (kind === 'shape' || kind === 'point' || kind === 'mark') {
      state.selected = { kind, id };
      renderAllPanels(); draw();
    }
  });

  $('#analysisBox').addEventListener('click', e => {
    const b = e.target.closest('[data-copy]');
    if (b) copyText(b.dataset.copy);
  });

  $('#selectionBox').addEventListener('click', e => {
    const preset = e.target.closest('[data-apex-angle]');
    if (preset) { applyApexFromUI(parseFloat(preset.dataset.apexAngle)); return; }
    if (e.target.closest('#applyApex')) { applyApexFromUI(); return; }
    const qpreset = e.target.closest('[data-quad-angle]');
    if (qpreset) { applyQuadFromUI(parseFloat(qpreset.dataset.quadAngle)); return; }
    if (e.target.closest('#applyQuadAngle')) { applyQuadFromUI(); return; }
  });
  $('#selectionBox').addEventListener('keydown', e => {
    if (!e.target) return;
    if (e.target.id === 'apexAngleInput' && e.key === 'Enter') {
      e.preventDefault();
      applyApexFromUI();
    } else if (e.target.id === 'quadAngleInput' && e.key === 'Enter') {
      e.preventDefault();
      applyQuadFromUI();
    }
  });

  $('#addSpacePoint').addEventListener('click', addSpacePoint);
  ['sx', 'sy', 'sz'].forEach(id => $(`#${id}`).addEventListener('keydown', e => { if (e.key === 'Enter') addSpacePoint(); }));
  $('#spacePointList').addEventListener('click', e => {
    const b = e.target.closest('[data-space-del]');
    if (b) removeSpacePoint(b.dataset.spaceDel);
  });
  $('#clearSpace').addEventListener('click', () => {
    if (!state.space.points.length) return;
    pushHistory();
    state.space.points = []; state.space.nextLabel = 0;
    renderSpacePointList(); renderObjectList(); draw(); saveSoon();
  });

  canvas.addEventListener('pointerdown', onPointerDown);
  canvas.addEventListener('pointermove', onPointerMove);
  canvas.addEventListener('pointerup', onPointerUp);
  canvas.addEventListener('pointercancel', () => { state.drag = null; });
  canvas.addEventListener('pointerleave', () => {
    if (state.drag) return;
    state.hover = null; state.preview = null; draw();
  });
  canvas.addEventListener('wheel', onWheel, { passive: false });
  canvas.addEventListener('contextmenu', e => { e.preventDefault(); cancelPending(); });
  canvas.addEventListener('dblclick', e => {
    e.preventDefault();
    if (state.mode === 'space') {
      state.space.yaw = -.72; state.space.pitch = .36; state.space.zoom = 1; state.space.panX = 0; state.space.panY = 0;
      updateZoomLabel(); draw(); saveSoon();
    } else resetView();
  });

  $('#undoBtn').addEventListener('click', undo);
  $('#redoBtn').addEventListener('click', redo);
  $('#deleteBtn').addEventListener('click', deleteSelected);
  $('#fitBtn').addEventListener('click', fitAll);
  $('#centerBtn').addEventListener('click', () => {
    if (state.mode === 'space') {
      state.space.yaw = -.72; state.space.pitch = .36; state.space.zoom = 1; state.space.panX = 0; state.space.panY = 0;
      updateZoomLabel(); draw(); saveSoon();
    } else resetView();
  });
  $('#exportBtn').addEventListener('click', exportPNG);

  $('#ocrBtn').addEventListener('click', openOcr);
  $$('[data-close-ocr]').forEach(el => el.addEventListener('click', closeOcr));
  const drop = $('#ocrDrop');
  drop.addEventListener('click', () => $('#ocrFile').click());
  $('#ocrFile').addEventListener('change', e => {
    const f = e.target.files && e.target.files[0];
    if (f) setOcrFile(f);
    e.target.value = '';
  });
  ['dragenter', 'dragover'].forEach(ev => drop.addEventListener(ev, e => {
    e.preventDefault(); drop.classList.add('drag');
  }));
  ['dragleave', 'drop'].forEach(ev => drop.addEventListener(ev, e => {
    e.preventDefault(); drop.classList.remove('drag');
  }));
  drop.addEventListener('drop', e => {
    const f = e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files[0];
    if (f) setOcrFile(f);
  });
  $('#ocrRun').addEventListener('click', runOcr);
  $('#ocrExample').addEventListener('click', fillOcrExample);
  $('#ocrGenerate').addEventListener('click', () => {
    const text = $('#ocrText').value;
    ocrApplyData(text, $('#ocrReplace').checked);
  });
  $('#ocrText').addEventListener('keydown', e => {
    if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) {
      e.preventDefault();
      ocrApplyData(e.target.value, $('#ocrReplace').checked);
    }
  });
  $('#zoomIn').addEventListener('click', () => {
    if (state.mode === 'space') { state.space.zoom = clamp(state.space.zoom * 1.2, .35, 5); updateZoomLabel(); draw(); saveSoon(); }
    else { zoomAt(W / 2, H / 2, 1.2); saveSoon(); }
  });
  $('#zoomOut').addEventListener('click', () => {
    if (state.mode === 'space') { state.space.zoom = clamp(state.space.zoom / 1.2, .35, 5); updateZoomLabel(); draw(); saveSoon(); }
    else { zoomAt(W / 2, H / 2, 1 / 1.2); saveSoon(); }
  });

  window.addEventListener('keydown', e => {
    if (e.key === 'Escape' && !$('#ocrModal').hidden) { e.preventDefault(); closeOcr(); return; }
    const tag = (e.target && e.target.tagName) || '';
    const typing = /INPUT|TEXTAREA|SELECT/.test(tag) || (e.target && e.target.isContentEditable);
    if (typing) {
      if (e.key === 'Escape') e.target.blur();
      return;
    }
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') {
      e.preventDefault();
      if (e.shiftKey) redo(); else undo();
      return;
    }
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'y') {
      e.preventDefault(); redo(); return;
    }
    if (e.key === 'Escape') {
      if (state.tangentPicking) {
        state.tangentPicking = false;
        updateTangentUI(); draw(); saveSoon();
        return;
      }
      cancelPending(); return;
    }
    if (e.key === 'Delete' || e.key === 'Backspace') {
      if (state.mode !== 'space' && state.tab === 'geometry' && state.selected) {
        e.preventDefault(); deleteSelected();
      }
    }
  });

  const ro = new ResizeObserver(() => resizeBoard());
  ro.observe($('#canvasWrap'));
  window.addEventListener('resize', resizeBoard);
}

function init() {
  const restored = restoreState();
  if (!state.functions.length) seedDefaultFunction();
  if (!Number.isFinite(state.space.nextLabel)) state.space.nextLabel = state.space.points.length;
  syncUidCounter();

  // 先恢复标签页，再恢复空间模式，避免空间模式隐藏标签页导致状态未应用
  const initTab = state.tab;
  const initMode = state.mode;
  state.mode = 'plane';
  bindUI();
  syncSnapToggles();
  renderConicFields();
  renderSpacePointList();
  setTab(initTab);
  setMode(initMode);
  updateHistoryButtons();
  booted = true;
  resizeBoard();
  renderAllPanels();
  updateModeStatus();
  saveSoon();
  if (!restored) {
    // 首次进入：默认已绘制一条二次函数
    $('#exprInput').value = state.functions[0] ? state.functions[0].expr : 'x^2 - 2x - 1';
  }
}

if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
else init();
