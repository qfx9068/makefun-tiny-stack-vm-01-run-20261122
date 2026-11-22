// Tiny stack VM: a spec-faithful interpreter for the tiny stack ISA.
// Every trap carries its own exit code; arithmetic wraps to 32 bits.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Stack effect tables indexed by opcode: immediate bytes, pops, pushes.
const IM = new Int8Array(84), PO = new Int8Array(84), PU = new Int8Array(84);
IM[1] = 1; IM[2] = 4; PU[1] = PU[2] = 1;
PO[3] = 1; PO[4] = 1; PU[4] = 2; PO[5] = 2; PU[5] = 2;
PO[6] = 2; PU[6] = 3; PO[7] = 3; PU[7] = 3;
for (let i = 16; i <= 34; i++) { PO[i] = 2; PU[i] = 1; }
PO[23] = PO[27] = 1;
IM[48] = IM[49] = IM[50] = IM[51] = 2; PO[49] = PO[50] = 1;
PO[64] = 1; PU[64] = 1; PO[65] = 2;
PO[80] = PO[81] = PO[83] = 1; PU[82] = 1;

function run(prog, inp) {
  const st = new Int32Array(256), cs = new Int32Array(64), mem = new Int32Array(256);
  const buf = new Uint8Array(65536);
  let sp = 0, csp = 0, pc = 0, ip = 0, len = 0, steps = 0;
  const n = prog.length;
  const end = (code) => ({ out: buf.slice(0, len), code });
  for (;;) {
    if (steps >= 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    const ok = op !== 31 && (op < 8 || (op >= 16 && op <= 34) || (op >= 48 && op <= 52) || op === 64 || op === 65 || (op >= 80 && op <= 83));
    if (!ok) return end(5);
    const imm = IM[op];
    if (imm > 0 && pc + imm >= n) return end(9);
    steps++;
    if (sp < PO[op]) return end(2);
    if (sp - PO[op] + PU[op] > 256) return end(3);
    pc += 1 + imm;
    if (op >= 16 && op <= 34 && op !== 23 && op !== 27) {
      const b = st[--sp], a = st[--sp];
      let r;
      if (op === 16) r = a + b;
      else if (op === 17) r = a - b;
      else if (op === 18) r = Math.imul(a, b);
      else if (op === 19) { if (!b) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 20) { if (!b) return end(4); r = b === -1 ? 0 : a % b; }
      else if (op === 21) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)); }
      else if (op === 22) { if (!b) return end(4); r = (a >>> 0) % (b >>> 0); }
      else if (op === 24) r = a & b;
      else if (op === 25) r = a | b;
      else if (op === 26) r = a ^ b;
      else if (op === 28) r = a << (b & 31);
      else if (op === 29) r = a >> (b & 31);
      else if (op === 30) r = a >>> (b & 31);
      else if (op === 32) r = a === b ? 1 : 0;
      else if (op === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      st[sp++] = r | 0;
      continue;
    }
    switch (op) {
      case 0: return end(0);
      case 1: st[sp++] = (prog[pc - 1] << 24) >> 24; break;
      case 2: st[sp++] = prog[pc - 4] | (prog[pc - 3] << 8) | (prog[pc - 2] << 16) | (prog[pc - 1] << 24); break;
      case 3: sp--; break;
      case 4: st[sp] = st[sp - 1]; sp++; break;
      case 5: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; }
      case 6: st[sp] = st[sp - 2]; sp++; break;
      case 7: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; }
      case 23: st[sp - 1] = (-st[sp - 1]) | 0; break;
      case 27: st[sp - 1] = ~st[sp - 1]; break;
      case 48: case 49: case 50: {
        const rel = ((prog[pc - 2] | (prog[pc - 1] << 8)) << 16) >> 16;
        if (op === 48 || (st[--sp] === 0) === (op === 49)) pc += rel;
        break;
      }
      case 51:
        if (csp >= 64) return end(7);
        cs[csp++] = pc;
        pc = prog[pc - 2] | (prog[pc - 1] << 8);
        break;
      case 52:
        if (csp === 0) return end(8);
        pc = cs[--csp];
        break;
      case 64: {
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 65: {
        const addr = st[sp - 1], v = st[sp - 2];
        if (addr < 0 || addr > 255) return end(6);
        sp -= 2; mem[addr] = v;
        break;
      }
      case 80: {
        const s = String(st[--sp]);
        if (len + s.length > 65536) return end(11);
        for (let i = 0; i < s.length; i++) buf[len++] = s.charCodeAt(i);
        break;
      }
      case 81:
        if (len >= 65536) return end(11);
        buf[len++] = st[--sp] & 255;
        break;
      case 82: st[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return end(st[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
