// Tiny stack VM, ISA v1: 32-bit wrapping values, 256-deep data stack,
// 64 return addresses, 256 memory words, 1M steps, 64K output.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
function joff(c: Uint8Array, at: number): number {
  const r = c[at] | (c[at + 1] << 8);
  return r >= 32768 ? r - 65536 : r;
}
function run(c: Uint8Array, inp: Uint8Array): { e: number; b: Uint8Array } {
  const d = new Int32Array(256), r = new Int32Array(64), m = new Int32Array(256);
  const w = new Uint8Array(65536);
  let pc = 0, sp = 0, rp = 0, st = 0, no = 0, ip = 0, tr = 0, dn = -1;
  while (dn < 0 && tr === 0) {
    if (st >= 1000000) { tr = 10; break; }
    if (pc < 0 || pc >= c.length) { tr = 9; break; }
    const op = c[pc];
    const ok = op <= 7 || (op >= 0x10 && op <= 0x22) || (op >= 0x30 && op <= 0x34) ||
      (op >= 0x40 && op <= 0x41) || (op >= 0x50 && op <= 0x53);
    if (!ok) { tr = 5; break; }
    const im = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + 1 + im > c.length) { tr = 9; break; }
    st++;
    const nx = pc + 1 + im;
    const un = (n: number) => sp < n, fu = (n: number) => sp + n > 256;
    switch (op) {
      case 0: dn = 0; break;
      case 1:
        if (fu(1)) { tr = 3; break; }
        d[sp++] = (c[pc + 1] << 24) >> 24; pc = nx; break;
      case 2:
        if (fu(1)) { tr = 3; break; }
        d[sp++] = c[pc + 1] | (c[pc + 2] << 8) | (c[pc + 3] << 16) | (c[pc + 4] << 24); pc = nx; break;
      case 3:
        if (un(1)) { tr = 2; break; }
        sp--; pc = nx; break;
      case 4:
        if (un(1) || fu(1)) { tr = un(1) ? 2 : 3; break; }
        d[sp] = d[sp - 1]; sp++; pc = nx; break;
      case 5: {
        if (un(2)) { tr = 2; break; }
        const t = d[sp - 1]; d[sp - 1] = d[sp - 2]; d[sp - 2] = t; pc = nx; break;
      }
      case 6:
        if (un(2) || fu(1)) { tr = un(2) ? 2 : 3; break; }
        d[sp] = d[sp - 2]; sp++; pc = nx; break;
      case 7: {
        if (un(3)) { tr = 2; break; }
        const a = d[sp - 3]; d[sp - 3] = d[sp - 2]; d[sp - 2] = d[sp - 1]; d[sp - 1] = a; pc = nx; break;
      }
      case 0x17:
        if (un(1)) { tr = 2; break; }
        d[sp - 1] = (-d[sp - 1]) | 0; pc = nx; break;
      case 0x1b:
        if (un(1)) { tr = 2; break; }
        d[sp - 1] = ~d[sp - 1]; pc = nx; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        if (un(2)) { tr = 2; break; }
        const b = d[--sp], a = d[sp - 1];
        let v = 0;
        if (op === 0x10) v = (a + b) | 0;
        else if (op === 0x11) v = (a - b) | 0;
        else if (op === 0x12) v = Math.imul(a, b);
        else if (op === 0x13) { if (!b) { tr = 4; break; } v = (a / b) | 0; }
        else if (op === 0x14) { if (!b) { tr = 4; break; } v = (a % b) | 0; }
        else if (op === 0x15) { if (!b) { tr = 4; break; } v = ((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (!b) { tr = 4; break; } v = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) v = a & b;
        else if (op === 0x19) v = a | b;
        else if (op === 0x1a) v = a ^ b;
        else if (op === 0x1c) v = a << (b & 31);
        else if (op === 0x1d) v = a >> (b & 31);
        else if (op === 0x1e) v = (a >>> (b & 31)) | 0;
        else if (op === 0x20) v = a === b ? 1 : 0;
        else if (op === 0x21) v = a < b ? 1 : 0;
        else v = (a >>> 0) < (b >>> 0) ? 1 : 0;
        d[sp - 1] = v; pc = nx; break;
      }
      case 0x30: pc = nx + joff(c, pc + 1); break;
      case 0x31:
        if (un(1)) { tr = 2; break; }
        pc = d[--sp] === 0 ? nx + joff(c, pc + 1) : nx; break;
      case 0x32:
        if (un(1)) { tr = 2; break; }
        pc = d[--sp] !== 0 ? nx + joff(c, pc + 1) : nx; break;
      case 0x33:
        if (rp >= 64) { tr = 7; break; }
        r[rp++] = nx; pc = c[pc + 1] | (c[pc + 2] << 8); break;
      case 0x34:
        if (rp <= 0) { tr = 8; break; }
        pc = r[--rp]; break;
      case 0x40: {
        if (un(1)) { tr = 2; break; }
        const a = d[sp - 1];
        if (a < 0 || a > 255) { tr = 6; break; }
        d[sp - 1] = m[a]; pc = nx; break;
      }
      case 0x41: {
        if (un(2)) { tr = 2; break; }
        const a = d[--sp], v = d[--sp];
        if (a < 0 || a > 255) { tr = 6; break; }
        m[a] = v; pc = nx; break;
      }
      case 0x50: {
        if (un(1)) { tr = 2; break; }
        const s = String(d[--sp]);
        if (no + s.length > 65536) { tr = 11; break; }
        for (let i = 0; i < s.length; i++) w[no++] = s.charCodeAt(i);
        pc = nx; break;
      }
      case 0x51:
        if (un(1)) { tr = 2; break; }
        if (no >= 65536) { tr = 11; break; }
        w[no++] = d[--sp] & 255; pc = nx; break;
      case 0x52:
        if (fu(1)) { tr = 3; break; }
        d[sp++] = ip < inp.length ? inp[ip++] : -1; pc = nx; break;
      case 0x53:
        if (un(1)) { tr = 2; break; }
        dn = d[--sp] & 255; break;
    }
  }
  return { e: dn >= 0 ? dn : tr, b: w.subarray(0, no) };
}
for (const id of readdirSync(I).sort()) {
  const res = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), res.b);
  writeFileSync(join(O, id, 'exit.txt'), String(res.e) + '\n');
}
