// Tiny stack VM for make.fun's tiny stack ISA v1. For every instance under
// /input/<id>/ it writes /output/<id>/stdout.bin and /output/<id>/exit.txt.
// Node 22, standard library only, deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode table: immediate length, values popped, values pushed, by opcode byte.
const IMM = new Int8Array(256).fill(-1);
const POPN = new Int8Array(256);
const PUSHN = new Int8Array(256);
for (const [op, imm, pops, pushes] of [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
]) {
  IMM[op] = imm;
  POPN[op] = pops;
  PUSHN[op] = pushes;
}

// Runs one program to its halt, exit or trap: what it wrote, and its exit code.
function runProgram(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = prog.length;
  const data = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  const text = new TextEncoder();
  let sp = 0, cp = 0, ip = 0, pc = 0, steps = 0, len = 0;
  const done = (code: number) => ({ out: out.slice(0, len), code });

  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm < 0) return done(5);
    if (pc + imm >= n) return done(9);
    steps += 1;
    const nx = pc + 1 + imm;
    if (sp < POPN[op]) return done(2);
    if (sp - POPN[op] + PUSHN[op] > 256) return done(3);
    pc = nx;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: data[sp++] = (prog[nx - 1] << 24) >> 24; break;
      case 0x02: data[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); break;
      case 0x03: sp -= 1; break;
      case 0x04: data[sp] = data[sp - 1]; sp += 1; break;
      case 0x05: { const t = data[sp - 1]; data[sp - 1] = data[sp - 2]; data[sp - 2] = t; break; }
      case 0x06: data[sp] = data[sp - 2]; sp += 1; break;
      case 0x07: { const a = data[sp - 3]; data[sp - 3] = data[sp - 2]; data[sp - 2] = data[sp - 1]; data[sp - 1] = a; break; }
      case 0x17: data[sp - 1] = (-data[sp - 1]) | 0; break;
      case 0x1b: data[sp - 1] = ~data[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = data[sp - 1];
        const a = data[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        data[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) {
          const v = data[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return done(7);
        calls[cp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = calls[--cp];
        break;
      case 0x40: {
        const addr = data[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        data[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = data[sp - 1];
        const v = data[sp - 2];
        if (addr < 0 || addr > 255) return done(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = text.encode(String(data[sp - 1]));
        if (len + bytes.length > 65536) return done(11);
        sp -= 1;
        out.set(bytes, len);
        len += bytes.length;
        break;
      }
      case 0x51:
        if (len + 1 > 65536) return done(11);
        out[len++] = data[--sp] & 255;
        break;
      case 0x52:
        data[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        return done(data[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let prog = new Uint8Array(0);
  let input = new Uint8Array(0);
  try { prog = new Uint8Array(readFileSync(join(I, id, 'program.bin'))); } catch { /* missing program traps 9 */ }
  try { input = new Uint8Array(readFileSync(join(I, id, 'input.bin'))); } catch { /* missing input is empty */ }
  const r = runProgram(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
