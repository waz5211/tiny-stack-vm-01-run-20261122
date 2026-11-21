// Tiny stack VM: a faithful interpreter of make.fun's tiny stack ISA v1.
// node main.ts answers every instance in /input/<id>/, writing
// /output/<id>/stdout.bin and /output/<id>/exit.txt. Node 22, no dependencies.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [byte, immediate bytes, pops, pushes] for every opcode ISA.md names.
const OPS = [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]];
const BY = new Array(256);
for (const o of OPS) BY[o[0]] = o;

function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const end = (c) => ({ o: out.subarray(0, olen), c });
  for (;;) {
    // ISA.md "One step", in its order: step limit, pc, opcode, immediate, stack.
    if (steps === 1e6) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc], t = BY[op];
    if (!t) return end(5);
    const imm = t[1];
    if (pc + imm >= n) return end(9);
    steps++;
    const nx = pc + 1 + imm;
    if (sp < t[2]) return end(2);
    if (sp - t[2] + t[3] > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0: return end(0); // HALT
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break; // PUSH32
      case 3: sp--; break; // POP
      case 4: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 5: { const x = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = x; break; } // SWAP
      case 6: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0; // ADD, wraps
        else if (op === 17) r = (a - b) | 0; // SUB, wraps
        else if (op === 18) r = Math.imul(a, b); // MUL, low 32 bits of the exact product
        else if (op === 19) { // DIV, truncated toward zero; INT_MIN / -1 is INT_MIN
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) { // MOD, sign of a; x % -1 is 0
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) { // DIVU, unsigned
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) { // MODU, unsigned
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 24) r = a & b; // AND
        else if (op === 25) r = a | b; // OR
        else if (op === 26) r = a ^ b; // XOR
        else if (op === 28) r = a << (b & 31); // SHL, low 5 bits of the count
        else if (op === 29) r = a >> (b & 31); // SHR, arithmetic
        else if (op === 30) r = (a >>> (b & 31)) | 0; // SHRU, logical
        else if (op === 32) r = a === b ? 1 : 0; // EQ
        else if (op === 33) r = a < b ? 1 : 0; // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 23: D[sp - 1] = (-D[sp - 1]) | 0; break; // NEG, wraps
      case 27: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 48: case 49: case 50: { // JMP, JZ, JNZ: pc = next + signed 16-bit offset
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51: // CALL: 64 return addresses held already traps 7
        if (csp === 64) return end(7);
        C[csp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52: // RET: an empty call stack traps 8
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 64: { // LOAD: address outside 0..255 traps 6
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: { // STORE: ( v addr -- ), address outside 0..255 traps 6
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a > 255) return end(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII, no newline; past 65,536 bytes traps 11
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC: one byte, v AND 255; past 65,536 bytes traps 11
        if (olen + 1 > 65536) return end(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN: -1 once used up
      case 83: return end(D[--sp] & 255); // EXIT: code v AND 255
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), `${r.c}\n`);
}
