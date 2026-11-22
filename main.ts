// Tiny stack VM: a from-scratch interpreter for make.fun's tiny stack ISA v1.
// One run answers every instance in /input/<id>/, writing /output/<id>/stdout.bin
// and /output/<id>/exit.txt. Node 22, no dependencies, erasable TypeScript only.
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function run(prog, input) {
  const n = prog.length;
  const st = new Int32Array(256); // data stack (256 max)
  const calls = new Int32Array(64); // call stack (64 max)
  const mem = new Int32Array(256); // memory, all zero at start
  const out = new Uint8Array(65536); // output, 65,536 bytes max
  let sp = 0, cp = 0, olen = 0, ipos = 0, pc = 0, steps = 0;
  const end = (code) => ({ bytes: out.subarray(0, olen), code });
  for (;;) {
    // One step, in ISA.md's order: step limit, pc, opcode, immediate, stack.
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    let imm = 0, pops = 0, pushes = 0; // immediate length, stack shape
    switch (op) {
      case 0x00: break; // HALT
      case 0x01: imm = 1; pushes = 1; break; // PUSH8
      case 0x02: imm = 4; pushes = 1; break; // PUSH32
      case 0x03: pops = 1; break; // POP
      case 0x04: pops = 1; pushes = 2; break; // DUP
      case 0x05: pops = 2; pushes = 2; break; // SWAP
      case 0x06: pops = 2; pushes = 3; break; // OVER
      case 0x07: pops = 3; pushes = 3; break; // ROT
      case 0x17: case 0x1b: pops = 1; pushes = 1; break; // NEG, NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: pops = 2; pushes = 1; break; // ALU
      case 0x30: case 0x33: imm = 2; break; // JMP, CALL
      case 0x31: case 0x32: imm = 2; pops = 1; break; // JZ, JNZ
      case 0x34: break; // RET
      case 0x40: pops = 1; pushes = 1; break; // LOAD
      case 0x41: pops = 2; break; // STORE
      case 0x50: case 0x51: pops = 1; break; // PRINT, PUTC
      case 0x52: pushes = 1; break; // IN
      case 0x53: pops = 1; break; // EXIT
      default: return end(5); // unknown opcode
    }
    if (pc + imm >= n) return end(9); // immediate cut off by program end
    steps++;
    const nx = pc + 1 + imm; // next instruction's address
    if (sp < pops) return end(2);
    if (sp - pops + pushes > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0x00: return end(0);
      case 0x01: st[sp++] = (prog[nx - 1] << 24) >> 24; break; // PUSH8 sign-extends
      case 0x02: st[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]; sp++; break;
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; }
      case 0x06: st[sp] = st[sp - 2]; sp++; break;
      case 0x07: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; }
      case 0x17: st[sp - 1] = -st[sp - 1] | 0; break; // NEG wraps
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1], a = st[sp - 2];
        let r;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break; // low 32 bits of exact product
          case 0x13: // DIV truncates toward zero; -2^31 / -1 is -2^31
            if (b === 0) return end(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14: // MOD sign follows a; x % -1 is 0
            if (b === 0) return end(4);
            r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: // DIVU: operands read unsigned
            if (b === 0) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: // MODU: operands read unsigned
            if (b === 0) return end(4);
            r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // low 5 bits of count
          case 0x1d: r = a >> (b & 31); break; // arithmetic shift
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // logical shift
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU unsigned
        }
        sp -= 2; st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (!take) { const v = st[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel; // target unchecked; out-of-program traps 9 next step
        break;
      }
      case 0x33: // CALL
        if (cp === 64) return end(7);
        calls[cp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return end(8);
        pc = calls[--cp];
        break;
      case 0x40: { // LOAD
        const addr = st[sp - 1];
        if (addr < 0 || addr >= 256) return end(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE: (v addr --), address is on top
        const addr = st[sp - 1], v = st[sp - 2];
        if (addr < 0 || addr >= 256) return end(6);
        sp -= 2; mem[addr] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline; over-limit writes nothing
        const s = String(st[sp - 1]);
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: one byte, v AND 255
        if (olen + 1 > 65536) return end(11);
        out[olen++] = st[--sp] & 255;
        break;
      case 0x52: st[sp++] = ipos < input.length ? input[ipos++] : -1; break; // IN: -1 past end
      case 0x53: return end(st[--sp] & 255); // EXIT with the low byte
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  const prog = existsSync(join(dir, 'program.bin')) ? readFileSync(join(dir, 'program.bin')) : Buffer.alloc(0);
  const input = existsSync(join(dir, 'input.bin')) ? readFileSync(join(dir, 'input.bin')) : Buffer.alloc(0);
  const r = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.bytes);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
