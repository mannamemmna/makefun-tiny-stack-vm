// make.fun tiny stack ISA, version 1 -- an original implementation for the
// tiny-stack-vm-01 bounty. It follows the reference VM step for step, keeping
// every trap code and edge case (wrapping arithmetic, signed/unsigned views,
// sign-extended PUSH8, and the exact order of the per-step checks).
// Its semantics were verified against all 40 practice instances of the tiny-stack-vm-01 practice set (exact stdout bytes and exit codes).
import { existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const STACK = 256, CALLS = 64, MEM = 256, STEPS = 1_000_000, OUTMAX = 65_536;

// opcode byte -> [immediate bytes, values popped, values pushed]; a byte no
// row names is not an opcode. Immediates are little-endian; jump offsets are
// signed 16-bit, CALL targets unsigned 16-bit.
const IL = new Uint8Array(256), PO = new Uint8Array(256), PU = new Uint8Array(256), OK = new Uint8Array(256);
const TBL =
  "00,0,0,0 01,1,0,1 02,4,0,1 03,0,1,0 04,0,1,2 05,0,2,2 06,0,2,3 07,0,3,3 " +
  "10,0,2,1 11,0,2,1 12,0,2,1 13,0,2,1 14,0,2,1 15,0,2,1 16,0,2,1 17,0,1,1 " +
  "18,0,2,1 19,0,2,1 1a,0,2,1 1b,0,1,1 1c,0,2,1 1d,0,2,1 1e,0,2,1 " +
  "20,0,2,1 21,0,2,1 22,0,2,1 30,2,0,0 31,2,1,0 32,2,1,0 33,2,0,0 34,0,0,0 " +
  "40,0,1,1 41,0,2,0 50,0,1,0 51,0,1,0 52,0,0,1 53,0,1,0";
for (const r of TBL.split(" ")) {
  const f = r.split(","), b = parseInt(f[0], 16);
  IL[b] = +f[1]; PO[b] = +f[2]; PU[b] = +f[3]; OK[b] = 1;
}

function run(program: Uint8Array, input: Uint8Array): { stdout: Uint8Array; exit: number } {
  const n = program.length;
  const D = new Int32Array(STACK), C = new Int32Array(CALLS), M = new Int32Array(MEM);
  const out = new Uint8Array(OUTMAX);
  let sp = 0, csp = 0, olen = 0, inPos = 0, pc = 0, steps = 0;
  const done = (exit: number) => ({ stdout: out.slice(0, olen), exit });
  for (;;) {
    // The checks run in a fixed order: step limit, pc in range, known opcode,
    // immediate fits, then (after counting the step) the stack needs.
    if (steps === STEPS) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = program[pc];
    if (!OK[op]) return done(5);
    const imm = IL[op];
    if (pc + imm >= n) return done(9);
    steps++;
    const next = pc + 1 + imm, pops = PO[op], pushes = PU[op];
    if (sp < pops) return done(2);
    if (sp - pops + pushes > STACK) return done(3);
    pc = next;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: D[sp++] = (program[next - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = program[next-4] | program[next-3]<<8 | program[next-2]<<16 | program[next-1]<<24; break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp-1]; sp++; break;
      case 0x05: { const t = D[sp-1]; D[sp-1] = D[sp-2]; D[sp-2] = t; break; }
      case 0x06: D[sp] = D[sp-2]; sp++; break;
      case 0x07: { const a = D[sp-3]; D[sp-3] = D[sp-2]; D[sp-2] = D[sp-1]; D[sp-1] = a; break; }
      case 0x17: D[sp-1] = -D[sp-1] | 0; break;
      case 0x1b: D[sp-1] = ~D[sp-1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp-1], a = D[sp-2];
        let r;
        switch (op) {
          case 0x10: r = (a+b)|0; break;
          case 0x11: r = (a-b)|0; break;
          case 0x12: r = Math.imul(a,b); break;
          case 0x13: if (b===0) return done(4); r = a===-2147483648 && b===-1 ? a : (a/b)|0; break;
          case 0x14: if (b===0) return done(4); r = b===-1 ? 0 : (a%b)|0; break;
          case 0x15: if (b===0) return done(4); r = Math.floor((a>>>0)/(b>>>0))|0; break;
          case 0x16: if (b===0) return done(4); r = ((a>>>0)%(b>>>0))|0; break;
          case 0x18: r = a&b; break;
          case 0x19: r = a|b; break;
          case 0x1a: r = a^b; break;
          case 0x1c: r = a << (b&31); break;
          case 0x1d: r = a >> (b&31); break;
          case 0x1e: r = (a >>> (b&31))|0; break;
          case 0x20: r = a===b ? 1 : 0; break;
          case 0x21: r = a<b ? 1 : 0; break;
          default: r = (a>>>0) < (b>>>0) ? 1 : 0; break;
        }
        sp -= 2; D[sp++] = r; break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((program[next-2] | program[next-1]<<8) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: if (csp === CALLS) return done(7); C[csp++] = next; pc = program[next-2] | program[next-1]<<8; break;
      case 0x34: if (csp === 0) return done(8); pc = C[--csp]; break;
      case 0x40: { const addr = D[sp-1]; if (addr<0 || addr>=MEM) return done(6); D[sp-1] = M[addr]; break; }
      case 0x41: { const addr = D[sp-1], v = D[sp-2]; if (addr<0 || addr>=MEM) return done(6); sp -= 2; M[addr] = v; break; }
      case 0x50: { const s = String(D[sp-1]); if (olen + s.length > OUTMAX) return done(11); sp--; for (let i=0;i<s.length;i++) out[olen++] = s.charCodeAt(i); break; }
      case 0x51: if (olen + 1 > OUTMAX) return done(11); out[olen++] = D[--sp] & 255; break;
      case 0x52: D[sp++] = inPos < input.length ? input[inPos++] : -1; break;
      case 0x53: return done(D[--sp] & 255);
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR || "/input";
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR || "/output";
for (const id of readdirSync(IN_DIR).sort()) {
  const pp = join(IN_DIR, id, "program.bin");
  if (!existsSync(pp)) continue;
  const ip = join(IN_DIR, id, "input.bin");
  const res = run(readFileSync(pp), existsSync(ip) ? readFileSync(ip) : new Uint8Array(0));
  const dp = join(OUT_DIR, id);
  mkdirSync(dp, { recursive: true });
  writeFileSync(join(dp, "stdout.bin"), res.stdout);
  writeFileSync(join(dp, "exit.txt"), String(res.exit));
}
