import Mathlib.Tactic
import Flapjack.Compiler.Encoders.X64.Machine.TargetProof

/-!
# Reader congruence for the closed x86-64 decoder

The machine fetch is a byte reader `fun i => s.mem (s.pc + i)`.  To show that
two states agreeing on a memory domain decode the same instruction, the decoder
has to be insensitive to bytes it never reads.  This module proves the
byte-level congruence lemmas: `le32`/`le64`, the sign-extended immediates, the
`parseRM` operand parser, and the two decoder helpers `binopReg` and `movImm`.
They are the analogue of the ARM8 `fetchWord_congr`, for a variable-length
instruction encoding.

The bound `off + 6` on `parseRM` is tight: a ModRM byte with `mod = 2`, a SIB
byte and a 32-bit displacement reads six bytes from `off`.
-/

namespace Flapjack.Compiler.Encoders.X64

/-! ## Little-endian immediates -/

/-- Two readers agreeing on the four bytes from `off` read the same `le32`. -/
theorem le32_congr (r r' : Nat → BitVec 8) (off : Nat)
    (h : ∀ i, i < off + 4 → r i = r' i) : le32 r off = le32 r' off := by
  simp only [le32, h off (by omega), h (off + 1) (by omega), h (off + 2) (by omega),
    h (off + 3) (by omega)]

/-- Two readers agreeing on the eight bytes from `off` read the same `le64`. -/
theorem le64_congr (r r' : Nat → BitVec 8) (off : Nat)
    (h : ∀ i, i < off + 8 → r i = r' i) : le64 r off = le64 r' off := by
  simp only [le64, h off (by omega), h (off + 1) (by omega), h (off + 2) (by omega),
    h (off + 3) (by omega), h (off + 4) (by omega), h (off + 5) (by omega),
    h (off + 6) (by omega), h (off + 7) (by omega)]

/-- Two readers agreeing on the byte at `off` read the same `imm8`. -/
theorem imm8_congr (r r' : Nat → BitVec 8) (off : Nat)
    (h : ∀ i, i < off + 1 → r i = r' i) : imm8 r off = imm8 r' off := by
  simp only [imm8, h off (by omega)]

/-- Two readers agreeing on the four bytes from `off` read the same `imm32`. -/
theorem imm32_congr (r r' : Nat → BitVec 8) (off : Nat)
    (h : ∀ i, i < off + 4 → r i = r' i) : imm32 r off = imm32 r' off := by
  simp only [imm32, le32_congr r r' off h]

/-! ## The ModRM operand parser -/

/-- Two readers agreeing on the six bytes from `off` parse the same operand. -/
theorem parseRM_congr (r r' : Nat → BitVec 8) (off : Nat) (rexB : Bool)
    (h : ∀ i, i < off + 6 → r i = r' i) :
    parseRM r off rexB = parseRM r' off rexB := by
  simp only [parseRM]
  simp only [h off (by omega), h (off + 1) (by omega)]
  simp only [imm32_congr r r' (off + 1) (fun i hi => h i (by omega)),
    imm32_congr r r' (off + 2) (fun i hi => h i (by omega)),
    imm8_congr r r' (off + 1) (fun i hi => h i (by omega)),
    imm8_congr r r' (off + 2) (fun i hi => h i (by omega))]

/-- A parsed operand consumes at most six bytes. -/
theorem parseRM_len_le (r : Nat → BitVec 8) (off : Nat) (rexB : Bool) (p : ParsedRM)
    (h : parseRM r off rexB = some p) : p.len ≤ 6 := by
  unfold parseRM at h
  dsimp only at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp

/-! ## Decoder helpers -/

/-- Two readers agreeing on the six bytes from `off` decode the same register
binary operation. -/
theorem binopReg_congr (opcode off : Nat) (r r' : Nat → BitVec 8) (hi : Nat)
    (rexW rexB : Bool) (h : ∀ i, i < off + 6 → r i = r' i) :
    binopReg opcode off r hi rexW rexB = binopReg opcode off r' hi rexW rexB := by
  simp only [binopReg, parseRM_congr r r' off rexB h]

/-- Two readers agreeing on the ten bytes from `0` decode the same immediate
move. -/
theorem movImm_congr (low : Nat) (r r' : Nat → BitVec 8) (rexB rexW : Bool)
    (h : ∀ i, i < 10 → r i = r' i) :
    movImm low r rexB rexW = movImm low r' rexB rexW := by
  simp only [movImm, le64_congr r r' 2 (fun i hi => h i (by omega)),
    imm32_congr r r' 2 (fun i hi => h i (by omega))]

end Flapjack.Compiler.Encoders.X64
