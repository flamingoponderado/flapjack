module

public import Mathlib.Tactic
public import Flapjack.Compiler.Encoders.X64.Machine.TargetProof

@[expose] public section

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

/-! ## The SSE decoder -/

/-- Two readers agreeing on the eight bytes from `off` decode the same SSE
instruction.  The only reader-dependent byte beyond the operand parser is the
shift immediate at `off + 1 + p.len`, which lies within the bound because a
parsed operand consumes at most six bytes. -/
theorem decodeSSE_congr (r r' : Nat → BitVec 8) (off : Nat) (mandatory : Nat)
    (hasRex rexW rexR rexB : Bool) (h : ∀ i, i < off + 8 → r i = r' i) :
    decodeSSE r off mandatory hasRex rexW rexR rexB =
      decodeSSE r' off mandatory hasRex rexW rexR rexB := by
  have hp1 : parseRM r (off + 1) rexB = parseRM r' (off + 1) rexB :=
    parseRM_congr r r' (off + 1) rexB (fun i hi => h i (by omega))
  have hp2 : parseRM r (off + 2) rexB = parseRM r' (off + 2) rexB :=
    parseRM_congr r r' (off + 2) rexB (fun i hi => h i (by omega))
  simp only [decodeSSE]
  rw [h off (by omega), h (off + 1) (by omega), hp1, hp2]
  cases hp : parseRM r' (off + 1) rexB with
  | none => simp
  | some p =>
    cases hp2' : parseRM r' (off + 2) rexB with
    | none =>
      have hl : p.len ≤ 6 := parseRM_len_le r' (off + 1) rexB p hp
      simp
      rw [h (off + 1 + p.len) (by omega)]
    | some q =>
      have hl : p.len ≤ 6 := parseRM_len_le r' (off + 1) rexB p hp
      simp
      rw [h (off + 1 + p.len) (by omega)]

/-! ## The whole decoder -/

/-- Two readers agreeing on the first sixteen bytes decode the same
instruction.  Sixteen bytes cover the longest x86-64 instruction, so the
decoder never reads past the bound. -/
theorem decode_congr (r r' : Nat → BitVec 8) (h : ∀ i, i < 16 → r i = r' i) :
    decode r = decode r' := by
  have hlen : ∀ (rexB : Bool) (p : ParsedRM), parseRM r' 2 rexB = some p → p.len ≤ 6 :=
    fun rexB p hp => parseRM_len_le r' 2 rexB p hp
  simp only [decode, decodeNoRex, decodeRex, binopReg, movImm]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega)]
  have hp1 : ∀ rexB, parseRM r 1 rexB = parseRM r' 1 rexB :=
    fun rexB => parseRM_congr r r' 1 rexB (fun i hi => h i (by omega))
  have hp2 : ∀ rexB, parseRM r 2 rexB = parseRM r' 2 rexB :=
    fun rexB => parseRM_congr r r' 2 rexB (fun i hi => h i (by omega))
  have hp3 : ∀ rexB, parseRM r 3 rexB = parseRM r' 3 rexB :=
    fun rexB => parseRM_congr r r' 3 rexB (fun i hi => h i (by omega))
  simp [hp1, hp2, hp3]
  rw [le64_congr r r' 2 (fun i hi => h i (by omega)),
      imm32_congr r r' 1 (fun i hi => h i (by omega)),
      imm32_congr r r' 2 (fun i hi => h i (by omega)),
      imm32_congr r r' 3 (fun i hi => h i (by omega)),
      imm8_congr r r' 1 (fun i hi => h i (by omega))]
  rw [decodeSSE_congr r r' 3 0x66 true _ _ _ (fun i hi => h i (by omega)),
      decodeSSE_congr r r' 2 0x66 false false false false (fun i hi => h i (by omega)),
      decodeSSE_congr r r' 3 0xF2 true _ _ _ (fun i hi => h i (by omega)),
      decodeSSE_congr r r' 2 0xF2 false false false false (fun i hi => h i (by omega)),
      decodeSSE_congr r r' 3 0xF3 true _ _ _ (fun i hi => h i (by omega)),
      decodeSSE_congr r r' 2 0xF3 false false false false (fun i hi => h i (by omega))]
  split <;> try rfl
  all_goals (try (split <;> try rfl))
  all_goals (try (split <;> try rfl))
  all_goals (try (split <;> try rfl))
  all_goals (try (split <;> try rfl))
  all_goals (try (split <;> try rfl))
  all_goals
    first
    | rfl
    | (rw [imm8_congr r r' _ (fun i hi => h i (by have h := hlen _ _ (by assumption); omega))])
    | (rw [imm32_congr r r' _ (fun i hi => h i (by have h := hlen _ _ (by assumption); omega))])

end Flapjack.Compiler.Encoders.X64
