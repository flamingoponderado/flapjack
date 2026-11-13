module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Const
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Simulate

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# The `div` constructor of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Arith (Div d n m)` to the single instruction
`Division@64 (1, false, m, n, d)`: a signed 64-bit divide of `n` by `m`, with
HOL's convention that a zero divisor yields zero.  The CakeML `asmSem` side
guards the divisor with `assert (q <> 0w)`, so a failing step has no successor
and the machine's zero-divisor branch is never reached on a successful step.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The word emitted for `Division@64`: HOL's `e_data` term
`0b10011011010 ++ Rm ++ 00001 ++ (!unsigned) ++ Rn ++ Rd` (Flapjack
infrastructure: a readable abbreviation for a mechanically rendered term). -/
def arm8DivisionWord (unsigned : Bool) (rm rn rd : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 11 1238) ++
    BitVec.setWidth 21 (rm ++
      BitVec.setWidth 16 ((BitVec.ofNat 5 1) ++
        BitVec.setWidth 11 (holV2w 1 [!unsigned] ++
          BitVec.setWidth 10 (rn ++ rd)))))

/-- `e_data` of `Division@64` is the division word (Flapjack infrastructure; no
separately named HOL declaration). -/
theorem arm8EData_division (unsigned : Bool) (rm rn rd : BitVec 5) :
    e_data (.«Division@64» ((1 : BitVec 64), (unsigned, (rm, (rn, rd))))) =
      MachineCode.ARM8 (arm8DivisionWord unsigned rm rn rd) := by
  rfl

/-- `Encode` of `Division@64` is the division word (Flapjack infrastructure; no
separately named HOL declaration). -/
theorem arm8Encode_division (unsigned : Bool) (rm rn rd : BitVec 5) :
    Encode (.Data (.«Division@64» ((1 : BitVec 64), (unsigned, (rm, (rn, rd)))))) =
      MachineCode.ARM8 (arm8DivisionWord unsigned rm rn rd) := by
  simp only [Encode, arm8EData_division]

/-- The rendered `Decode` inverts `arm8DivisionWord` for the signed form used by
`arm8_ast`. -/
theorem arm8Decode_division (rm rn rd : BitVec 5) :
    Decode (arm8DivisionWord false rm rn rd) =
      instruction.Data (Data.«Division@64» ((1 : BitVec 64), (false, (rm, (rn, rd))))) := by
  simp only [arm8DivisionWord, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_true, holV2w_five]

/-- `Run` of `Division@64`: divide `Rn` by `Rm` and write the quotient to `Rd`,
with a zero divisor yielding zero (HOL's `dfn'Division` convention). -/
theorem arm8Run_division (unsigned : Bool) (rm rn rd : BitVec 5) (st : arm8_state) :
    Run (instruction.Data (Data.«Division@64» ((1 : BitVec 64), (unsigned, (rm, (rn, rd)))))) st =
      «write'X» ((if X (TN := 64) rm st == (0 : BitVec 64) then (0 : BitVec 64)
        else if unsigned then (X (TN := 64) rn st).udiv (X (TN := 64) rm st)
        else (X (TN := 64) rn st).sdiv (X (TN := 64) rm st)), rd) st := by
  simp only [Run, «dfn'Division»]
  rfl

/-! ## The `div` constructor -/

/-- The `div` constructor of `encoder_correct arm8TargetL3`, lowered to the
single instruction `Division@64`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_div (destination dividend divisor : Nat)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.arith (.div destination dividend divisor))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms) :
    CaseGoal (.inst (.arith (.div destination dividend divisor))) s1 s2 ms := by
  have hs := h.1
  have hregok : (asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact dividend arm8ConfigL3 = true) ∧
      asmRegOkExact divisor arm8ConfigL3 = true := by
    have hk := hs.2.2.2.2.2.2
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, arm8ConfigL3,
      Bool.and_eq_true] using hk
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hregok.1.1
  obtain ⟨hnlt, hnav, hn31⟩ := regOk_of_asmL3 hregok.1.2
  obtain ⟨hdvlt, hdvav, hdv31⟩ := regOk_of_asmL3 hregok.2
  have hast : arm8Ast (.inst (.arith (.div destination dividend divisor))) =
      [.Data (.«Division@64» (1, false, BitVec.ofNat 5 divisor, BitVec.ofNat 5 dividend,
        BitVec.ofNat 5 destination))] := by
    simp [arm8Ast]
  have henc : arm8Enc (.inst (.arith (.div destination dividend divisor))) =
      arm8Encode (.Data (.«Division@64» (1, false, BitVec.ofNat 5 divisor,
        BitVec.ofNat 5 dividend, BitVec.ofNat 5 destination))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8DivisionWord false (BitVec.ofNat 5 divisor)
    (BitVec.ofNat 5 dividend) (BitVec.ofNat 5 destination)
  have hdec : Decode w = instruction.Data (Data.«Division@64»
      ((1 : BitVec 64), (false, (BitVec.ofNat 5 divisor, (BitVec.ofNat 5 dividend,
        BitVec.ofNat 5 destination))))) :=
    arm8Decode_division _ _ _
  let v : BitVec 64 := (s1.regs dividend).sdiv (s1.regs divisor)
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hne : s1.regs divisor ≠ 0 := by
    have hf : s2.failed = false := by simpa using hs.2.2.2.2.2.1
    rw [← hupd] at hf
    simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc] at hf
    exact hf.1
  refine arm8RegCaseOne _ destination v s1 s2 ms h (by omega) _ _ _ henc (by rw [arm8Encode_division]) hdec ?_ ?_
  · intro hreg
    rw [arm8Run_division, arm8WriteX_of_valid _ _ hd31 hdlt]
    have hXm : X (TN := 64) (BitVec.ofNat 5 divisor) { ms with branch_hint := none } =
        s1.regs divisor := by
      rw [arm8X_of_valid _ hdv31 hdvlt]
      exact hreg divisor ⟨hdvlt, hdvav⟩
    have hXn : X (TN := 64) (BitVec.ofNat 5 dividend) { ms with branch_hint := none } =
        s1.regs dividend := by
      rw [arm8X_of_valid _ hn31 hnlt]
      exact hreg dividend ⟨hnlt, hnav⟩
    simp only [hXm, hXn, holUpdate]
    rw [ite_eq_right (by intro h0; exact hne (by simpa using h0))]
    simp [v]
  · intro hreg p
    refine ⟨?_, fun x => ?_, ?_, fun k => ?_⟩
    · simp [asmUpd, instUpd, arithUpd, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc]
    · simp [asmUpd, instUpd, arithUpd, assertState, updReg, updPc, v,
        Flapjack.Compiler.Encoders.AsmSem.readReg]

end Flapjack.Compiler.Encoders.Arm8.L3
