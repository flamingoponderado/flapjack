import Flapjack.Compiler.Backend.LabSem.Inst
import Flapjack.Compiler.Backend.LabSem.SharedMemory

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabSem

/-- Full arbitrary operand and clock replacement from the original theorem. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "reg_imm_with_clock"
  (words_as_type_indexed_bitvec)]
theorem regImmWithClock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (operand : HolRegImm width) (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (z : Nat) : regImm operand { s with clock := z } = regImm operand s := by
  cases operand <;> rfl

/-- All native instructions commute with arbitrary clock replacement, including
failed updates and every FP constructor. The inherited real rendering remains
subject to SOUNDNESS item8. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_inst_with_clock"
  (words_as_type_indexed_bitvec)]
theorem asmInstWithClock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (instruction : HolInst width) (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (z : Nat) : asmInst instruction { s with clock := z } =
      { asmInst instruction s with clock := z } := by
  cases instruction with
  | skip => rfl
  | const register value => rfl
  | arith operation =>
      cases operation <;> simp only [asmInst, arithUpd, regImmWithClock]
      all_goals repeat' first
        | simp_all [binopUpd, updReg, assertState]
        | split
  | mem operator register address =>
      cases operator <;> simp only [asmInst, memOp, memLoad, memStore,
        memLoad32, memStore32, memLoadByte, memStoreByte, addrValue]
      all_goals repeat' first
        | simp_all [updReg, updMem, assertState]
        | split
  | fp operation =>
      cases operation <;> simp only [asmInst, fpUpd, readFpReg]
      all_goals repeat' first
        | simp_all [updFpReg, updReg, assertState]
        | split
      all_goals rfl

/-- Exact source addition order and arbitrary address; no validity premise. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "addr_add_clock_eq"
  (words_as_type_indexed_bitvec)]
theorem addrAddClockEq {width : Nat} [NeZero width] {C : Type} {F : Type}
    (address : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (extra : Nat) : addrValue address { s with clock := extra + s.clock } =
      addrValue address s := by
  cases address <;> rfl

/-- Flapjack equation consequence used to assemble all three original shared
clock clauses. The Option mapping is local infrastructure, not a HOL declaration. -/
private theorem shareMemOp_clockMap {width : Nat} [NeZero width] {C F : Type}
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) (extra : Nat)
    (hne : s.clock ≠ 0) :
    shareMemOp operator register address { s with clock := extra + s.clock } =
      (shareMemOp operator register address s).map
        (fun (result, next) => (result, { next with clock := extra + next.clock })) := by
  have hc : extra + s.clock - 1 = extra + (s.clock - 1) := by omega
  cases operator <;> simp only [shareMemOp, shareMemLoad, shareMemStore, addrValue]
  all_goals repeat' first
    | simp_all [incPc, decClock]
    | split

/-- All three full original NONE, returning and final shared-memory clauses.
The original nonzero-clock guard is kept separately in each antecedent; all
state/result binders and the literal extra+clock update are retained. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "share_mem_op_add_clock_same"
  (words_as_type_indexed_bitvec)]
theorem shareMemOpAddClockSame {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (operator : HolMemop) (register : Nat) (address : HolAddr width) (extra : Nat)
    (ffi : HolFfiState F) (bytes : List (BitVec 8))
    (r : Flapjack.Compiler.Backend.LabSem.State width C F) (final : HolFinalEvent)
    (r2 : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (s.clock ≠ 0 ∧ shareMemOp operator register address s = none →
      shareMemOp operator register address { s with clock := extra + s.clock } = none) ∧
    (s.clock ≠ 0 ∧ shareMemOp operator register address s = some (.ret ffi bytes, r) →
      shareMemOp operator register address { s with clock := extra + s.clock } =
        some (.ret ffi bytes, { r with clock := extra + r.clock })) ∧
    (s.clock ≠ 0 ∧ shareMemOp operator register address s = some (.final final, r2) →
      shareMemOp operator register address { s with clock := extra + s.clock } =
        some (.final final, { r2 with clock := extra + r2.clock })) := by
  constructor
  · intro h
    rw [shareMemOp_clockMap _ _ _ _ _ h.1, h.2]
    rfl
  · constructor
    · intro h
      rw [shareMemOp_clockMap _ _ _ _ _ h.1, h.2]
      rfl
    · intro h
      rw [shareMemOp_clockMap _ _ _ _ _ h.1, h.2]
      rfl

end Flapjack.Compiler.Backend.LabProps
