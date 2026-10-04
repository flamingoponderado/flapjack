import Flapjack.Compiler.Backend.WordCse.Proofs.KeyInjectivity
import Flapjack.Compiler.Backend.WordCse.Proofs.InsertEquality
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm WordSemStateFiniteExact

/-! Internal proof decomposition of the original arithmetic-key cases. These
helpers have no separate HOL declarations; they derive instruction shape and
value transport internally, without adding public simulation hypotheses. -/

private theorem regImmKeyEq {width : Nat} [NeZero width] (a b : HolRegImm width) :
    regImmToNumList a = regImmToNumList b ↔ a = b := by
  cases a <;> cases b <;> simp [regImmToNumList, wordToNumUnique]

private def replaceDestination {width : Nat} [NeZero width]
    (a : HolArith width) (d : Nat) : HolArith width :=
  match a with
  | .binop op _ src ri => .binop op d src ri
  | .shift sh _ src ri => .shift sh d src ri
  | .div _ src1 src2 => .div d src1 src2
  | a => a

private theorem keyDestination {width : Nat} [NeZero width] (a1 a2 : HolArith width)
    (h : canMemArith a1 = true ∧ arithToNumList a1 = arithToNumList a2) :
    a2 = replaceDestination a1 (firstRegOfArith a2) := by
  cases a1 <;> cases a2 <;>
    simp_all [canMemArith, arithToNumList, firstRegOfArith, replaceDestination,
      arithOpToNumEq, shiftToNumEq, regImmKeyEq, Nat.add_right_cancel_iff]

private theorem replaceCanMem {width : Nat} [NeZero width] (a : HolArith width) (d : Nat) :
    canMemArith (replaceDestination a d) = canMemArith a := by
  cases a with
  | binop op dst src ri => cases ri <;> rfl
  | shift sh dst src ri => cases ri <;> rfl
  | _ => rfl

private theorem replaceReads {width : Nat} [NeZero width] (a : HolArith width) (d : Nat) :
    arithReads (replaceDestination a d) = arithReads a := by
  cases a with
  | binop op dst src ri => cases ri <;> rfl
  | shift sh dst src ri => cases ri <;> rfl
  | _ => rfl

private theorem setVarValueEq {width : Nat} [NeZero width] {C : Type} {F : Type}
    (d : Nat) (v1 v2 : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : setVar d v1 s = setVar d v2 s) : v1 = v2 := by
  exact (insertEq d v1 v2 s.locals).mp (congrArg (fun st => st.locals) h)

private theorem resultTransfer {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i1 i2 : WordLangInst (BitVec width)) (d1 d2 : Nat)
    (value : Option (WordLocW width)) (s : WordSemStateFiniteExact width C F)
    (w : WordLocW width)
    (hi1 : inst i1 s = value.map (fun v => setVar d1 v s))
    (hi2 : inst i2 s = value.map (fun v => setVar d2 v s))
    (h : evaluate (.inst i1) s = (none, setVar d1 w s)) :
    evaluate (.inst i2) s = (none, setVar d2 w s) := by
  cases value with
  | none => simp [evaluate, hi1] at h
  | some v =>
    have hs : setVar d1 v s = setVar d1 w s := by
      simpa [evaluate, hi1] using h
    have hv := setVarValueEq d1 v w s hs
    subst v
    simp [evaluate, hi2]

private theorem assignMap {width : Nat} [NeZero width] {C : Type} {F : Type}
    (d : Nat) (exp : WordLangExpHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    assign d exp s = (wordExp s exp).map (fun v => setVar d v s) := by
  cases h : wordExp s exp <;> simp [assign, h]

private theorem binopTransfer {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : BinOp) (src : Nat) (ri : HolRegImm width) (d1 d2 : Nat)
    (s : WordSemStateFiniteExact width C F) (w : WordLocW width)
    (h : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop op d1 src ri)))) s =
      (none, setVar d1 w s)) :
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop op d2 src ri)))) s =
      (none, setVar d2 w s) := by
  cases ri with
  | reg r =>
    exact resultTransfer _ _ d1 d2 (wordExp s (.op op [.var src, .var r])) s w
      (by simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, assignMap])
      (by simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, assignMap]) h
  | imm v =>
    exact resultTransfer _ _ d1 d2 (wordExp s (.op op [.var src, .const v])) s w
      (by simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, assignMap])
      (by simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, assignMap]) h

private theorem shiftTransfer {width : Nat} [NeZero width] {C : Type} {F : Type}
    (sh : Shift) (src : Nat) (ri : HolRegImm width) (d1 d2 : Nat)
    (s : WordSemStateFiniteExact width C F) (w : WordLocW width)
    (h : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift sh d1 src ri)))) s =
      (none, setVar d1 w s)) :
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift sh d2 src ri)))) s =
      (none, setVar d2 w s) := by
  cases ri with
  | reg r =>
    exact resultTransfer _ _ d1 d2 (wordExp s (.shift sh (.var src) (.var r))) s w
      (by simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, assignMap])
      (by simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, assignMap]) h
  | imm v =>
    exact resultTransfer _ _ d1 d2 (wordExp s (.shift sh (.var src) (.const v))) s w
      (by simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, assignMap])
      (by simp [HolArith.toWordLangArith, HolRegImm.toWordRegImm, inst, assignMap]) h

private theorem divTransfer {width : Nat} [NeZero width] {C : Type} {F : Type}
    (src1 src2 d1 d2 : Nat) (s : WordSemStateFiniteExact width C F) (w : WordLocW width)
    (h : evaluate (.inst (.arith (.div d1 src1 src2))) s = (none, setVar d1 w s)) :
    evaluate (.inst (.arith (.div d2 src1 src2))) s = (none, setVar d2 w s) := by
  let value : Option (WordLocW width) :=
    match WordSemStateFiniteExact.getVars [src2, src1] s with
    | some [.word q, .word v] => if q ≠ 0 then some (.word (v.sdiv q)) else none
    | _ => none
  apply resultTransfer _ _ d1 d2 value s w _ _ h
  all_goals
    simp only [inst]
    split <;> simp_all [value, Option.map]
    split <;> simp_all

/-- Canonical finite-support state roundtrip, for the state fields named by
the arithmetic simulation. This reuses the reviewed owning carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Full original key-to-evaluation simulation, including eligibility and reads.
The original `can_mem_arith` guard excludes multi-output arithmetic. Native Asm
codecs only translate corresponding constructors. The state retains the reviewed
finite-support `fpRegs`/`store` representation and positive-width words. The
faithful evaluator inherits the IEEE rational-cut assumption (SOUNDNESS item 8);
this theorem adds no further evaluation, state, or operand hypothesis. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem arithKeysEq {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a1 a2 : HolArith width)
    (h : canMemArith a1 = true ∧ arithToNumList a1 = arithToNumList a2) :
    canMemArith a2 = true ∧ arithReads a2 = arithReads a1 ∧
    ∀ (s : WordSemStateFiniteExact width C F) (w : WordLocW width),
      evaluate (.inst (.arith (HolArith.toWordLangArith a1))) s =
        (none, setVar (firstRegOfArith a1) w s) →
      evaluate (.inst (.arith (HolArith.toWordLangArith a2))) s =
        (none, setVar (firstRegOfArith a2) w s) := by
  obtain ⟨d, rfl⟩ : ∃ d, a2 = replaceDestination a1 d :=
    ⟨firstRegOfArith a2, keyDestination a1 a2 h⟩
  refine ⟨(replaceCanMem a1 d).trans h.1, replaceReads a1 d, ?_⟩
  intro s w heval
  have hc := h.1
  cases a1 with
  | binop op dst src ri => exact binopTransfer op src ri dst d s w heval
  | shift sh dst src ri => exact shiftTransfer sh src ri dst d s w heval
  | div dst src1 src2 => exact divTransfer src1 src2 dst d s w heval
  | _ => simp [canMemArith] at hc

end Flapjack.Compiler.Backend.WordCse
