import Flapjack.Compiler.Backend.Semantics.StackSem.State

/-! Counterpart of StackSem's code lookup and clock-clamping prerequisites.
The payload of the code tree and the result component of the clock pair retain
HOL's polymorphism. No evaluator or production-path refinement is supplied. -/
namespace Flapjack.StackSemControl

/-- Canonical finite-support state roundtrip re-export; infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Direct code label lookup or indirect lookup through a zero-offset Loc.
    The code tree is sptree, not a finite-support fmap translation. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "find_code_def"
  (fmap_as_finite_support_relation := [regs]) (words_as_type_indexed_bitvec)]
def findCode {width : Nat} [NeZero width] {α : Type}
    (target : Sum Nat Nat) (regs : HolFiniteMapExact Nat (WordLocW width))
    (code : Spt α) : Option α :=
  match target with
  | .inl label => sptLookup label code
  | .inr reg =>
      match regs.lookup reg with
      | some (.loc label 0) => sptLookup label code
      | _ => none

/-- Clamp only the returned state's clock to the input/returned minimum. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "fix_clock_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def fixClock {width : Nat} [NeZero width] {C F R : Type}
    (s : StackSemStateFiniteExact width C F)
    (x : R × StackSemStateFiniteExact width C F) : R × StackSemStateFiniteExact width C F :=
  (x.1, { x.2 with clock := min s.clock x.2.clock })

/-- HOL's local clock bound, retaining its sole successful-pair equality premise. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "fix_clock_IMP"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem fixClockImp {width : Nat} [NeZero width] {C F R : Type}
    (s : StackSemStateFiniteExact width C F)
    (x : R × StackSemStateFiniteExact width C F) (res : R)
    (s1 : StackSemStateFiniteExact width C F)
    (h : fixClock s x = (res, s1)) : s1.clock ≤ s.clock := by
  have hc := congrArg (fun pair => pair.2.clock) h
  change min s.clock x.2.clock = s1.clock at hc
  rw [← hc]
  exact Nat.min_le_left _ _

end Flapjack.StackSemControl

namespace Flapjack.StackSemControl

/-- HOL `check_store_consts_opt` (`cakeml/compiler/backend/semantics/stackSemScript.sml:743`):
    the `None` stub is always admissible, and a `some n` stub demands that label
    `n` names exactly `Seq (StoreConsts t1 t2 NONE) (Return 0)`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "check_store_consts_opt_def"
  (words_as_type_indexed_bitvec)]
def checkStoreConstsOpt {width : Nat} [NeZero width] (t1 t2 : Nat)
    (stub : Option Nat) (code : Spt (Compiler.Backend.StackLang.HolProg width)) : Prop :=
  match stub with
  | none => True
  | some n =>
      sptLookup n code =
        some (.seq (.storeConsts t1 t2 none) (.ret 0))

end Flapjack.StackSemControl
