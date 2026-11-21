module

public import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

/-! The opening list and state lemmas of `stack_removeProofScript.sml`
(lines 58-97) and its conditional-pushing rewrite `push_if` (3034-3039). The
StackSem state operations are the reviewed `get_var_def`/`set_var_def` ports on
the canonical finite-support state carrier. -/
namespace Flapjack.Compiler.Backend.StackRemove.Preliminaries
open Flapjack Flapjack.StackSemStateOps

/-- Same-module re-export of the canonical StackSem state roundtrip;
Flapjack representation infrastructure with no HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Every index below the length splits the list into a prefix of that
length and a suffix. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "LESS_LENGTH_IMP_APPEND"]
theorem lessLengthImpAppend {α : Type} :
    ∀ (xs : List α) (n : Nat), n < xs.length → ∃ ys zs, xs = ys ++ zs ∧ ys.length = n := by
  intro xs n bound
  exact ⟨xs.take n, xs.drop n, (List.take_append_drop n xs).symm,
    List.length_take_of_le (Nat.le_of_lt bound)⟩

/-- Updating the clock to its own value leaves the state unchanged. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "with_same_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem withSameClock {width : Nat} [NeZero width] {C F : Type} :
    ∀ x : StackSemStateFiniteExact width C F, { x with clock := x.clock } = x := by
  intro x
  rfl

/-- A second register write overrides the first. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "set_var_set_var"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVar_setVar {width : Nat} [NeZero width] {C F : Type} (x : Nat) (y z : WordLocW width)
    (w : StackSemStateFiniteExact width C F) :
    setVar x y (setVar x z w) = setVar x y w := by
  simp only [setVar]
  congr 1
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL]
  split <;> rfl

/-- Reading a register just written returns the written value. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_var_set_var_same"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVar_setVar_same {width : Nat} [NeZero width] {C F : Type} (x : Nat) (y : WordLocW width)
    (z : StackSemStateFiniteExact width C F) :
    getVar x (setVar x y z) = some y := by
  simp [getVar, setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL]

/-- Reading a register after a write returns the written value at the same
register and the previous value elsewhere. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_var_set_var"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVar_setVar {width : Nat} [NeZero width] {C F : Type} (x x' : Nat) (y : WordLocW width)
    (z : StackSemStateFiniteExact width C F) :
    getVar x (setVar x' y z) = if x = x' then some y else getVar x z := by
  simp [getVar, setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL]

/-- Pushing a function application through a conditional, in its argument
and in its function position. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "push_if"]
theorem pushIf {α β : Type} (b : Bool) (f g : β → α) (x y : β) :
    (if b then f x else f y) = f (if b then x else y) ∧
      (if b then f x else g x) = (if b then f else g) x := by
  constructor <;> split <;> rfl

end Flapjack.Compiler.Backend.StackRemove.Preliminaries
