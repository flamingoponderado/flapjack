module

public import Flapjack.Compiler.Backend.StackRemove.Proofs.RelationLaws
public import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

@[expose] public section

/-! Native register relation laws from stack_removeProofScript.sml. Updates
use the evaluator's canonical finite maps and preserve the complete relation,
including reserved pointer registers and the full separated target heap. -/
namespace Flapjack.Compiler.Backend.StackRemove.StateUpdates
open Flapjack

/-- Flapjack-specific canonical state codec witness, reexporting the actual
carrier's genuine broad/exact roundtrips; it has no standalone HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Same arbitrary Word or Loc assignment below the original reserved register
bound preserves every conjunct of the full native state relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_set_var"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelSetVar {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register : Nat)
    (value : WordLocW width) (source target : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧ register < pointer) :
    stateRelHOL jump bounds pointer (StackSemStateOps.setVar register value source)
      (StackSemStateOps.setVar register value target) := by
  rcases hypothesis with ⟨relation, below⟩
  have pointerNe : pointer ≠ register := by omega
  have baseNe : pointer + 1 ≠ register := by omega
  have heapNe : pointer + 2 ≠ register := by omega
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  have lookupPreserved : ∀ query, query < pointer →
      (target.regs.updateEq (register, value)).lookup query =
        (source.regs.updateEq (register, value)).lookup query := by
    intro query queryBelow
    by_cases same : query = register
    · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same, ite_true]
    · simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same, ite_false] using h18 query queryBelow
  simp only [stateRelHOL, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL, pointerNe, baseNe, heapNe, ite_false]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, lookupPreserved, h19, h20, h21, h22, h23, h24, h25⟩

/-- Exact equality of the original fixed-width FP lookup; no integer-register
bound is needed because the full FP maps are equal in the relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_get_fp_var"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelGetFpVar {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    StackSemStateOps.getFpVar register source = StackSemStateOps.getFpVar register target := by
  have fpEqual : target.fpRegs = source.fpRegs := relation.2.2.2.2.2.2.2.2.2.2.2.1
  exact congrArg (fun map => map.lookup register) fpEqual.symm

/-- Same arbitrary fixed 64-bit FP value assignment preserves the complete
relation. This changes no floating-point execution equation or rounding mode. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_set_fp_var"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelSetFpVar {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register : Nat)
    (value : BitVec 64) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer (StackSemStateOps.setFpVar register value source)
      (StackSemStateOps.setFpVar register value target) := by
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  simp only [stateRelHOL, StackSemStateOps.setFpVar]
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, congrArg (fun map => map.updateEq (register, value)) h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩

/-- Canonical roundtrip for the imported actual state carrier; representation
infrastructure rather than an assumption about any update run. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Flapjack helper: two finite-support maps with the same lookup are equal,
because the support field is a proposition. Has no separate HOL original. -/
private theorem holFmapExactExt {α β : Type} {left right : HolFiniteMapExact α β}
    (h : ∀ k, left.lookup k = right.lookup k) : left = right := by
  obtain ⟨lleft, pleft⟩ := left
  obtain ⟨lright, pright⟩ := right
  have hfun : lleft = lright := funext h
  subst hfun
  rfl

/-- HOL `with_same_clock` (`stack_removeProofScript.sml`): rewriting the clock
with its own value leaves the state unchanged. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "with_same_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem withSameClock {width : Nat} [NeZero width] {C F : Type}
    (x : StackSemStateFiniteExact width C F) : { x with clock := x.clock } = x := rfl

/-- HOL `set_var_set_var` (`stack_removeProofScript.sml`): a second assignment
to the same register overwrites the first. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "set_var_set_var"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVarSetVar {width : Nat} [NeZero width] {C F : Type} (x : Nat)
    (y z : WordLocW width) (w : StackSemStateFiniteExact width C F) :
    StackSemStateOps.setVar x y (StackSemStateOps.setVar x z w) =
      StackSemStateOps.setVar x y w := by
  have hregs : (w.regs.updateEq (x, z)).updateEq (x, y) = w.regs.updateEq (x, y) := by
    apply holFmapExactExt
    intro key
    by_cases h : key = x
    · simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, h]
    · simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, h]
  simp only [StackSemStateOps.setVar]
  rw [hregs]

/-- HOL `get_var_set_var_same` (`stack_removeProofScript.sml`): reading the
register just assigned yields the assigned value. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_var_set_var_same"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarSetVarSame {width : Nat} [NeZero width] {C F : Type} (x : Nat)
    (y : WordLocW width) (z : StackSemStateFiniteExact width C F) :
    StackSemStateOps.getVar x (StackSemStateOps.setVar x y z) = some y := by
  simp [StackSemStateOps.getVar, StackSemStateOps.setVar, HolFiniteMapExact.updateEq,
    FUPDATE_HOL]

/-- HOL `get_var_set_var` (`stack_removeProofScript.sml`): reading a register
after an assignment selects the new value exactly when the registers agree. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "get_var_set_var"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarSetVar {width : Nat} [NeZero width] {C F : Type} (x x' : Nat)
    (y : WordLocW width) (z : StackSemStateFiniteExact width C F) :
    StackSemStateOps.getVar x (StackSemStateOps.setVar x' y z) =
      if x = x' then some y else StackSemStateOps.getVar x z := by
  simp [StackSemStateOps.getVar, StackSemStateOps.setVar, HolFiniteMapExact.updateEq,
    FUPDATE_HOL]

end Flapjack.Compiler.Backend.StackRemove.StateUpdates
