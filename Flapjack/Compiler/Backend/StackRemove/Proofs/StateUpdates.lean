import Flapjack.Compiler.Backend.StackRemove.Proofs.RelationLaws
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

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

end Flapjack.Compiler.Backend.StackRemove.StateUpdates
