import Flapjack.Compiler.Backend.StackRemove.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps

/-! Source-local relation laws used by StackRemove's faithful evaluation
simulation. The states and operations are the imported evaluator's carriers. -/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack
namespace RelationLaws

theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source get_var is preserved for every register below the original bound. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_get_var"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelGetVar {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧ register < pointer) :
    StackSemStateOps.getVar register source = StackSemStateOps.getVar register target := by
  have relation := hypothesis.1
  simp only [stateRelHOL] at relation
  exact (relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 register hypothesis.2).symm

/-- Updating both clocks to any common value preserves the full relation. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_with_clock"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelWithClock {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer clock : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer {source with clock := clock} {target with clock := clock} := by
  simp only [stateRelHOL] at relation ⊢
  rcases relation with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, True.intro, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩

/-- The original decrement operation truncates at zero on both states. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_IMP"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelDecClock {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer (StackSemStateOps.decClock source)
      (StackSemStateOps.decClock target) := by
  have clockEq := relation
  simp only [stateRelHOL] at clockEq
  have equalClocks := clockEq.2.2.2.2.2.2.2.2.1
  simpa only [StackSemStateOps.decClock, equalClocks] using
    stateRelWithClock jump bounds pointer (source.clock - 1) source target relation

/-- Complete source constant-field conclusion, including both transport equations. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_const"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelConst {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    target.codeBuffer = source.codeBuffer ∧ target.shMdomain = source.shMdomain ∧
    target.useStack = false ∧ source.useStack = true ∧ target.ffi = source.ffi ∧
    target.compileOracle = (fun index =>
      let oracle := source.compileOracle index
      (oracle.1, oracle.2.1.map (progComp jump bounds pointer), oracle.2.2)) ∧
    source.compile = (fun config program =>
      target.compile config (program.map (progComp jump bounds pointer))) := by
  simp only [stateRelHOL] at relation
  exact ⟨relation.2.2.2.2.2.2.2.2.2.2.2.2.1, relation.2.2.2.2.2.2.2.2.2.2.2.2.2.1, relation.2.2.1, relation.1, relation.2.2.2.2.2.2.2.2.2.1, relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

end RelationLaws
end Flapjack.Compiler.Backend.StackRemove
