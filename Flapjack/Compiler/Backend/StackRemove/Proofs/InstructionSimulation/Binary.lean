import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation.Atoms

namespace Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.Binary
open Flapjack Compiler.Encoders.Asm

/-- Flapjack proof factoring of HOL's assignment argument, without a separately
named HOL theorem. All register/expression bounds here are derived in each
instruction case from its original reg_bound_inst premise. -/
theorem stateRelAssign {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register : Nat)
    (expression : WordLangExpHOL (BitVec width))
    (source target postSource : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (registerBound : register < pointer) (expressionBound : StackProps.regBoundExp expression pointer)
    (run : StackSemExpressions.assign register expression source = some postSource) :
    ∃ postTarget, StackSemExpressions.assign register expression target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  cases valueEq : StackSemExpressions.wordExp source expression with
  | none => simp [StackSemExpressions.assign, valueEq] at run
  | some value =>
    have targetEq := ExpressionSimulation.stateRelWordExp jump bounds pointer source target
      expression value ⟨relation, expressionBound, valueEq⟩
    simp only [StackSemExpressions.assign, valueEq, Option.some.injEq] at run
    subst postSource
    refine ⟨StackSemStateOps.setVar register (.word value) target, ?_, ?_⟩
    · simp only [StackSemExpressions.assign, targetEq]
    · exact StateUpdates.stateRelSetVar jump bounds pointer register (.word value) source target
        ⟨relation, registerBound⟩

/-- Canonical actual-state roundtrip witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine full Shift instruction case for every shift and Reg/Imm operand. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_inst"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelInstShift {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer destination input : Nat)
    (operator : Shift) (right : HolRegImm width)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst (.arith (.shift operator destination input right)) pointer ∧
      StackSemInst.instHOL (.arith (.shift operator destination input right)) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.arith (.shift operator destination input right)) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  simp only [StackProps.regBoundInst] at bound
  simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, Option.join_some] at run ⊢
  apply stateRelAssign jump bounds pointer destination _ source target postSource relation bound.2.1 _ run
  cases right <;> simp only [StackProps.regBoundExp] <;> exact ⟨bound.1, bound.2.2⟩

/-- Genuine full Binop case, retaining the special Or register-copy path for
both Word and Loc values and all general binary operations. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "state_rel_inst"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelInstBinop {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer destination input : Nat)
    (operator : BinOp) (right : HolRegImm width)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst (.arith (.binop operator destination input right)) pointer ∧
      StackSemInst.instHOL (.arith (.binop operator destination input right)) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.arith (.binop operator destination input right)) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  cases right with
  | imm word =>
    simp only [StackProps.regBoundInst] at bound
    simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
      Bool.and_false, Bool.false_eq_true, ite_false, Option.join_some] at run ⊢
    apply stateRelAssign jump bounds pointer destination _ source target postSource relation bound.2.1 _ run
    simp only [StackProps.regBoundExp, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, and_true]
    exact bound.1
  | reg second =>
    simp only [StackProps.regBoundInst] at bound
    simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, Option.join_some] at run ⊢
    by_cases guard : (operator == .or && second == input) = true
    · simp only [guard, ite_true] at run ⊢
      have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer input source target
        ⟨relation, bound.1⟩
      change source.regs.lookup input = target.regs.lookup input at lookupEq
      cases lookup : source.regs.lookup input with
      | none => simp [lookup] at run
      | some value =>
        simp only [lookup, Option.some.injEq] at run
        subst postSource
        refine ⟨StackSemStateOps.setVar destination value target, ?_, ?_⟩
        · simp only [← lookupEq, lookup]
        · exact StateUpdates.stateRelSetVar jump bounds pointer destination value source target
            ⟨relation, bound.2.1⟩
    · simp only [guard] at run ⊢
      apply stateRelAssign jump bounds pointer destination _ source target postSource relation bound.2.1 _ run
      simp only [StackProps.regBoundExp, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      exact ⟨bound.1, bound.2.2⟩

end Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.Binary
