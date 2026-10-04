import Flapjack.Compiler.Backend.WordToStack.Proofs.CallDest
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

namespace Flapjack.WordToStackProofs.ConstantInstruction
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness



/-- Full original constant-instruction relation transport (6743–6756).
HOL stackLang's const_inst overload is literal Inst(Const register word).
No target run, output relation or successful-instruction premise is supplied.
Canonical map and positive word carriers are explicitly qualified.
-/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateConstInst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame extra : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (word : BitVec width)
    (related : stateRel ac k f frame source target lens extra) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (.inst (.const (k + 1) word), target) = (none, post) ∧
      target.clock = post.clock ∧ stateRel ac k f frame source post lens extra ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace ∧
      StackSemStateOps.getVar (k + 1) post = some (.word word) := by
  refine ⟨StackSemStateOps.setVar (k + 1) (.word word) target, ?_, rfl,
    CallDest.stateRel_setVar_of_ge (k + 1) (by omega) (.word word) related,
    rfl, rfl, ?_⟩
  · simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp]
  · simp [StackSemStateOps.getVar, StackSemStateOps.setVar,
      HolFiniteMapExact.updateEq, FUPDATE_HOL]

/-- Full original unconditional clock equation (6758–6765), retaining the
whole result and post-state for every initial state, register, word and clock.
Canonical map and positive word carriers are explicitly qualified.
-/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateConstInstClock {width : Nat} [NeZero width] {C F : Type}
    (register clock : Nat) (word : BitVec width) (target : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.inst (.const register word), {target with clock := clock}) =
      (StackSemEvaluate.evaluate (.inst (.const register word), target)).map
        id (fun post => {post with clock := clock}) := by
  simp only [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, Option.join_some]
  rfl

end Flapjack.WordToStackProofs.ConstantInstruction
