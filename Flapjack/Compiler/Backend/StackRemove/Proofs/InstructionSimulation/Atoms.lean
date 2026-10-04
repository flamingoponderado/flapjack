import Flapjack.Compiler.Backend.StackRemove.Proofs.StateUpdates
import Flapjack.Compiler.Backend.StackRemove.Proofs.ExpressionSimulation
import Flapjack.Compiler.Backend.Semantics.StackSem.Inst

namespace Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.Atoms
open Flapjack

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine Skip case of the full instruction theorem, retaining all three
original hypotheses and its existential successful target/full relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelInstSkip {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst (.skip : Compiler.Encoders.Asm.HolInst width) pointer ∧
      StackSemInst.instHOL .skip source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL .skip target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, _bound, run⟩
  simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    Option.join_some, Option.some.injEq] at run
  subst postSource
  exact ⟨target, rfl, relation⟩

/-- Genuine Const case of the full instruction theorem. Native assignment
updates the same bounded register in both actual states, with no supplied
post-state relation or target execution. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelInstConst {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register : Nat)
    (value : BitVec width) (source target postSource : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      StackProps.regBoundInst (.const register value) pointer ∧
      StackSemInst.instHOL (.const register value) source = some postSource) :
    ∃ postTarget, StackSemInst.instHOL (.const register value) target = some postTarget ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, bound, run⟩
  simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, Option.join_some,
    Option.some.injEq] at run
  subst postSource
  refine ⟨StackSemStateOps.setVar register (.word value) target, ?_, ?_⟩
  · simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
      StackSemExpressions.assign, StackSemExpressions.wordExp, Option.join_some]
  · exact StateUpdates.stateRelSetVar jump bounds pointer register (.word value) source target
      ⟨relation, bound⟩

end Flapjack.Compiler.Backend.StackRemove.InstructionSimulation.Atoms
