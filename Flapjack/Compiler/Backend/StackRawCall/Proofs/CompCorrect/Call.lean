import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Return

namespace Flapjack.Compiler.Backend.StackRawCall.CallAssembly
open Flapjack Flapjack.Compiler.Backend.StackLang
open IfCase CallCase

/-- Original Call evaluate_ind hypotheses split only on the native optional
return continuation. Unused components of the paired motives are omitted.
This abbreviation is Flapjack notation, not a separate HOL declaration. -/
abbrev CallIH {width : Nat} [NeZero width] (C F : Type)
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) : Prop :=
  match ret with
  | none => TailCalleeIH C F dest handler source
  | some (body, link, l1, l2) =>
      ReturnCalleeIH C F dest link l1 l2 source ∧
      ReturnContinuationIH C F body dest link l1 l2 source ∧
      ExceptionContinuationIH C F handler dest link l1 l2 source

/-- Canonical roundtrip of the actual imported evaluator-state owner.
Flapjack qualifier infrastructure with no duplicate carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original Call case409-518. All optional return/handler and
direct/indirect destination branches retain the original source evaluation,
nonError and literal state relation premises plus only the actual guarded
recursive hypotheses. Both original existential conclusions and timeout/
Halt Word2 stackspace exceptions remain. No target execution, successful body
or final relation is assumed. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCall {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (induction : CallIH C F ret dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call ret dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call ret dest handler)) info target post result ∧
    SimulationResult (comp info (.call ret dest handler)) info target post result := by
  cases ret with
  | none => exact compCorrectCallTail dest handler info source target post result induction hypothesis
  | some triple =>
      obtain ⟨body, link, l1, l2⟩ := triple
      obtain ⟨calleeIH, returnIH, exceptionIH⟩ := induction
      exact compCorrectCallReturn body link l1 l2 dest handler info source target post result
        calleeIH returnIH exceptionIH hypothesis

end Flapjack.Compiler.Backend.StackRawCall.CallAssembly
