import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineEvaluation

/-! The thunk-force case of BVL inlining simulation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps Flapjack.SemanticPrimitivesHOL

namespace InlineForceCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InlineForceCarrier

/-- The Force/Force expression-relation case of the inlining simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_force {C F : Type} (limit location index : Nat)
    (env : List BvlSem.Value)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (bodyIH : ∀ (body body' : Bvl.Exp) (values : List BvlSem.Value)
      (thunk value : BvlSem.Value)
      (last : State (Spt (Nat × Bvl.Exp) × C) F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      env[index]? = some thunk → destThunk thunk source.refs = .isThunk .notEvaluated value →
      findCode (some location) [thunk, value] source.code = some (values, body) →
      source.clock ≠ 0 →
      ExpRel source.code [body] [body'] →
      evaluateTuple ([body], values, decClock 1 source) = (result, last) →
      result ≠ .err (.abort .typeError) →
      ∃ targetLast, evaluateTuple ([body'], values, decClock 1 target) = (result, targetLast) ∧
        inStateRel limit last targetLast)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (_expressions : ExpRel source.code [.force location index] [.force location index])
    (run : evaluateTuple ([.force location index], env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.force location index], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  have refs := related.2.1
  have clocks := related.2.2.1
  cases valueAt : env[index]? with
  | none =>
    simp [evaluateTuple, evaluate, valueAt] at run
    exact False.elim (notTypeError run.1.symm)
  | some thunk =>
    cases thunkAt : destThunk thunk source.refs with
    | badRef =>
      simp [evaluateTuple, evaluate, valueAt, thunkAt] at run
      exact False.elim (notTypeError run.1.symm)
    | notThunk =>
      simp [evaluateTuple, evaluate, valueAt, thunkAt] at run
      exact False.elim (notTypeError run.1.symm)
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp [evaluateTuple, evaluate, valueAt, thunkAt] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, by simp [evaluateTuple, evaluate, valueAt, refs, thunkAt], related⟩
      | notEvaluated =>
        cases find : findCode (some location) [thunk, value] source.code with
        | none =>
          simp [evaluateTuple, evaluate, valueAt, thunkAt, find] at run
          exact False.elim (notTypeError run.1.symm)
        | some pair =>
          obtain ⟨values, body⟩ := pair
          obtain ⟨body', targetFind, bodyRel⟩ :=
            inStateRel_findCode limit source target related (some location) [thunk, value] values body find
          by_cases zero : source.clock = 0
          · have targetZero : target.clock = 0 := clocks.trans zero
            simp [evaluateTuple, evaluate, valueAt, thunkAt, find, zero] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ target with clock := 0 }, ?_, ?_⟩
            · simp [evaluateTuple, evaluate, valueAt, refs, thunkAt, targetFind, targetZero]
            · simpa [inStateRel, zero, targetZero] using related
          · have targetNonzero : target.clock ≠ 0 := by simpa [clocks] using zero
            simp [evaluateTuple, evaluate, valueAt, thunkAt, find, zero] at run
            obtain ⟨targetFinal, targetRun, finalRel⟩ :=
              bodyIH body body' values thunk value final result valueAt thunkAt find zero bodyRel run notTypeError
            refine ⟨targetFinal, ?_, finalRel⟩
            simpa [evaluateTuple, evaluate, valueAt, refs, thunkAt, targetFind, targetNonzero] using targetRun

end Flapjack.Compiler.Backend.BvlInline.Proofs
