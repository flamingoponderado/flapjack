import Flapjack.Compiler.Backend.ClosInterp.Proofs.PrimitiveRelation

/-! Thunk-force simulation for the proof-side evaluator. The semantics and
finite-map carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Replacing both reference stores by the same store preserves the relation. -/
theorem stateRel_withRefs {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (refs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) :
    StateRel { source with refs := refs } { target with refs := refs } := by
  rcases related with ⟨⟨safe, sc, tc, maxEq, maxPositive, clock, ffi, globals, _, compiler, oracle⟩, installed⟩
  exact ⟨⟨safe, sc, tc, maxEq, maxPositive, clock, ffi, globals, rfl, compiler, oracle⟩, installed⟩

/-- Thunk inspection is identical in related states. -/
theorem destThunk_stateRel {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (values : List ClosSem.Value) :
    ClosSem.destThunk values source.refs = ClosSem.destThunk values target.refs := by
  rw [related.1.2.2.2.2.2.2.2.2.1]

/-- A thunk update produces the same reference store in related states. -/
theorem updateThunk_stateRel {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) (targets values : List ClosSem.Value)
    (refs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (run : ClosSem.updateThunk targets source.refs values = some refs) :
    ClosSem.updateThunk targets target.refs values = some refs ∧
      StateRel { source with refs := refs } { target with refs := refs } := by
  constructor
  · rw [← related.1.2.2.2.2.2.2.2.2.1]
    exact run
  · exact stateRel_withRefs source target related refs

/-- Thunk forcing preserves the state relation, assuming simulations for
the argument list and the forced thunk computation. -/
theorem evaluate_force_simulation_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ∀ (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (result, sourceFinal) → StateRel source target →
      result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate args env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (forceIH : ∀ (value : ClosSem.Value) (forceSource forceTarget forceFinal : ClosSem.State C F)
      (forceResult : Result (List ClosSem.Value) ClosSem.Value),
      forceSource.clock ≤ source.clock →
      ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] forceSource = (forceResult, forceFinal) →
      StateRel forceSource forceTarget → forceResult ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value]
          { forceTarget with clock := extra + forceTarget.clock } = (forceResult, targetFinal) ∧
        StateRel forceFinal targetFinal)
    (related : StateRel source target)
    (run : ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env { target with clock := extra + target.clock } =
        (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases argsRun : ClosSem.evaluate args env source with
  | mk argsResult sourceMid =>
    have bound : sourceMid.clock ≤ source.clock := by
      have h := ClosSem.evaluate_clock_le args env source
      simpa [argsRun] using h
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at run
    have argsNotTypeError : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨argsExtra, targetMid, targetArgs, midRel⟩ := argsIH source target sourceMid argsResult argsRun related argsNotTypeError
    cases argsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨argsExtra, targetMid, ?_, midRel⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
    | val values =>
      dsimp only at run
      have inspectEq := destThunk_stateRel sourceMid targetMid midRel values
      cases inspected : ClosSem.destThunk values sourceMid.refs with
      | badRef | notThunk =>
        simp [inspected] at run
        exact (notTypeError run.1.symm).elim
      | isThunk mode value =>
        cases mode with
        | evaluated =>
          simp [inspected] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨argsExtra, targetMid, ?_, midRel⟩
          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
          simp [← inspectEq, inspected]
        | notEvaluated =>
          rw [inspected] at run
          dsimp only at run
          cases forceRun : ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] sourceMid with
          | mk forceResult sourceLast =>
            rw [forceRun] at run
            have forceNotTypeError : forceResult ≠ .err (.abort .typeError) := by
              intro bad
              subst forceResult
              simp at run
              exact notTypeError run.1.symm
            obtain ⟨forceExtra, targetLast, targetForce, lastRel⟩ :=
              forceIH value sourceMid targetMid sourceLast forceResult bound forceRun midRel forceNotTypeError
            have shiftedArgs := ClosSem.evaluate_addClock.1 args env
              { target with clock := argsExtra + target.clock } targetMid (.val values) forceExtra targetArgs (by simp)
            let enlarged := { target with clock := (argsExtra + target.clock) + forceExtra }
            let enlargedMid := { targetMid with clock := targetMid.clock + forceExtra }
            have targetArgs' : ClosSem.evaluate args env enlarged = (.val values, enlargedMid) := by
              simpa [enlarged, enlargedMid] using shiftedArgs
            have targetForce' : ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] enlargedMid =
                (forceResult, targetLast) := by
              simpa [enlargedMid, Nat.add_comm] using targetForce
            have inspectTarget : ClosSem.destThunk values enlargedMid.refs = .isThunk .notEvaluated value := by
              simpa [enlargedMid, ← inspectEq] using inspected
            cases forceResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨argsExtra + forceExtra, targetLast, ?_, lastRel⟩
              have targetRun : ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env enlarged =
                  (.err error, targetLast) := by
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs']
                simp only [inspectTarget, targetForce']
              simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun
            | val forcedValues =>
              dsimp only at run
              cases updated : ClosSem.updateThunk values sourceLast.refs forcedValues with
              | none =>
                simp [updated] at run
                exact (notTypeError run.1.symm).elim
              | some refs =>
                simp [updated] at run
                rcases run with ⟨rfl, rfl⟩
                obtain ⟨targetUpdate, updatedRel⟩ := updateThunk_stateRel sourceLast targetLast lastRel values forcedValues refs updated
                refine ⟨argsExtra + forceExtra, { targetLast with refs := refs }, ?_, updatedRel⟩
                have targetRun : ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env enlarged =
                    (.val forcedValues, { targetLast with refs := refs }) := by
                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs']
                  simp only [inspectTarget, targetForce', targetUpdate]
                simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun

end Flapjack.Compiler.Backend.ClosInterp
