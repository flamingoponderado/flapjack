import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyRefs
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateClock
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL

/-! Reference-domain growth during BVL evaluation. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem

namespace EvalRefsCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end EvalRefsCarrier

/-- Inclusion of reference domains, stated at the canonical lookup carrier. -/
def refsSubset {C F D G : Type} (before : State C F) (after : State D G) : Prop :=
  ∀ key, before.refs.lookup key ≠ none → after.refs.lookup key ≠ none

/-- Domain inclusion composes. -/
theorem refsSubset_trans {C F D G E H : Type} {a : State C F} {b : State D G} {c : State E H}
    (ab : refsSubset a b) (bc : refsSubset b c) : refsSubset a c :=
  fun key present => bc key (ab key present)

/-- Every evaluation preserves previously allocated reference keys. This
proof-side invariant remains untagged until source statement review. -/
theorem evaluate_refs_mono {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (state : State C F) : refsSubset state (evaluate expressions env state).2 := by
  have allRanks : ∀ clock weight : Nat, ∀ (expressions : List Bvl.Exp)
      (env : List Value) (state : State C F),
      state.clock = clock → expsWeight expressions = weight →
      refsSubset state (evaluate expressions env state).2 := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List Bvl.Exp) (env : List Value) (state : State C F),
            state.clock ≤ clock → expsWeight expressions < weight →
            refsSubset state (evaluate expressions env state).2 := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
          · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List Bvl.Exp) (env : List Value) (state : State C F),
            state.clock < clock → refsSubset state (evaluate expressions env state).2 := by
          intro expressions env state clockLt
          exact clockIH state.clock clockLt (expsWeight expressions) expressions env state rfl rfl
        intro expressions env state stateClock measure
        cases expressions with
        | nil => simp [evaluate, refsSubset]
        | cons first rest =>
          cases rest with
          | cons second tail =>
            have headRefs := exprIH [first] env state (by omega) (by
              simp only [expsWeight] at measure ⊢; omega)
            have headClock := evaluate_clock_le [first] env state
            rw [evaluate, fixClock_evaluate]
            cases headRun : evaluate [first] env state with
            | mk result next =>
              simp only [headRun] at headRefs headClock
              cases result with
              | err error => exact headRefs
              | val values =>
                have tailRefs := exprIH (second :: tail) env next (by omega) (by
                  simp only [expsWeight] at measure ⊢; omega)
                cases tailRun : evaluate (second :: tail) env next with
                | mk result last =>
                  simp only [tailRun] at tailRefs
                  cases result <;> exact refsSubset_trans headRefs tailRefs
          | nil =>
            cases first with
            | var index =>
              rw [evaluate]
              split <;> simp [refsSubset]
            | ifThenElse condition yes no =>
              have firstRefs := exprIH [condition] env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              have firstClock := evaluate_clock_le [condition] env state
              rw [evaluate, fixClock_evaluate]
              cases firstRun : evaluate [condition] env state with
              | mk result next =>
                simp only [firstRun] at firstRefs firstClock
                cases result with
                | err error => exact firstRefs
                | val values =>
                  dsimp only
                  split
                  · exact firstRefs
                  · exact refsSubset_trans firstRefs (exprIH [yes] env next (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega))
                  · exact refsSubset_trans firstRefs (exprIH [no] env next (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega))
            | «let» bindings body =>
              have firstRefs := exprIH bindings env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              have firstClock := evaluate_clock_le bindings env state
              rw [evaluate, fixClock_evaluate]
              cases firstRun : evaluate bindings env state with
              | mk result next =>
                simp only [firstRun] at firstRefs firstClock
                cases result with
                | err error => exact firstRefs
                | val values =>
                  exact refsSubset_trans firstRefs (exprIH [body] (values ++ env) next (by omega) (by
                    simp only [expsWeight, expWeight] at measure ⊢; omega))
            | raise body =>
              have bodyRefs := exprIH [body] env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              rw [evaluate]
              cases bodyRun : evaluate [body] env state with
              | mk result next =>
                simp only [bodyRun] at bodyRefs
                cases result <;> exact bodyRefs
            | handle body handler =>
              have firstRefs := exprIH [body] env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              have firstClock := evaluate_clock_le [body] env state
              rw [evaluate, fixClock_evaluate]
              cases firstRun : evaluate [body] env state with
              | mk result next =>
                simp only [firstRun] at firstRefs firstClock
                cases result with
                | val values => exact firstRefs
                | err error =>
                  cases error with
                  | abort reason => exact firstRefs
                  | raise value =>
                    exact refsSubset_trans firstRefs (exprIH [handler] (value :: env) next (by omega) (by
                      simp only [expsWeight, expWeight] at measure ⊢; omega))
            | tick body =>
              rw [evaluate]
              split
              · simp [refsSubset]
              · have bodyRefs := smaller [body] env (decClock 1 state) (by
                  simp only [decClock]; omega)
                simpa [refsSubset, decClock] using bodyRefs
            | force location index =>
              rw [evaluate]
              split
              · simp [refsSubset]
              · split
                · simp [refsSubset]
                · simp [refsSubset]
                · simp [refsSubset]
                · split
                  · simp [refsSubset]
                  · rename_i args body found
                    split
                    · simp [refsSubset]
                    · have bodyRefs := smaller [body] args (decClock 1 state) (by
                        simp only [decClock]; omega)
                      simpa [refsSubset, decClock] using bodyRefs
            | call ticks location args =>
              have firstRefs := exprIH args env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              have firstClock := evaluate_clock_le args env state
              rw [evaluate, fixClock_evaluate]
              cases firstRun : evaluate args env state with
              | mk result next =>
                simp only [firstRun] at firstRefs firstClock
                cases result with
                | err error => exact firstRefs
                | val values =>
                  dsimp only
                  split
                  · exact firstRefs
                  · rename_i selected body found
                    split
                    · exact firstRefs
                    · have callRefs := smaller [body] selected (decClock (ticks + 1) next) (by
                        simp only [decClock]; omega)
                      apply refsSubset_trans firstRefs
                      simpa [refsSubset, decClock] using callRefs
            | op op args =>
              have firstRefs := exprIH args env state (by omega) (by
                simp only [expsWeight, expWeight] at measure ⊢; omega)
              rw [evaluate, fixClock_evaluate]
              cases firstRun : evaluate args env state with
              | mk result next =>
                simp only [firstRun] at firstRefs
                cases result with
                | err error => exact firstRefs
                | val values =>
                  cases appRun : doApp op values.reverse next with
                  | err error => simpa [appRun] using firstRefs
                  | val pair =>
                    obtain ⟨value, last⟩ := pair
                    have appRefs : refsSubset next last := fun key present =>
                      doApp_refs_mono op values.reverse next last value appRun key present
                    simpa [appRun] using refsSubset_trans firstRefs appRefs
  exact allRanks state.clock (expsWeight expressions) expressions env state rfl rfl

/-- Successful or failing evaluation preserves the source reference domain. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_refs_SUBSET"
  (fmap_as_finite_support := [refs])]
theorem evaluateRefsSubset {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (state next : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : BvlSem.evaluateTuple (expressions, env, state) = (result, next)) :
    ∀ key, state.refs.lookup key ≠ none → next.refs.lookup key ≠ none := by
  have preserved := evaluate_refs_mono expressions env state
  change evaluate expressions env state = (result, next) at run
  simpa [run, refsSubset] using preserved

end Flapjack.Compiler.Backend.BvlProps
