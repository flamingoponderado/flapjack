module

public import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyAux
public import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateGrowth
public import Flapjack.SemanticPrimitivesProps.ResultMap
public import Flapjack.HolRef

@[expose] public section

/-!
# BVI primitive fields and clock stability of evaluation

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:309-365`
and `:350-460`: `do_app_inv_clock`, `do_app_inc_clock_IMP`,
`evaluate_inv_clock`, `do_app_code`, `do_app_oracle`,
`evaluate_global_mono_lemma` and `evaluate_global_mono`. Each keeps HOL's
binder order and premise shape; the underlying facts are the untagged
dispatcher and evaluator lemmas in the neighbouring modules.
-/

namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

namespace ApplyFieldsCarrier
/-- Canonical BVI reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BviSem.BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end ApplyFieldsCarrier

/-- A non-install primitive application leaves the code tree unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_code"
  (fmap_as_finite_support := [refs])]
theorem doApp_code {C F : Type} (op : ClosLang.Op)
    (state next : Flapjack.Compiler.Backend.BviSem.BviState C F) (args : List Value)
    (value : Value) (run : doApp op args state = .val (value, next) ∧ op ≠ .install) :
    next.code = state.code := by
  obtain ⟨runEq, notInstall⟩ := run
  by_cases hinstall : op = .install
  · subst hinstall
    exact (notInstall rfl).elim
  · simp only [doApp, doAppFallback] at runEq ⊢
    cases aux : doAppAux op args state with
    | none => simp [aux] at runEq
    | some inner =>
      cases inner with
      | some pair =>
        obtain ⟨value', next'⟩ := pair
        simp only [aux] at runEq
        cases runEq
        exact doAppAux_code op args state next value aux
      | none =>
        simp only [aux] at runEq
        cases fallback : BvlSem.doApp op args (toBvl state) with
        | err error' =>
          split at runEq
          all_goals simp_all
        | val pair =>
          obtain ⟨value', next'⟩ := pair
          simp only [fallback] at runEq
          cases runEq
          simp [fromBvl]

/-- A non-install primitive application leaves the compiler and its oracle
unchanged. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_oracle"
  (fmap_as_finite_support := [refs])]
theorem doApp_oracle {C F : Type} (op : ClosLang.Op)
    (state next : Flapjack.Compiler.Backend.BviSem.BviState C F) (args : List Value)
    (value : Value) (run : doApp op args state = .val (value, next) ∧ op ≠ .install) :
    next.compileOracle = state.compileOracle ∧ next.compile = state.compile := by
  obtain ⟨runEq, notInstall⟩ := run
  by_cases hinstall : op = .install
  · subst hinstall
    exact (notInstall rfl).elim
  · simp only [doApp, doAppFallback] at runEq ⊢
    cases aux : doAppAux op args state with
    | none => simp [aux] at runEq
    | some inner =>
      cases inner with
      | some pair =>
        obtain ⟨value', next'⟩ := pair
        simp only [aux] at runEq
        cases runEq
        have fields := doAppAux_compiler_fields op args state next value aux
        exact ⟨fields.2.1, fields.1⟩
      | none =>
        simp only [aux] at runEq
        cases fallback : BvlSem.doApp op args (toBvl state) with
        | err error' =>
          split at runEq
          all_goals simp_all
        | val pair =>
          obtain ⟨value', next'⟩ := pair
          simp only [fallback] at runEq
          cases runEq
          simp [fromBvl]

/-- Adding clock allowance commutes with primitive application, mapping the
returned state's clock as in the source. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_inc_clock"
  (fmap_as_finite_support := [refs])]
theorem doApp_inc_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (clock : Nat) (state : Flapjack.Compiler.Backend.BviSem.BviState C F) :
    doApp op args (incClock clock state) =
      SemanticPrimitivesProps.mapResult (fun (value, next) =>
        (value, { next with clock := clock + state.clock })) id (doApp op args state) := by
  cases run : doApp op args state with
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have sameClock := BviSem.doApp_clock op args state next value run
    have shifted := doApp_incClock op args state next value clock run
    rw [shifted]
    simp only [SemanticPrimitivesProps.mapResult, incClock]
    rw [sameClock]
    simp [Nat.add_comm]
  | err error =>
    rw [doApp_incClock_error op args state error clock run]
    simp only [SemanticPrimitivesProps.mapResult, SemanticPrimitivesProps.mapErrorResult_id]

/-- Non-timeout evaluation is stable under an added clock allowance. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_inv_clock"
  (fmap_as_finite_support := [refs])]
theorem evaluateInvClockHOL {C F : Type} (expressions : List Bvi.Exp) (env : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (result : BviResult)
    (next : Flapjack.Compiler.Backend.BviSem.BviState C F) (clock : Nat)
    (run : evaluateTuple (expressions, env, state) = (result, next) ∧
      result ≠ .err (.abort .timeoutError)) :
    evaluateTuple (expressions, env, incClock clock state) = (result, incClock clock next) :=
  evaluateAddClock expressions env state result next run clock

/-- A successful or failing primitive application is stable under an added
clock allowance. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_inc_clock_IMP"
  (fmap_as_finite_support := [refs])]
theorem doApp_inc_clock_IMP {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : Flapjack.Compiler.Backend.BviSem.BviState C F) (value : Value)
    (error : ErrorResult ExnOrRet) (clock : Nat) :
    (doApp op args state = .val (value, next) →
        doApp op args (incClock clock state) = .val (value, incClock clock next)) ∧
      (doApp op args state = .err error →
        doApp op args (incClock clock state) = .err error) := by
  constructor
  · intro run
    exact doApp_incClock op args state next value clock run
  · intro run
    exact doApp_incClock_error op args state error clock run

/-- A primitive application result is stable under an added clock allowance,
case by case as in the source. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_inv_clock"
  (fmap_as_finite_support := [refs])]
theorem doApp_inv_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (clock : Nat) :
    match doApp op args.reverse state with
    | .val (value, next) =>
      doApp op args.reverse (incClock clock state) = .val (value, incClock clock next)
    | .err error => doApp op args.reverse (incClock clock state) = .err error := by
  cases run : doApp op args.reverse state with
  | val pair =>
    obtain ⟨value, next⟩ := pair
    exact doApp_incClock op args.reverse state next value clock run
  | err error =>
    exact doApp_incClock_error op args.reverse state error clock run

/-- Evaluation cannot remove an initialized global pointer. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_global_mono_lemma"
  (fmap_as_finite_support := [refs])]
theorem evaluateGlobalMonoLemmaHOL {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state : Flapjack.Compiler.Backend.BviSem.BviState C F) :
    state.global.isSome = true →
      (evaluateTuple (expressions, env, state)).2.global.isSome = true := by
  intro present
  have growth := evaluate_growth expressions env state
  simpa [evaluateTuple, stateGrowth] using growth.2 present

/-- Evaluation cannot remove an initialized global pointer. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "evaluate_global_mono"
  (fmap_as_finite_support := [refs])]
theorem evaluateGlobalMonoHOL {C F : Type} (expressions : List Bvi.Exp)
    (env : List Value) (state : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (result : BviResult) (next : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (run : evaluateTuple (expressions, env, state) = (result, next))
    (present : state.global.isSome = true) : next.global.isSome = true := by
  have preserved := evaluateGlobalMonoLemmaHOL expressions env state present
  rw [run] at preserved
  exact preserved

end Flapjack.Compiler.Backend.BviProps
