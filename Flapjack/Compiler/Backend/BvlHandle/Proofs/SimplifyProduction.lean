import Flapjack.Compiler.Backend.BvlHandle.Proofs.Simplify
import Flapjack.Compiler.Backend.BvlHandle.Proofs.HelpersProduction
import Flapjack.Compiler.Backend.BvlHandle.Proofs.SimplifyTotal
import Aesop

/-! Executable correspondence for BVL handler simplification. -/
namespace Flapjack.Compiler.Backend.BvlHandle
open Bvl BvlToBvi

/-- The executable short-circuit fold computes the source list raise test. -/
theorem foldRaiseBounded_eq (fuel : Nat) (xs : List Exp) (init : Bool) :
    xs.foldlM (fun b e => if b then pure true else canRaiseBounded fuel e) init =
      some (init || canRaiseList xs) := by
  induction xs generalizing init with
  | nil => cases init <;> simp [canRaiseList]
  | cons e es ih =>
    simp only [canRaiseBounded_eq] at ih ⊢
    cases init with
    | true =>
      simp only [List.foldlM_cons, ↓reduceIte, bind, Option.bind]
      simpa [canRaiseList] using ih true
    | false =>
      simp only [List.foldlM_cons, Bool.false_eq_true, ↓reduceIte,
        bind, Option.bind]
      simpa [canRaiseList] using ih (canRaise e)

private theorem mapM_eq_map {α β : Type} (visit : α → Option β) (f : α → β)
    (correct : ∀ x y, visit x = some y → y = f x) (xs : List α) (ys : List β)
    (run : xs.mapM visit = some ys) : ys = xs.map f := by
  induction xs generalizing ys with
  | nil => simpa using run.symm
  | cons x rest ih =>
    simp only [List.mapM_cons] at run
    cases first : visit x with
    | none => simp [first] at run
    | some value =>
      cases remaining : rest.mapM visit with
      | none => simp [first, remaining] at run
      | some values =>
        simp [first, remaining] at run
        subst ys
        simp [correct x value first, ih values remaining]

private theorem fallback_eq (fuel : Nat)
    (ih : ∀ expression result, simplifyFuel fuel expression = some result → result = handleSimp expression)
    (body handler : Exp) (depth : Nat) (result : Exp)
    (run : (do
      let body' ← simplifyFuel fuel body
      let handler' ← simplifyFuel fuel handler
      pure (.handle body' (← adjustVarsBounded fuel 1 depth handler'))) = some result) :
    result = .handle (handleSimp body) (handleAdjVars 1 depth (handleSimp handler)) := by
  cases bodyRun : simplifyFuel fuel body with
  | none => simp [bodyRun] at run
  | some body' =>
    cases handlerRun : simplifyFuel fuel handler with
    | none => simp [bodyRun, handlerRun] at run
    | some handler' =>
      have bodyEq := ih body body' bodyRun
      have handlerEq := ih handler handler' handlerRun
      simpa [bodyRun, handlerRun, adjustVarsBounded_eq, bodyEq, handlerEq] using run.symm

/-- Successful fuel-bounded simplification and handler pushing agree with the
source traversals. This executable correspondence has no HOL declaration. -/
theorem simplifyFuel_eq (fuel : Nat) :
    (∀ expression result, simplifyFuel fuel expression = some result → result = handleSimp expression) ∧
    (∀ body handler depth result, makeHandleFuel fuel body handler depth = some result →
      result = makeHandle body handler depth) := by
  induction fuel with
  | zero => simp [simplifyFuel, makeHandleFuel]
  | succ fuel ih =>
    constructor
    · intro expression result run
      cases expression <;> simp only [simplifyFuel] at run <;> try simp only [handleSimp]
      all_goals try (simp only [bind, Option.bind] at run)
      all_goals repeat' split at run
      all_goals try simp_all [Proofs.handleSimpList_eq_map]
      all_goals aesop (add safe apply mapM_eq_map)
    · intro body handler depth result run
      cases body
      case raise value =>
        cases raises : canRaise value with
        | false =>
          cases handlerRun : simplifyFuel fuel handler with
          | none => simp [makeHandleFuel, canRaiseBounded_eq, raises, handlerRun] at run
          | some handler' =>
            have handlerEq := ih.1 handler handler' handlerRun
            simp [makeHandleFuel, canRaiseBounded_eq, raises, handlerRun,
              adjustVarsBounded_eq] at run
            simpa [makeHandle, raises, handlerEq] using run.symm
        | true =>
          have fallback : (do
              let body' ← simplifyFuel fuel (.raise value)
              let handler' ← simplifyFuel fuel handler
              pure (.handle body' (← adjustVarsBounded fuel 1 depth handler'))) = some result := by
            simpa [makeHandleFuel, canRaiseBounded_eq, raises] using run
          simpa [makeHandle, raises] using fallback_eq fuel ih.1 (.raise value) handler depth result fallback
      case «let» xs body =>
        cases raises : canRaiseList xs with
        | false =>
          have foldRun : xs.foldlM (fun b e => if b then pure true else canRaiseBounded fuel e) false =
              some false := by simpa [raises] using foldRaiseBounded_eq fuel xs false
          simp only [makeHandleFuel] at run
          rw [foldRun] at run
          simp only [bind, Option.bind, Bool.not_false, ↓reduceIte] at run
          cases xsRun : xs.mapM (simplifyFuel fuel) with
          | none => simp [xsRun] at run
          | some xs' =>
            cases bodyRun : makeHandleFuel fuel body handler (depth + xs.length) with
            | none => simp [xsRun, bodyRun] at run
            | some body' =>
              have xsEq := mapM_eq_map (simplifyFuel fuel) handleSimp ih.1 xs xs' xsRun
              have bodyEq := ih.2 body handler (depth + xs.length) body' bodyRun
              simp [xsRun, bodyRun] at run
              simpa [makeHandle, raises, Proofs.handleSimpList_eq_map, xsEq, bodyEq] using run.symm
        | true =>
          have foldRun : xs.foldlM (fun b e => if b then pure true else canRaiseBounded fuel e) false =
              some true := by simpa [raises] using foldRaiseBounded_eq fuel xs false
          simp only [makeHandleFuel] at run
          rw [foldRun] at run
          have fallback : (do
              let body' ← simplifyFuel fuel (.let xs body)
              let handler' ← simplifyFuel fuel handler
              pure (.handle body' (← adjustVarsBounded fuel 1 depth handler'))) = some result := by
            simpa using run
          simpa [makeHandle, raises] using fallback_eq fuel ih.1 (.let xs body) handler depth result fallback
      case ifThenElse condition yes no =>
        cases hc : canRaise condition <;> cases hy : canRaise yes <;> cases hn : canRaise no
        all_goals try
          have fallback : (do
              let body' ← simplifyFuel fuel (.ifThenElse condition yes no)
              let handler' ← simplifyFuel fuel handler
              pure (.handle body' (← adjustVarsBounded fuel 1 depth handler'))) = some result := by
            simpa [makeHandleFuel, canRaiseBounded_eq, hc, hy, hn] using run
          simpa [makeHandle, hc, hy, hn] using
            fallback_eq fuel ih.1 (.ifThenElse condition yes no) handler depth result fallback
        case false.true.false =>
          cases condRun : simplifyFuel fuel condition with
          | none => simp [makeHandleFuel, canRaiseBounded_eq, hc, hy, hn, condRun] at run
          | some cond' =>
            cases yesRun : makeHandleFuel fuel yes handler depth with
            | none => simp [makeHandleFuel, canRaiseBounded_eq, hc, hy, hn, condRun, yesRun] at run
            | some yes' =>
              cases noRun : simplifyFuel fuel no with
              | none => simp [makeHandleFuel, canRaiseBounded_eq, hc, hy, hn, condRun, yesRun, noRun] at run
              | some no' =>
                have condEq := ih.1 condition cond' condRun
                have yesEq := ih.2 yes handler depth yes' yesRun
                have noEq := ih.1 no no' noRun
                simp [makeHandleFuel, canRaiseBounded_eq, hc, hy, hn, condRun, yesRun, noRun] at run
                simpa [makeHandle, hc, hy, hn, condEq, yesEq, noEq] using run.symm
        case false.false.true =>
          cases condRun : simplifyFuel fuel condition with
          | none => simp [makeHandleFuel, canRaiseBounded_eq, hc, hy, hn, condRun] at run
          | some cond' =>
            cases yesRun : simplifyFuel fuel yes with
            | none => simp [makeHandleFuel, canRaiseBounded_eq, hc, hy, hn, condRun, yesRun] at run
            | some yes' =>
              cases noRun : makeHandleFuel fuel no handler depth with
              | none => simp [makeHandleFuel, canRaiseBounded_eq, hc, hy, hn, condRun, yesRun, noRun] at run
              | some no' =>
                have condEq := ih.1 condition cond' condRun
                have yesEq := ih.1 yes yes' yesRun
                have noEq := ih.2 no handler depth no' noRun
                simp [makeHandleFuel, canRaiseBounded_eq, hc, hy, hn, condRun, yesRun, noRun] at run
                simpa [makeHandle, hc, hy, hn, condEq, yesEq, noEq] using run.symm
      all_goals
        simp only [makeHandle]
        apply fallback_eq fuel ih.1 _ handler depth result
        simpa [makeHandleFuel] using run

/-- The executed bounded simplifier always returns the source result, even
when it retries after fuel exhaustion. -/
theorem simplifyBounded_eq (fuel : Nat) (expression : Exp) :
    simplifyBounded fuel expression = some (handleSimp expression) := by
  cases first : simplifyFuel fuel expression with
  | some result =>
    have correct := (simplifyFuel_eq fuel).1 expression result first
    simp [simplifyBounded, first, correct]
  | none =>
    have bound : expBudget expression < max fuel (expBudget expression + 1) := by omega
    obtain ⟨result, run⟩ := simplifyFuel_succeeds _ expression bound
    have correct := (simplifyFuel_eq _).1 expression result run
    simp [simplifyBounded, first, run, correct]

end Flapjack.Compiler.Backend.BvlHandle
