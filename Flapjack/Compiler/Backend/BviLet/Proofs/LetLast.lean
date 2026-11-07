import Flapjack.Compiler.Backend.BviLet.Proofs.Let

/-! The final-variable shortcut of BVI let propagation. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The final-variable shortcut preserves evaluation given the two recursive
simulations. Untagged until BVI evaluation and its dispatcher are reviewed. -/
theorem evaluate_compile_let_last {C F : Type} (front : List Bvi.Exp) (last : Bvi.Exp)
    (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (frontIH : ∀ (s t : BviState C F) r, evaluateTuple (front, source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList offsets d front, target, s) = (r, t))
    (lastIH : ∀ (ax : List Nat) (depth : Nat) (src dst : List Value) (s t : BviState C F) r,
      evaluateTuple ([last], src, s) = (r, t) → envRel ax depth src dst →
      r ≠ .err (.abort .typeError) → evaluateTuple ([compileSing ax depth last], dst, s) = (r, t))
    (run : evaluateTuple ([.let (front ++ [last]) (.var front.length)], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.let (compileList offsets d front)
      (compileSing (offsets.map (front.length + ·)) (d + front.length) last)], target, state) =
      (result, final) := by
  change evaluate [.let (front ++ [last]) (.var front.length)] source state = _ at run
  change evaluate [.let (compileList offsets d front)
    (compileSing (offsets.map (front.length + ·)) (d + front.length) last)] target state = _
  rw [evaluate, fixClock_evaluate] at run ⊢
  have split := evaluateSnoc front source state last
  change evaluate (front ++ [last]) source state = _ at split
  rw [split] at run
  cases frontRun : evaluateTuple (front, source, state) with
  | mk frontResult middle =>
    cases frontResult with
    | err error =>
      simp only [frontRun] at run
      have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have mapped := frontIH state middle (.err error) frontRun related ok
      change evaluate (compileList offsets d front) target state = _ at mapped
      rw [mapped]
      exact run
    | val values =>
      have length := evaluateImpLength front source state middle values frontRun
      have mapped := frontIH state middle (.val values) frontRun related (by simp)
      change evaluate (compileList offsets d front) target state = _ at mapped
      rw [mapped]
      simp only [frontRun] at run
      cases lastRun : evaluateTuple ([last], source, middle) with
      | mk lastResult next =>
        cases lastResult with
        | err error =>
          simp only [lastRun] at run
          have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
            intro bad
            apply notTypeError
            exact (congrArg Prod.fst run).symm.trans bad
          have shifted := envRel_shift values offsets d source target related
          rw [← length] at shifted
          exact lastIH _ _ _ _ middle next (.err error) lastRun shifted ok |>.trans run
        | val lastValues =>
          obtain ⟨value, rfl⟩ := evaluateSing last source middle next lastValues lastRun
          have lookup : (values ++ [value] ++ source)[front.length]? = some value := by
            rw [length, List.append_assoc, List.getElem?_append_right (by omega)]
            simp
          simp only [lastRun, evaluate, lookup] at run
          have shifted := envRel_shift values offsets d source target related
          rw [← length] at shifted
          exact lastIH _ _ _ _ middle next (.val [value]) lastRun shifted (by simp) |>.trans run

/-- The source-shaped optimizer selects the final-variable shortcut. -/
theorem compileSing_let_last (front : List Bvi.Exp) (last : Bvi.Exp)
    (offsets : List Nat) (d : Nat) :
    compileSing offsets d (.let (front ++ [last]) (.var front.length)) =
      .let (compileList offsets d front)
        (compileSing (offsets.map (front.length + ·)) (d + front.length) last) := by
  cases front with
  | nil => simp [compileSing, compileList]
  | cons first rest =>
    have drop : (first :: (rest ++ [last])).dropLast = first :: rest := by
      simpa only [List.cons_append] using
        (List.dropLast_concat (l₁ := first :: rest) (b := last))
    simp [compileSing, drop]

/-- The actual final-variable optimizer branch preserves evaluation under
the recursive simulations. Untagged until BVI evaluation is reviewed. -/
theorem evaluate_compile_let_last_branch {C F : Type} (front : List Bvi.Exp) (last : Bvi.Exp)
    (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (frontIH : ∀ (s t : BviState C F) r, evaluateTuple (front, source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList offsets d front, target, s) = (r, t))
    (lastIH : ∀ (ax : List Nat) (depth : Nat) (src dst : List Value) (s t : BviState C F) r,
      evaluateTuple ([last], src, s) = (r, t) → envRel ax depth src dst →
      r ≠ .err (.abort .typeError) → evaluateTuple ([compileSing ax depth last], dst, s) = (r, t))
    (run : evaluateTuple ([.let (front ++ [last]) (.var front.length)], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.let (front ++ [last]) (.var front.length))], target, state) =
      (result, final) := by
  rw [compileSing_let_last]
  exact evaluate_compile_let_last front last offsets d source target state final result
    frontIH lastIH run related notTypeError

end Flapjack.Compiler.Backend.BviLet.Proofs
