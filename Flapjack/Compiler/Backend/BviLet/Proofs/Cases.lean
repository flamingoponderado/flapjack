import Flapjack.Compiler.Backend.BviLet.Proofs.LetLast

/-! List, primitive, and control cases for BVI let propagation. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value asBool)

/-- The force case uses the same relocated environment lookup as variables.
Untagged until the evaluator is reviewed. -/
theorem evaluate_compile_force {C F : Type} (location index : Nat) (offsets : List Nat) (d : Nat)
    (source target : List Value) (state final : BviState C F) (result : BviResult)
    (run : evaluateTuple ([.force location index], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.force location index)], target, state) = (result, final) := by
  cases lookup : source[index]? with
  | none =>
    simp [evaluateTuple, evaluate, lookup] at run
    exact False.elim (notTypeError run.1.symm)
  | some value =>
    have targetLookup := envRel_lookup offsets d source target related index value lookup
    simpa [compileSing, evaluateTuple, evaluate, lookup, targetLookup] using run

/-- Sequential list evaluation preserves results given the head and tail
simulations. Untagged until the evaluator is reviewed. -/
theorem evaluate_compile_cons {C F : Type} (head : Bvi.Exp) (tail : List Bvi.Exp)
    (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (headIH : ∀ (s t : BviState C F) r, evaluateTuple ([head], source, s) = (r, t) →
      r ≠ .err (.abort .typeError) → evaluateTuple ([compileSing offsets d head], target, s) = (r, t))
    (tailIH : ∀ (s t : BviState C F) r, evaluateTuple (tail, source, s) = (r, t) →
      r ≠ .err (.abort .typeError) → evaluateTuple (compileList offsets d tail, target, s) = (r, t))
    (run : evaluateTuple (head :: tail, source, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple (compileList offsets d (head :: tail), target, state) = (result, final) := by
  rw [compileList, evaluateCons]
  rw [evaluateCons] at run
  cases headRun : evaluateTuple ([head], source, state) with
  | mk headResult next =>
    cases headResult with
    | err error =>
      simp only [headRun] at run
      have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      rw [headIH state next (.err error) headRun ok]
      exact run
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing head source state next values headRun
      rw [headIH state next (.val [value]) headRun (by simp)]
      dsimp only
      simp only [headRun] at run
      cases tailRun : evaluateTuple (tail, source, next) with
      | mk tailResult last =>
        cases tailResult with
        | err error =>
          simp only [tailRun] at run
          have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
            intro bad
            apply notTypeError
            exact (congrArg Prod.fst run).symm.trans bad
          rw [tailIH next last (.err error) tailRun ok]
          exact run
        | val vs =>
          rw [tailIH next last (.val vs) tailRun (by simp)]
          simpa [tailRun] using run

/-- Primitive application preserves evaluation under the argument-list
induction hypothesis. Untagged until the dispatcher is reviewed. -/
theorem evaluate_compile_op {C F : Type} (op : ClosLang.Op) (args : List Bvi.Exp)
    (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (ih : ∀ (s t : BviState C F) r, evaluateTuple (args, source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList offsets d args, target, s) = (r, t))
    (run : evaluateTuple ([.op op args], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.op op args)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.op op (compileList offsets d args)] target state = _
  change evaluate [.op op args] source state = _ at run
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases original : evaluate args source state with
  | mk inner next =>
    cases inner with
    | err error =>
      simp only [original] at run
      have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have transformed := ih state next (.err error) original related ok
      change evaluate (compileList offsets d args) target state = _ at transformed
      rw [transformed]
      exact run
    | val values =>
      have transformed := ih state next (.val values) original related (by simp)
      change evaluate (compileList offsets d args) target state = _ at transformed
      rw [transformed]
      simpa [original] using run

/-- Tick preserves evaluation when the recursive body simulation holds.
Untagged until the evaluator is reviewed. -/
theorem evaluate_compile_tick {C F : Type} (body : Bvi.Exp) (offsets : List Nat) (d : Nat)
    (source target : List Value) (state final : BviState C F) (result : BviResult)
    (ih : ∀ (s t : BviState C F) r, evaluateTuple ([body], source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing offsets d body], target, s) = (r, t))
    (run : evaluateTuple ([.tick body], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.tick body)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.tick (compileSing offsets d body)] target state = _
  change evaluate [.tick body] source state = _ at run
  rw [evaluate] at run ⊢
  by_cases zero : state.clock = 0
  · simpa [zero] using run
  · simp only [zero, ↓reduceIte] at run ⊢
    exact ih _ _ result run related notTypeError

/-- Raise preserves evaluation under the recursive body simulation.
Untagged until the evaluator is reviewed. -/
theorem evaluate_compile_raise {C F : Type} (body : Bvi.Exp) (offsets : List Nat) (d : Nat)
    (source target : List Value) (state final : BviState C F) (result : BviResult)
    (ih : ∀ (s t : BviState C F) r, evaluateTuple ([body], source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing offsets d body], target, s) = (r, t))
    (run : evaluateTuple ([.raise body], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.raise body)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.raise (compileSing offsets d body)] target state = _
  change evaluate [.raise body] source state = _ at run
  rw [evaluate] at run ⊢
  cases original : evaluate [body] source state with
  | mk inner next =>
    cases inner with
    | err error =>
      simp only [original] at run
      have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have transformed := ih state next (.err error) original related ok
      change evaluate [compileSing offsets d body] target state = _ at transformed
      rw [transformed]
      exact run
    | val values =>
      have transformed := ih state next (.val values) original related (by simp)
      change evaluate [compileSing offsets d body] target state = _ at transformed
      rw [transformed]
      simpa [original] using run

/-- Return preserves evaluation under the argument-list simulation. Untagged
until the evaluator is reviewed. -/
theorem evaluate_compile_return {C F : Type} (args : List Bvi.Exp) (offsets : List Nat) (d : Nat)
    (source target : List Value) (state final : BviState C F) (result : BviResult)
    (ih : ∀ (s t : BviState C F) r, evaluateTuple (args, source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList offsets d args, target, s) = (r, t))
    (run : evaluateTuple ([.return args], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.return args)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.return (compileList offsets d args)] target state = _
  change evaluate [.return args] source state = _ at run
  rw [evaluate] at run ⊢
  cases original : evaluate args source state with
  | mk inner next =>
    cases inner with
    | err error =>
      simp only [original] at run
      have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have transformed := ih state next (.err error) original related ok
      change evaluate (compileList offsets d args) target state = _ at transformed
      rw [transformed]
      exact run
    | val values =>
      have transformed := ih state next (.val values) original related (by simp)
      change evaluate (compileList offsets d args) target state = _ at transformed
      rw [transformed]
      simpa [original] using run

/-- The conditional case preserves the selected branch and all non-type-error
outcomes. Untagged until the evaluator is reviewed. -/
theorem evaluate_compile_if {C F : Type} (guard yes no : Bvi.Exp)
    (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (guardIH : ∀ (s t : BviState C F) r, evaluateTuple ([guard], source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing offsets d guard], target, s) = (r, t))
    (yesIH : ∀ (s t : BviState C F) r, evaluateTuple ([yes], source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing offsets d yes], target, s) = (r, t))
    (noIH : ∀ (s t : BviState C F) r, evaluateTuple ([no], source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing offsets d no], target, s) = (r, t))
    (run : evaluateTuple ([.ifThenElse guard yes no], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.ifThenElse guard yes no)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.ifThenElse (compileSing offsets d guard) (compileSing offsets d yes)
    (compileSing offsets d no)] target state = _
  change evaluate [.ifThenElse guard yes no] source state = _ at run
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases original : evaluate [guard] source state with
  | mk inner next =>
    cases inner with
    | err error =>
      simp only [original] at run
      have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have mapped := guardIH state next (.err error) original related ok
      change evaluate [compileSing offsets d guard] target state = _ at mapped
      rw [mapped]
      exact run
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing guard source state next values original
      have mapped := guardIH state next (.val [value]) original related (by simp)
      change evaluate [compileSing offsets d guard] target state = _ at mapped
      rw [mapped]
      simp only [original] at run
      change (match asBool value with
        | none => ((.err (.abort .typeError) : BviResult), next)
        | some true => evaluate [yes] source next
        | some false => evaluate [no] source next) = _ at run
      change (match asBool value with
        | none => ((.err (.abort .typeError) : BviResult), next)
        | some true => evaluate [compileSing offsets d yes] target next
        | some false => evaluate [compileSing offsets d no] target next) = _
      cases h : asBool value with
      | none =>
        simp [h] at run
        exact False.elim (notTypeError run.1.symm)
      | some choice =>
        cases choice <;> simp [h] at run ⊢
        · exact noIH next final result run related notTypeError
        · exact yesIH next final result run related notTypeError

end Flapjack.Compiler.Backend.BviLet.Proofs
