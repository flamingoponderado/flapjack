import Flapjack.Compiler.Backend.BviLet.Proofs.Cases

/-! Call cases of the BVI let-propagation simulation. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value findCode)

/-- Let-call preserves evaluation under the argument and continuation
induction hypotheses. Untagged until the BVI evaluator is reviewed. -/
theorem evaluate_compile_letCall {C F : Type} (rets ticks dest : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (argsIH : ∀ (s t : BviState C F) r, evaluateTuple (args, source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList offsets d args, target, s) = (r, t))
    (bodyIH : ∀ (values : List Value) (s t : BviState C F) r,
      evaluateTuple ([body], values ++ source, s) = (r, t) →
      envRel (List.replicate rets 0 ++ offsets) d (values ++ source) (values ++ target) →
      r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing (List.replicate rets 0 ++ offsets) d body], values ++ target, s) = (r, t))
    (run : evaluateTuple ([.letCall rets ticks dest args body], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.letCall rets ticks dest args body)], target, state) =
      (result, final) := by
  simp only [compileSing]
  change evaluate [.letCall rets ticks dest (compileList offsets d args)
    (compileSing (List.replicate rets 0 ++ offsets) d body)] target state = _
  change evaluate [.letCall rets ticks dest args body] source state = _ at run
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
      have mapped := argsIH state next (.err error) original related ok
      change evaluate (compileList offsets d args) target state = _ at mapped
      rw [mapped]
      exact run
    | val values =>
      have mapped := argsIH state next (.val values) original related (by simp)
      change evaluate (compileList offsets d args) target state = _ at mapped
      rw [mapped]
      simp only [original] at run
      cases code : findCode (some dest) values next.code with
      | none => simpa [code] using run
      | some selected =>
        rcases selected with ⟨callEnv, callee⟩
        simp only [code] at run ⊢
        by_cases clock : next.clock < ticks + 1
        · simpa [clock] using run
        · simp only [clock, ↓reduceIte, fixClock_evaluate] at run ⊢
          cases called : evaluate [callee] callEnv (decClock (ticks + 1) next) with
          | mk callResult callState =>
            cases callResult with
            | val returned => simpa [called] using run
            | err error =>
              cases error with
              | abort reason => simpa [called] using run
              | raise payload =>
                cases payload with
                | exn value => simpa [called] using run
                | ret returned =>
                  simp only [called] at run ⊢
                  by_cases count : returned.length = rets
                  · simp only [count, ↓reduceIte] at run ⊢
                    have extended := envRel_replicate returned offsets d source target related
                    rw [count] at extended
                    exact bodyIH returned callState final result run extended notTypeError
                  · simpa [count] using run

/-- Calls preserve evaluation under the argument and exception-handler
induction hypotheses. Untagged until the BVI evaluator is reviewed. -/
theorem evaluate_compile_call {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (handler : Option Bvi.Exp) (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (argsIH : ∀ (s t : BviState C F) r, evaluateTuple (args, source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList offsets d args, target, s) = (r, t))
    (handlerIH : ∀ (h : Bvi.Exp), handler = some h → ∀ (value : Value) (s t : BviState C F) r,
      evaluateTuple ([h], value :: source, s) = (r, t) →
      envRel (0 :: offsets) d (value :: source) (value :: target) →
      r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing (0 :: offsets) d h], value :: target, s) = (r, t))
    (run : evaluateTuple ([.call ticks dest args handler], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.call ticks dest args handler)], target, state) =
      (result, final) := by
  have compiled : compileSing offsets d (.call ticks dest args handler) =
      .call ticks dest (compileList offsets d args) (handler.map (compileSing (0 :: offsets) d)) := by
    cases handler <;> simp [compileSing]
  rw [compiled]
  change evaluate [.call ticks dest (compileList offsets d args)
    (handler.map (compileSing (0 :: offsets) d))] target state = _
  change evaluate [.call ticks dest args handler] source state = _ at run
  rw [evaluate] at run ⊢
  have validEq : (dest.isNone && (handler.map (compileSing (0 :: offsets) d)).isSome) =
      (dest.isNone && handler.isSome) := by cases handler <;> rfl
  rw [validEq]
  by_cases invalid : dest.isNone && handler.isSome
  · simpa [invalid] using run
  · simp only [invalid, fixClock_evaluate] at run ⊢
    cases original : evaluate args source state with
    | mk inner next =>
      cases inner with
      | err error =>
        simp only [original] at run
        have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
          intro bad
          apply notTypeError
          exact (congrArg Prod.fst run).symm.trans bad
        have mapped := argsIH state next (.err error) original related ok
        change evaluate (compileList offsets d args) target state = _ at mapped
        rw [mapped]
        exact run
      | val values =>
        have mapped := argsIH state next (.val values) original related (by simp)
        change evaluate (compileList offsets d args) target state = _ at mapped
        rw [mapped]
        simp only [original] at run
        cases code : findCode dest values next.code with
        | none => simpa [code] using run
        | some selected =>
          rcases selected with ⟨callEnv, callee⟩
          simp only [code] at run ⊢
          by_cases clock : next.clock < ticks + 1
          · simpa [clock] using run
          · simp only [clock, ↓reduceIte] at run ⊢
            cases called : evaluate [callee] callEnv (decClock (ticks + 1) next) with
            | mk callResult callState =>
              cases callResult with
              | val returned => simpa [called] using run
              | err error =>
                cases error with
                | abort reason => simpa [called] using run
                | raise payload =>
                  cases payload with
                  | ret returned => simpa [called] using run
                  | exn value =>
                    cases handler with
                    | none => simpa [called] using run
                    | some h =>
                      simp only [called, Option.map_some] at run ⊢
                      have extended : envRel (0 :: offsets) d (value :: source) (value :: target) := by
                        simpa [envRel] using related
                      cases handlerRun : evaluate [h] (value :: source) callState with
                      | mk handlerResult handlerState =>
                        have ok : handlerResult ≠ .err (.abort .typeError) := by
                          intro bad
                          subst handlerResult
                          simp [handlerRun] at run
                          exact notTypeError run.1.symm
                        have mapped := handlerIH h rfl value callState handlerState handlerResult
                          handlerRun extended ok
                        change evaluate [compileSing (0 :: offsets) d h] (value :: target) callState = _ at mapped
                        rw [mapped]
                        simpa [handlerRun] using run

end Flapjack.Compiler.Backend.BviLet.Proofs
