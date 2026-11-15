module

public import Flapjack.Compiler.Backend.BviLet.Proofs.Calls
public import Flapjack.Compiler.Backend.BviLet.Proofs.SourceAgreement
public import Flapjack.Compiler.Backend.BviLet.SourceList

@[expose] public section

/-! Simulation of the source-shaped BVI let optimizer. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

namespace OriginalEvalCarrier
/-- The BVI reference state and its finite-support representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end OriginalEvalCarrier

private theorem dropLastSize (xs : List Bvi.Exp) : sizeOf xs.dropLast ≤ sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      simp only [List.dropLast, List.cons.sizeOf_spec] at *
      omega

private theorem lastSize (xs : List Bvi.Exp) (nonempty : xs ≠ []) :
    sizeOf (xs.getLast nonempty) < sizeOf xs := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp_wf; omega
    | cons y ys =>
      have bound := ih (by simp)
      simp only [List.getLast, List.cons.sizeOf_spec] at *
      omega

/-- Induction over the rewritten list compiler, used to establish the
source-shaped simulation. -/
theorem evaluate_envRel {C F : Type} (xs : List Bvi.Exp) (offsets : List Nat) (d : Nat)
    (source target : List Value) (state final : BviState C F) (result : BviResult)
    (run : evaluateTuple (xs, source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple (compileList offsets d xs, target, state) = (result, final) := by
  cases xs with
  | nil => simpa [compileList, evaluateTuple, evaluate] using run
  | cons x rest =>
    cases rest with
    | cons y rest =>
      apply evaluate_compile_cons x (y :: rest) offsets d source target state final result
      · intro s t r h ok
        simpa [compileList] using evaluate_envRel [x] offsets d source target s t r h related ok
      · intro s t r h ok
        exact evaluate_envRel (y :: rest) offsets d source target s t r h related ok
      · exact run
      · exact notTypeError
    | nil =>
      simp only [compileList] at ⊢
      cases x with
      | var index => exact evaluate_compile_var offsets d index source target state final result related run notTypeError
      | force location index => exact evaluate_compile_force location index offsets d source target state final result run related notTypeError
      | op op args =>
        apply evaluate_compile_op op args offsets d source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | tick body =>
        apply evaluate_compile_tick body offsets d source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | raise body =>
        apply evaluate_compile_raise body offsets d source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | «return» args =>
        apply evaluate_compile_return args offsets d source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | ifThenElse guard yes no =>
        apply evaluate_compile_if guard yes no offsets d source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [guard] offsets d source target s t r h rel ok
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [yes] offsets d source target s t r h rel ok
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [no] offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | call ticks dest args handler =>
        apply evaluate_compile_call ticks dest args handler offsets d source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args offsets d source target s t r h rel ok
        · intro handlerBody eq value s t r h rel ok
          subst handler
          simpa [compileList] using evaluate_envRel [handlerBody] (0 :: offsets) d
            (value :: source) (value :: target) s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | letCall rets ticks dest args body =>
        apply evaluate_compile_letCall rets ticks dest args body offsets d source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args offsets d source target s t r h rel ok
        · intro values s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] (List.replicate rets 0 ++ offsets) d
            (values ++ source) (values ++ target) s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | «let» bindings body =>
        cases bindings with
        | nil =>
          apply evaluate_compile_let_empty body offsets d source target state final result
          · intro s t r h rel ok
            simpa [compileList] using evaluate_envRel [body] offsets d source target s t r h rel ok
          · exact run
          · exact related
          · exact notTypeError
        | cons first rest =>
          by_cases last : body = .var rest.length
          · subst body
            let front := (first :: rest).dropLast
            let endExp := (first :: rest).getLast (by simp)
            have split : first :: rest = front ++ [endExp] :=
              (List.dropLast_concat_getLast (by simp : first :: rest ≠ [])).symm
            have length : rest.length = front.length := by
              have sizes := congrArg List.length split
              simp only [List.length_cons, List.length_append, List.length_nil] at sizes
              omega
            rw [split, length] at run ⊢
            apply evaluate_compile_let_last_branch front endExp offsets d source target state final result
            · intro s t r h rel ok
              exact evaluate_envRel front offsets d source target s t r h rel ok
            · intro ax depth src dst s t r h rel ok
              simpa [compileList] using evaluate_envRel [endExp] ax depth src dst s t r h rel ok
            · exact run
            · exact related
            · exact notTypeError
          · apply evaluate_compile_let_normal first rest body offsets d source target state final result last
            · intro s t r h rel ok
              exact evaluate_envRel (first :: rest) offsets d source target s t r h rel ok
            · intro ax depth src dst s t r h rel ok
              simpa [compileList] using evaluate_envRel [body] ax depth src dst s t r h rel ok
            · exact run
            · exact related
            · exact notTypeError
termination_by sizeOf xs
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  all_goals try (cases y <;> simp_wf <;> omega)
  all_goals try (have bound := dropLastSize (first :: rest); simp only [List.cons.sizeOf_spec] at bound; omega)
  all_goals try (have bound := lastSize (first :: rest) (by simp); simp only [List.cons.sizeOf_spec] at bound; omega)

/-- The source compiler preserves a non-type-error evaluation under the
original environment relation. The independent inhabited type preserves
HOL's unused quantified argument. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "evaluate_env_rel"
  (fmap_as_finite_support := [refs])]
theorem evaluateOriginal {C F Y : Type} [Nonempty Y]
    (xs : List Bvi.Exp) (env1 : List Value) (s1 : BviState C F)
    (ax : List Nat) (env2 : List Value) (res : BviResult) (s2 : BviState C F)
    (_ys : Y) (d : Nat)
    (h : evaluateTuple (xs, env1, s1) = (res, s2) ∧ envRel ax d env1 env2 ∧
      res ≠ .err (.abort .typeError)) :
    evaluateTuple (BviLet.compile ax d xs, env2, s1) = (res, s2) := by
  rw [BviLet.compile_eq_compileList]
  exact evaluate_envRel xs ax d env1 env2 s1 s2 res h.1 h.2.1 h.2.2

/-- The original empty-displacement compiler preserves evaluation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "compile_thm"
  (fmap_as_finite_support := [refs])]
theorem compileThmOriginal {C F : Type} (xs : List Bvi.Exp) (s2 s1 : BviState C F)
    (res : BviResult) (env : List Value)
    (h : evaluateTuple (xs, env, s1) = (res, s2) ∧ res ≠ .err (.abort .typeError)) :
    evaluateTuple (BviLet.compile [] 0 xs, env, s1) = (res, s2) :=
  evaluateOriginal xs env s1 [] env res s2 () 0 ⟨h.1, by simp [envRel], h.2⟩

/-- The original single-expression compiler preserves evaluation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "evaluate_compile_exp"
  (fmap_as_finite_support := [refs])]
theorem evalExpOriginal {C F : Type} (d : Bvi.Exp) (env : List Value)
    (s t : BviState C F) (r : BviResult)
    (h : evaluateTuple ([d], env, s) = (r, t) ∧ r ≠ .err (.abort .typeError)) :
    evaluateTuple ([BviLet.compileExp d], env, s) = (r, t) := by
  simpa [BviLet.compile_eq_compileList, BviLet.compileExp_eq, BviLet.compileList] using
    compileThmOriginal [d] t s r env h

end Flapjack.Compiler.Backend.BviLet.Proofs
