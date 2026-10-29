import Flapjack.Compiler.Backend.FlatToClos.Proofs.OperatorInduction

/-! Clock-and-weight induction for the proof-side flat-to-closure evaluator.
The semantic carriers and relations remain under HOL correspondence review;
these declarations are not tagged as HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Singleton evaluation is simulated for match-free expressions under the
proof-side state and environment relations. -/
theorem evaluate_singleton_simulation {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F) (expression : FlatLang.Exp)
    (states : StateRel source target) (environments : EnvRel env names values)
    (safe : FlatProps.noMat expression = true)
    (notTypeError : (FlatSem.evaluate env source [expression]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [expression] := by
  have allRanks : ∀ clock weight : Nat,
      ∀ (env : FlatSem.Environment FlatSem.Value) (names : List (Option MlString)) (values : List ClosSem.Value)
        (source : FlatSem.State C F) (target : ClosSem.State C F) (expression : FlatLang.Exp),
        source.clock = clock → FlatSem.expWeight expression = weight → StateRel source target →
        EnvRel env names values → FlatProps.noMat expression = true →
        (FlatSem.evaluate env source [expression]).2 ≠ .err (.abort .typeError) →
        EvalSim env names values source target [expression] := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expression : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
            (names : List (Option MlString)) (values : List ClosSem.Value)
            (source : FlatSem.State C F) (target : ClosSem.State C F),
            source.clock ≤ clock → FlatSem.expWeight expression < weight → StateRel source target →
            EnvRel env names values → FlatProps.noMat expression = true →
            (FlatSem.evaluate env source [expression]).2 ≠ .err (.abort .typeError) →
            EvalSim env names values source target [expression] := by
          intro expression env names values source target clockLe weightLt states environments safe notError
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH source.clock clockLt (FlatSem.expWeight expression) env names values source target expression
              rfl rfl states environments safe notError
          · exact weightIH (FlatSem.expWeight expression) weightLt env names values source target expression
              clockEq rfl states environments safe notError
        intro env names values source target expression clockEq weightEq states environments safe notError
        cases expression with
        | lit trace literal => exact evaluate_lit env names values source target trace literal states
        | varLocal trace name =>
          cases found : env.v.lookup name with
          | none => simp [FlatSem.evaluate, found] at notError
          | some value => exact evaluate_var env names values source target trace name value states environments found
        | fn trace name body =>
          apply evaluate_fn env names values source target trace name body states environments
          simpa [FlatProps.noMat] using safe
        | raise trace body =>
          apply evaluate_raise env names values source target trace body ?_ notError
          intro bodyNot
          apply exprIH body env names values source target (by omega) ?_ states environments ?_ bodyNot
          · simp only [FlatSem.expWeight] at weightEq; omega
          · simpa [FlatProps.noMat] using safe
        | con trace stamp args =>
          apply evaluate_con env names values source target trace stamp args ?_ notError
          intro argsNot
          apply evaluate_list_of_singletons env names values args.reverse clock
          · intro body member next nextTarget bound nextStates bodyNot
            have original : body ∈ args := by simpa using member
            have bodySafe : FlatProps.noMat body = true :=
              noMat_member args body (by simpa [FlatProps.noMat] using safe) original
            have bodyWeight := expWeight_lt_expsWeight args body original
            apply exprIH body env names values next nextTarget bound ?_ nextStates environments bodySafe bodyNot
            simp only [FlatSem.expWeight] at weightEq
            omega
          · omega
          · exact states
          · exact argsNot
        | app trace op args =>
          apply evaluate_operator_from_induction env names values source target trace op args states environments safe ?_ ?_ notError
          · intro body newEnv newNames newValues next nextTarget bound bodySafe envRel nextStates bodyNot
            exact clockIH next.clock (by omega) (FlatSem.expWeight body) newEnv newNames newValues next nextTarget body
              rfl rfl nextStates envRel bodySafe bodyNot
          · intro body newEnv newNames newValues next nextTarget bound smaller bodySafe envRel nextStates bodyNot
            exact exprIH body newEnv newNames newValues next nextTarget (by omega) (by omega) nextStates envRel bodySafe bodyNot
        | letrec trace funs body =>
          have safeParts : FlatProps.noMatFuns funs = true ∧ FlatProps.noMat body = true := by
            simpa [FlatProps.noMat] using safe
          apply evaluate_letrec env names values source target trace funs body states environments safeParts.1 ?_ notError
          intro newEnv newNames newValues envRel bodyNot
          apply exprIH body newEnv newNames newValues source target (by omega) ?_ states envRel safeParts.2 bodyNot
          simp only [FlatSem.expWeight] at weightEq
          omega
        | let_ trace name first body =>
          have safeParts : FlatProps.noMat first = true ∧ FlatProps.noMat body = true := by
            simpa [FlatProps.noMat] using safe
          apply evaluate_let env names values source target trace name first body environments ?_ ?_ notError
          · intro firstNot
            apply exprIH first env names values source target (by omega) ?_ states environments safeParts.1 firstNot
            simp only [FlatSem.expWeight] at weightEq; omega
          · intro sourceValue targetValue next nextTarget valueRel nextStates bound nextEnv envRel bodyNot
            apply exprIH body _ _ _ next nextTarget (by omega) ?_ nextStates envRel safeParts.2 bodyNot
            simp only [FlatSem.expWeight] at weightEq; omega
        | if_ trace condition yes no =>
          have safeParts : FlatProps.noMat condition = true ∧ FlatProps.noMat yes = true ∧ FlatProps.noMat no = true := by
            simpa [FlatProps.noMat, Bool.and_eq_true, and_assoc] using safe
          apply evaluate_if env names values source target trace condition yes no ?_ ?_ notError
          · intro condNot
            apply exprIH condition env names values source target (by omega) ?_ states environments safeParts.1 condNot
            simp only [FlatSem.expWeight] at weightEq; omega
          · intro branch next nextTarget nextStates bound branchNot
            cases branch with
            | false =>
              apply exprIH no env names values next nextTarget (by omega) ?_ nextStates environments safeParts.2.2 branchNot
              simp only [FlatSem.expWeight] at weightEq; omega
            | true =>
              apply exprIH yes env names values next nextTarget (by omega) ?_ nextStates environments safeParts.2.1 branchNot
              simp only [FlatSem.expWeight] at weightEq; omega
        | mat trace body rows => simp [FlatProps.noMat] at safe
        | handle trace body rows =>
          cases rows with
          | nil => simp [FlatProps.noMat] at safe
          | cons row rest =>
            obtain ⟨pattern, handler⟩ := row
            cases rest with
            | cons row rest => simp [FlatProps.noMat] at safe
            | nil =>
              cases pattern <;> simp [FlatProps.noMat] at safe
              case pvar name =>
                have safeParts := safe
                apply evaluate_handle env names values source target trace name body handler environments ?_ ?_ notError
                · intro bodyNot
                  apply exprIH body env names values source target (by omega) ?_ states environments safeParts.1 bodyNot
                  simp only [FlatSem.expWeight, FlatSem.rowsWeight] at weightEq; omega
                · intro sourceValue targetValue next nextTarget valueRel nextStates bound envRel handlerNot
                  apply exprIH handler _ _ _ next nextTarget (by omega) ?_ nextStates envRel safeParts.2 handlerNot
                  simp only [FlatSem.expWeight, FlatSem.rowsWeight] at weightEq; omega
  exact allRanks source.clock (FlatSem.expWeight expression) env names values source target expression
    rfl rfl states environments safe notTypeError

/-- Match-free expression lists preserve the proof-side state and result
relations without additional simulation hypotheses. -/
theorem evaluate_simulation {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F) (expressions : List FlatLang.Exp)
    (states : StateRel source target) (environments : EnvRel env names values)
    (safe : FlatProps.noMatList expressions = true)
    (notTypeError : (FlatSem.evaluate env source expressions).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target expressions := by
  apply evaluate_list_of_singletons env names values expressions source.clock
  · intro expression member next nextTarget _ nextStates notError
    exact evaluate_singleton_simulation env names values next nextTarget expression nextStates environments
      (noMat_member expressions expression safe member) notError
  · exact le_refl _
  · exact states
  · exact notTypeError

/-- Match-free installed declarations preserve the proof-side state and
unit-terminated result relations without additional simulation hypotheses. -/
theorem evaluate_decs_unit_simulation {C F : Type}
    (source : FlatSem.State C F) (target : ClosSem.State C F) (declarations : List FlatLang.Exp)
    (states : StateRel source target) (safe : FlatProps.noMatDecs declarations = true)
    (notTypeError : (FlatSem.evaluateDecs source declarations).2 ≠ some (.abort .typeError)) :
    DecUnitSim source target declarations := by
  have emptyEnv : EnvRel ⟨[]⟩ [] [] := by
    apply (envRel_iff_lookup _ _ _).2
    simp
  apply evaluate_decs_unit_of_singletons declarations source.clock
  · intro expression member next nextTarget _ nextStates notError
    have expressionSafe : FlatProps.noMat expression = true := by
      apply noMat_member declarations expression
      · simpa [FlatProps.noMatDecs_eq_noMatList] using safe
      · exact member
    exact evaluate_singleton_simulation ⟨[]⟩ [] [] next nextTarget expression nextStates emptyEnv expressionSafe notError
  · exact le_refl _
  · exact states
  · exact notTypeError

/-- Match-free top-level declaration lists preserve the proof-side state and
declaration result relations. -/
theorem evaluate_decs_simulation {C F : Type}
    (source : FlatSem.State C F) (target : ClosSem.State C F) (declarations : List FlatLang.Exp)
    (states : StateRel source target) (safe : FlatProps.noMatDecs declarations = true)
    (notTypeError : (FlatSem.evaluateDecs source declarations).2 ≠ some (.abort .typeError)) :
    DecSim source target declarations := by
  have emptyEnv : EnvRel ⟨[]⟩ [] [] := by
    apply (envRel_iff_lookup _ _ _).2
    simp
  induction declarations generalizing source target with
  | nil => exact evaluate_decs_nil source target states
  | cons first rest ih =>
    have safeParts : FlatProps.noMat first = true ∧ FlatProps.noMatDecs rest = true := by
      simpa [FlatProps.noMatDecs] using safe
    apply evaluate_decs_cons source target first rest
    · intro firstNot
      exact evaluate_singleton_simulation ⟨[]⟩ [] [] source target first states emptyEnv safeParts.1 firstNot
    · intro next nextTarget nextStates _ nextNot
      exact ih next nextTarget nextStates safeParts.2 nextNot
    · exact notTypeError

end Flapjack.Compiler.Backend.FlatToClos
