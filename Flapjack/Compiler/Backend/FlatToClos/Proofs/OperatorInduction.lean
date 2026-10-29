import Flapjack.Compiler.Backend.FlatToClos.Proofs.Sequencing

/-! The operator case of the proof-side evaluator induction. Its clock and
weight hypotheses are induction hypotheses, not a reviewed HOL theorem. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Every member has smaller weight than the expression-list measure. -/
theorem expWeight_lt_expsWeight (expressions : List FlatLang.Exp) (expression : FlatLang.Exp)
    (member : expression ∈ expressions) : FlatSem.expWeight expression < FlatSem.expsWeight expressions := by
  induction expressions with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    simp only [FlatSem.expsWeight]
    rcases member with rfl | member
    · omega
    · have bound := ih member
      omega

/-- The no-match list predicate holds for every member. -/
theorem noMat_member (expressions : List FlatLang.Exp) (expression : FlatLang.Exp)
    (safe : FlatProps.noMatList expressions = true) (member : expression ∈ expressions) :
    FlatProps.noMat expression = true := by
  rw [FlatProps.noMatList_eq_all] at safe
  exact List.all_eq_true.mp safe expression member

/-- The operator expression case follows from induction at lower clocks and
at smaller expression weights. -/
theorem evaluate_operator_from_induction {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (states : StateRel source target) (environments : EnvRel env names values)
    (safe : FlatProps.noMat (.app trace op args) = true)
    (lowerClock : ∀ (expression : FlatLang.Exp) (newEnv : FlatSem.Environment FlatSem.Value)
        (newNames : List (Option MlString)) (newValues : List ClosSem.Value)
        (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      next.clock < source.clock → FlatProps.noMat expression = true →
      EnvRel newEnv newNames newValues → StateRel next nextTarget →
      (FlatSem.evaluate newEnv next [expression]).2 ≠ .err (.abort .typeError) →
      EvalSim newEnv newNames newValues next nextTarget [expression])
    (lowerWeight : ∀ (expression : FlatLang.Exp) (newEnv : FlatSem.Environment FlatSem.Value)
        (newNames : List (Option MlString)) (newValues : List ClosSem.Value)
        (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      next.clock ≤ source.clock → FlatSem.expWeight expression < FlatSem.expWeight (.app trace op args) →
      FlatProps.noMat expression = true → EnvRel newEnv newNames newValues → StateRel next nextTarget →
      (FlatSem.evaluate newEnv next [expression]).2 ≠ .err (.abort .typeError) →
      EvalSim newEnv newNames newValues next nextTarget [expression])
    (notTypeError : (FlatSem.evaluate env source [.app trace op args]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace op args] := by
  have safeArgs : FlatProps.noMatList args = true := by simpa [FlatProps.noMat] using safe
  have argWeight : ∀ expression, expression ∈ args →
      FlatSem.expWeight expression < FlatSem.expWeight (.app trace op args) := by
    intro expression member
    have bound := expWeight_lt_expsWeight args expression member
    simp only [FlatSem.expWeight]
    omega
  apply evaluate_operator env names values source target trace op args states
  · intro argsNot
    apply evaluate_list_of_singletons env names values args.reverse source.clock
    · intro expression member next nextTarget bound related notError
      have original : expression ∈ args := by simpa using member
      exact lowerWeight expression env names values next nextTarget bound (argWeight expression original)
        (noMat_member args expression safeArgs original) environments related notError
    · exact le_refl _
    · exact states
    · exact argsNot
  · intro expression next nextTarget member related bound notError
    exact lowerWeight expression env names values next nextTarget bound (argWeight expression member)
      (noMat_member args expression safeArgs member) environments related notError
  · intro innerTrace inner shape innerNot
    subst args
    have innerSafe : FlatProps.noMat inner = true := by simpa [FlatProps.noMat, FlatProps.noMatList] using safeArgs
    apply lowerWeight inner env names values source target (le_refl _) ?_ innerSafe environments states innerNot
    simp [FlatSem.expWeight, FlatSem.expsWeight]
    omega
  · intro innerTrace inner shape innerNot
    subst args
    have innerSafe : FlatProps.noMat inner = true := by simpa [FlatProps.noMat, FlatProps.noMatList] using safeArgs
    apply lowerWeight inner env names values source target (le_refl _) ?_ innerSafe environments states innerNot
    simp [FlatSem.expWeight, FlatSem.expsWeight]
    omega
  · intro next nextTarget nextEnv body newNames newValues bound nonzero related safeBody nextStates bodyNot
    apply lowerClock body nextEnv newNames newValues (FlatSem.decClock next) (ClosSem.decClock 1 nextTarget) ?_
      safeBody related nextStates bodyNot
    simp [FlatSem.decClock]
    omega
  · intro sourceValue targetValue next nextTarget isForce related nextStates bound bodyNot
    subst op
    apply lowerWeight (FlatSem.appUnit (.varLocal .none (ofString "f")))
      ⟨[(ofString "f", sourceValue)]⟩ [some (ofString "f")] [targetValue] next nextTarget bound
      (FlatSem.appUnit_force_weight trace args) ?_ ?_ nextStates bodyNot
    · simp [FlatSem.appUnit, FlatProps.noMat, FlatProps.noMatList]
    · have emptyEnv : EnvRel ⟨[]⟩ [] [] := by
        apply (envRel_iff_lookup _ _ _).2
        simp
      simpa using envRel_cons (name := ofString "f") emptyEnv related
  · intro decs next nextTarget related smaller safeDecs decsNot
    apply evaluate_decs_unit_of_singletons decs next.clock
    · intro expression member after afterTarget bound afterStates afterNot
      have safeExpr : FlatProps.noMat expression = true := by
        apply noMat_member decs expression
        · simpa [FlatProps.noMatDecs_eq_noMatList] using safeDecs
        · exact member
      have emptyEnv : EnvRel ⟨[]⟩ [] [] := by
        apply (envRel_iff_lookup _ _ _).2
        simp
      exact lowerClock expression ⟨[]⟩ [] [] after afterTarget (by omega) safeExpr emptyEnv afterStates afterNot
    · exact le_refl _
    · exact related
    · exact decsNot
  · exact notTypeError

end Flapjack.Compiler.Backend.FlatToClos
