module

public import Flapjack.Compiler.Inference.TypeDCanon.Expression

@[expose] public section

/-! Single-identifier renaming in source typing judgments. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.AstHOL
  Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps

/-- Flapjack proof helper for the source single-renaming proofs: an identifier
outside the primitive set can be changed without changing the primitive IDs. -/
private theorem goodRemapSingRenum (m n : Nat) (tids : Nat → Prop)
    (absent : ¬ tids m) (prim : primTids true tids) : goodRemap (singRenum m n) := by
  unfold goodRemap
  calc
    (TlistNum :: TboolNum :: primTypeNums).map (singRenum m n) =
        (TlistNum :: TboolNum :: primTypeNums).map id := by
      apply List.map_congr_left
      intro x member
      have other : x ≠ m := fun eq => absent (eq ▸ (prim x member).2 rfl)
      simp [singRenum, other]
    _ = _ := List.map_id _

/-- Single-identifier renaming preserves source pattern typing. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_p_ts_tid_rename_sing_renum"]
theorem typePTsTidRenameSingRenum (m n : Nat) (tids : Nat → Prop) (tvs : Nat)
    (env : TypeEnv) (p : Pat) (t : SemanticT) (bindings : List (MlString × SemanticT)) :
    ¬ tids m ∧ primTids true tids ∧ TypeP tvs env p t bindings ∧ setTidsTenv tids env →
      TypeP tvs env p (tsTidRename (singRenum m n) t)
        (bindings.map (fun entry => (entry.1, tsTidRename (singRenum m n) entry.2))) := by
  rintro ⟨absent, prim, typed, bound⟩
  have good := goodRemapSingRenum m n tids absent prim
  have renamed := (typePTsTidRename (singRenum m n) good).1 tvs env p t bindings typed
  exact typePTenvEquiv.1 tvs _ p _ _ renamed env (singRenumNotInTenvId tids env m n ⟨bound, absent⟩)

/-- Single-identifier renaming preserves source expression typing. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_e_ts_tid_rename_sing_renum"]
theorem typeETsTidRenameSingRenum (m n : Nat) (tids : Nat → Prop) (env : TypeEnv)
    (localEnv : TenvValExp) (e : Flapjack.AstHOL.Exp) (t : SemanticT) :
    ¬ tids m ∧ primTids true tids ∧ TypeE env localEnv e t ∧ setTidsTenv tids env →
      TypeE env (remapTenvE (singRenum m n) localEnv) e (tsTidRename (singRenum m n) t) := by
  rintro ⟨absent, prim, typed, bound⟩
  have good := goodRemapSingRenum m n tids absent prim
  have renamed := (typeETsTidRename (singRenum m n) good).1 env localEnv e t typed
  exact typeETenvEquiv.1 _ _ e _ renamed env (singRenumNotInTenvId tids env m n ⟨bound, absent⟩)

/-- Single-identifier renaming preserves source function-list typing. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_funs_ts_tid_rename_sing_renum"]
theorem typeFunsTsTidRenameSingRenum (m n : Nat) (tids : Nat → Prop) (env : TypeEnv)
    (localEnv : TenvValExp) (funs : List (MlString × MlString × Flapjack.AstHOL.Exp))
    (bindings : List (MlString × SemanticT)) :
    ¬ tids m ∧ primTids true tids ∧ TypeFuns env localEnv funs bindings ∧ setTidsTenv tids env →
      TypeFuns env (remapTenvE (singRenum m n) localEnv) funs
        (bindings.map (fun entry => (entry.1, tsTidRename (singRenum m n) entry.2))) := by
  rintro ⟨absent, prim, typed, bound⟩
  have good := goodRemapSingRenum m n tids absent prim
  have renamed := (typeETsTidRename (singRenum m n) good).2.2 env localEnv funs bindings typed
  exact typeETenvEquiv.2.2 _ _ funs _ renamed env (singRenumNotInTenvId tids env m n ⟨bound, absent⟩)

end Flapjack.Compiler.Inference.TypeDCanon
