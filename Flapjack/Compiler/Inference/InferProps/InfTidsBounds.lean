module

public import Flapjack.Compiler.Inference.InferProps

@[expose] public section

/-!
# Identifier-set bounds for inference substitutions

Counterparts of `inf_set_tids_infer_deBruijn_subst_SUBSET` and
`inf_set_tids_infer_type_subst_SUBSET`. HOL's `A ⊆ B` is the tagged
`infSetTidsSubset B A` (the pointwise `∀ id, infSetTids A id → B id`), and
`BIGUNION (IMAGE inf_set_tids (set l))` is the pointwise
`∃ s ∈ l, infSetTids s id`.
-/

namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Basis.Pure.MlString Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.Infer

/-- A looked-up value occurs among the right components of the association
list. Flapjack infrastructure for the source-substitution bound. -/
private theorem mem_snd_of_lookup {α β : Type} [DecidableEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), l.lookup k = some v → v ∈ l.map Prod.snd
  | [], _, _, h => by simp [List.lookup] at h
  | (k', v') :: l, k, v, h => by
      simp only [List.lookup] at h
      split at h
      · simp_all
      · exact List.mem_cons_of_mem _ (mem_snd_of_lookup l k v h)

mutual
/-- Structural induction helper for the de Bruijn substitution bound. -/
private theorem dbSubstTidsType (subst : List InferT) (t : InferT) :
    ∀ id, infSetTids (inferDeBruijnSubst subst t) id →
      infSetTids t id ∨ ∃ s ∈ subst, infSetTids s id := by
  cases t with
  | varDb k =>
    intro id h
    cases hk : subst[k]? with
    | none => simp [inferDeBruijnSubst, hk, infSetTids] at h
    | some s =>
      refine Or.inr ⟨s, List.mem_iff_getElem?.mpr ⟨k, hk⟩, ?_⟩
      simpa [inferDeBruijnSubst, hk] using h
  | uvar k =>
    intro id h
    simp [inferDeBruijnSubst, infSetTids] at h
  | app ts name =>
    intro id h
    simp only [inferDeBruijnSubst, infSetTids] at h ⊢
    rcases h with same | nested
    · exact Or.inl (Or.inl same)
    · rcases dbSubstTidsList subst ts id nested with inTs | witness
      · exact Or.inl (Or.inr inTs)
      · exact Or.inr witness
termination_by sizeOf t

/-- List induction used by the de Bruijn substitution bound. -/
private theorem dbSubstTidsList (subst : List InferT) (ts : List InferT) :
    ∀ id, infSetTidsList (inferDeBruijnSubstList subst ts) id →
      infSetTidsList ts id ∨ ∃ s ∈ subst, infSetTids s id := by
  cases ts with
  | nil =>
    intro id h
    simp [inferDeBruijnSubstList, infSetTidsList] at h
  | cons t ts =>
    intro id h
    simp only [inferDeBruijnSubstList, infSetTidsList] at h ⊢
    rcases h with head | tail
    · rcases dbSubstTidsType subst t id head with inT | witness
      · exact Or.inl (Or.inl inT)
      · exact Or.inr witness
    · rcases dbSubstTidsList subst ts id tail with inTs | witness
      · exact Or.inl (Or.inr inTs)
      · exact Or.inr witness
termination_by sizeOf ts
end

/-- Original `inf_set_tids_infer_deBruijn_subst_SUBSET`: substituting de Bruijn
variables cannot introduce identifiers beyond the original type and the
substituted types. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "inf_set_tids_infer_deBruijn_subst_SUBSET"]
theorem infSetTidsInferDeBruijnSubstSubset (subst : List InferT) (t : InferT) :
    infSetTidsSubset (fun id => infSetTids t id ∨ ∃ s ∈ subst, infSetTids s id)
      (inferDeBruijnSubst subst t) :=
  dbSubstTidsType subst t

mutual
/-- Structural induction helper for the source-substitution bound. -/
private theorem typeSubstTidsType (subst : List (MlString × InferT)) (t : SemanticT) :
    ∀ id, infSetTids (inferTypeSubst subst t) id →
      setTids t id ∨ ∃ s ∈ subst.map Prod.snd, infSetTids s id := by
  cases t with
  | var name =>
    intro id h
    cases found : subst.lookup name with
    | none => simp [inferTypeSubst, found, infSetTids] at h
    | some s =>
      refine Or.inr ⟨s, mem_snd_of_lookup subst name s found, ?_⟩
      simpa [inferTypeSubst, found] using h
  | varDb n =>
    intro id h
    simp [inferTypeSubst, infSetTids] at h
  | app ts name =>
    intro id h
    simp only [inferTypeSubst, infSetTids, setTids] at h ⊢
    rcases h with same | nested
    · exact Or.inl (Or.inl same)
    · rcases typeSubstTidsList subst ts id nested with inTs | witness
      · exact Or.inl (Or.inr inTs)
      · exact Or.inr witness
termination_by sizeOf t

/-- List induction used by the source-substitution bound. -/
private theorem typeSubstTidsList (subst : List (MlString × InferT)) (ts : List SemanticT) :
    ∀ id, infSetTidsList (inferTypeSubstList subst ts) id →
      setTidsList ts id ∨ ∃ s ∈ subst.map Prod.snd, infSetTids s id := by
  cases ts with
  | nil =>
    intro id h
    simp [inferTypeSubstList, infSetTidsList] at h
  | cons t ts =>
    intro id h
    simp only [inferTypeSubstList, infSetTidsList, setTidsList] at h ⊢
    rcases h with head | tail
    · rcases typeSubstTidsType subst t id head with inT | witness
      · exact Or.inl (Or.inl inT)
      · exact Or.inr witness
    · rcases typeSubstTidsList subst ts id tail with inTs | witness
      · exact Or.inl (Or.inr inTs)
      · exact Or.inr witness
termination_by sizeOf ts
end

/-- Original `inf_set_tids_infer_type_subst_SUBSET`: substituting source type
variables cannot introduce identifiers beyond the original type and the
substituted types. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "inf_set_tids_infer_type_subst_SUBSET"]
theorem infSetTidsInferTypeSubstSubset (subst : List (MlString × InferT)) (t : SemanticT) :
    infSetTidsSubset
      (fun id => setTids t id ∨ ∃ s ∈ subst.map Prod.snd, infSetTids s id)
      (inferTypeSubst subst t) :=
  typeSubstTidsType subst t

end Flapjack.Compiler.Inference.InferProps
