module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.NamespaceProps.MapLookup

@[expose] public section

/-! Type identifier conditions for declarative environments. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.InferProps
  Flapjack.Basis.Pure.MlString

/-- Every type identifier in the declarative environment belongs to the set. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_tenv_def"]
noncomputable def setTidsTenv (tids : Nat → Prop) (tenv : TypeEnv) : Prop :=
  nsAll (fun _ entry => setTidsSubset tids entry.2) tenv.t ∧
  nsAll (fun _ entry => (∀ t ∈ entry.2.1, setTidsSubset tids t) ∧ tids entry.2.2) tenv.c ∧
  nsAll (fun _ entry => setTidsSubset tids entry.2) tenv.v

/-- Extending two environments preserves their common type-ID bound. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_tenv_extend_dec_tenv"]
theorem setTidsTenvExtendDecTenv (s : Nat → Prop) (t : TypeEnv)
    (s' : Nat → Prop) (t' : TypeEnv) :
    setTidsTenv (fun id => s' id ∨ s id) t' ∧
      setTidsTenv (fun id => s' id ∨ s id) t →
      setTidsTenv (fun id => s' id ∨ s id) (extendDecTenv t' t) := by
  rintro ⟨⟨ht', hc', hv'⟩, ⟨ht, hc, hv⟩⟩
  have append {V : Type} (p : Ident MlString MlString → V → Prop)
      (a b : Namespace MlString MlString V) (ha : nsAll p a) (hb : nsAll p b) :
      nsAll p (nsAppend a b) := by
    intro id value found
    cases a with
    | bind av am =>
      cases b with
      | bind bv bm =>
        cases id with
        | short name =>
          cases h : av.lookup name with
          | none => exact hb (.short name) value (by simpa [nsAppend, nsLookup, List.lookup_append, h] using found)
          | some v => exact ha (.short name) value (by simpa [nsAppend, nsLookup, List.lookup_append, h] using found)
        | long name rest =>
          cases h : am.lookup name with
          | none => exact hb (.long name rest) value (by simpa [nsAppend, nsLookup, List.lookup_append, h] using found)
          | some env => exact ha (.long name rest) value (by simpa [nsAppend, nsLookup, List.lookup_append, h] using found)
  exact ⟨append _ _ _ ht' ht, append _ _ _ hc' hc, append _ _ _ hv' hv⟩

/-- Renaming an environment maps its permitted type identifiers pointwise. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_tenv_remap"]
theorem setTidsTenvRemap (tids : Nat → Prop) (tenv : TypeEnv) (f : Nat → Nat) :
    setTidsTenv tids tenv →
      setTidsTenv (fun id => ∃ old, tids old ∧ f old = id) (remapTenv f tenv) := by
  intro ⟨ht, hc, hv⟩
  have rename (t : SemanticT) (h : setTidsSubset tids t) :
      setTidsSubset (fun id => ∃ old, tids old ∧ f old = id) (tsTidRename f t) := by
    intro id hid
    rw [setTidsTsTidRename] at hid
    obtain ⟨old, hold, heq⟩ := hid
    exact ⟨old, h old hold, heq⟩
  simp only [setTidsTenv, remapTenv]
  refine ⟨?_, ?_, ?_⟩
  · rw [nsAll_nsMap]
    intro id entry found
    exact rename _ (ht id entry found)
  · rw [nsAll_nsMap]
    intro id entry found
    obtain ⟨hargs, hid⟩ := hc id entry found
    constructor
    · intro t mem
      obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp mem
      exact rename old (hargs old oldMem)
    · exact ⟨entry.2.2, hid, rfl⟩
  · rw [nsAll_nsMap]
    intro id entry found
    exact rename _ (hv id entry found)

/-- Renaming commutes with extending declarative environments. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "remap_tenv_extend_dec_tenv"]
theorem remapTenvExtendDecTenv (f : Nat → Nat) (t t' : TypeEnv) :
    remapTenv f (extendDecTenv t t') =
      extendDecTenv (remapTenv f t) (remapTenv f t') := by
  cases t
  cases t'
  simp [remapTenv, extendDecTenv, nsMap_nsAppend]

/-- Enlarging the permitted set preserves the type's identifier condition. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_subset_mono"]
theorem setTidsSubsetMono (tids : Nat → Prop) (t : SemanticT) (tids' : Nat → Prop) :
    setTidsSubset tids t ∧ (∀ id, tids id → tids' id) → setTidsSubset tids' t := by
  rintro ⟨ht, hsub⟩ id hid
  exact hsub id (ht id hid)

/-- Enlarging the permitted set preserves the environment's identifier condition. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_tenv_mono"]
theorem setTidsTenvMono (tids : Nat → Prop) (tenv : TypeEnv) (tids' : Nat → Prop) :
    setTidsTenv tids tenv ∧ (∀ id, tids id → tids' id) → setTidsTenv tids' tenv := by
  rintro ⟨⟨ht, hc, hv⟩, hsub⟩
  refine ⟨?_, ?_, ?_⟩
  · intro id entry h
    exact setTidsSubsetMono tids entry.2 tids' ⟨ht id entry h, hsub⟩
  · intro id entry h
    obtain ⟨hall, hid⟩ := hc id entry h
    exact ⟨fun t mem => setTidsSubsetMono tids t tids' ⟨hall t mem, hsub⟩, hsub _ hid⟩
  · intro id entry h
    exact setTidsSubsetMono tids entry.2 tids' ⟨hv id entry h, hsub⟩

end Flapjack.Compiler.Inference.TypeDCanon
