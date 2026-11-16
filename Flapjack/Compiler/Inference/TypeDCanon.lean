module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.NamespaceProps.MapLookup
public import Flapjack.NamespaceProps.LiftLookup

@[expose] public section

/-! Type identifier conditions for declarative environments. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.InferProps
  Flapjack.Basis.Pure.MlString

/-- Declarative environments agree on all namespace lookups. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "tenv_equiv_def"]
def tenvEquiv (t1 t2 : TypeEnv) : Prop :=
  nsAll2 (fun _ a b => a = b) t1.t t2.t ∧
  nsAll2 (fun _ a b => a = b) t1.c t2.c ∧
  nsAll2 (fun _ a b => a = b) t1.v t2.v

/-- Every declarative environment is equivalent to itself. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "tenv_equiv_refl"]
theorem tenvEquivRefl (tenv : TypeEnv) : tenvEquiv tenv tenv := by
  have refl {V : Type} (env : Namespace MlString MlString V) :
      nsAll2 (fun _ a b => a = b) env env := by
    constructor <;> constructor
    all_goals first | (intro id v found; exact ⟨v, found, rfl⟩) | (intro path absent; exact absent)
  exact ⟨refl tenv.t, refl tenv.c, refl tenv.v⟩

/-- Environment equivalence is symmetric. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "tenv_equiv_sym"]
theorem tenvEquivSym (t1 t2 : TypeEnv) : tenvEquiv t1 t2 → tenvEquiv t2 t1 := by
  have sym {V : Type} {a b : Namespace MlString MlString V}
      (h : nsAll2 (fun _ x y => x = y) a b) :
      nsAll2 (fun _ x y => x = y) b a := by
    obtain ⟨⟨forward, fm⟩, ⟨backward, bm⟩⟩ := h
    refine ⟨⟨?_, bm⟩, ⟨?_, fm⟩⟩
    · intro id v found
      obtain ⟨w, hw, eq⟩ := backward id v found
      exact ⟨w, hw, eq.symm⟩
    · intro id v found
      obtain ⟨w, hw, eq⟩ := forward id v found
      exact ⟨w, hw, eq.symm⟩
  intro ⟨ht, hc, hv⟩
  exact ⟨sym ht, sym hc, sym hv⟩

/-- Lifting equivalent environments under the same module preserves equivalence. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "tenv_equiv_tenvLift"]
theorem tenvEquivTenvLift (t1 t2 : TypeEnv) (m : MlString) :
    tenvEquiv t1 t2 → tenvEquiv (tenvLift m t1) (tenvLift m t2) := by
  intro h
  simpa only [tenvEquiv, tenvLift, nsAll2_nsLift] using h

/-- Equivalent environments give the same variable lookup. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "lookup_var_tenv_equiv"]
theorem lookupVarTenvEquiv (t1 t2 : TypeEnv) (n : Ident MlString MlString)
    (bvs : TenvValExp) : tenvEquiv t1 t2 → lookupVar n bvs t1 = lookupVar n bvs t2 := by
  intro ⟨_, _, hv⟩
  have same : nsLookup t1.v n = nsLookup t2.v n := by
    cases first : nsLookup t1.v n with
    | none =>
      cases second : nsLookup t2.v n with
      | none => rfl
      | some v =>
        obtain ⟨w, found, _⟩ := hv.2.1 n v second
        simp [first] at found
    | some v =>
      obtain ⟨w, found, eq⟩ := hv.1.1 n v first
      cases eq
      simp [found]
  simp only [lookupVar, same]

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
