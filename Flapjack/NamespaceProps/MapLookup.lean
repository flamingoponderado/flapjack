module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Lookup and quantification through a mapped namespace. -/
namespace Flapjack.NamespaceHOL

/-- Mapping twice composes the value transformations throughout a namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsMap_compose"]
theorem nsMapCompose {M N V W X : Type} (g : V → W) (env : Namespace M N V) (f : W → X) :
    nsMap f (nsMap g env) = nsMap (f ∘ g) env := by
  cases env with
  | bind values modules =>
    simp only [nsMap, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p mem
    cases p with
    | mk name sub => simp only [Function.comp_apply, nsMapCompose g sub f]
termination_by sizeOf env
decreasing_by
  have h := List.sizeOf_lt_of_mem mem
  simp only [Prod.mk.sizeOf_spec, Namespace.bind.sizeOf_spec] at h ⊢
  omega

/-- Mapping the identity function preserves the namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsMap_I"]
theorem nsMapId {M N V : Type} (env : Namespace M N V) : nsMap id env = env := by
  cases env with
  | bind values modules =>
    simp only [nsMap]
    congr 1
    · simp
    · have h : modules.map (fun p => (p.1, nsMap id p.2)) = modules.map id := by
        apply List.map_congr_left
        intro p mem
        cases p with
        | mk name sub => simp only [id_eq, nsMapId sub]
      simpa using h
termination_by sizeOf env
decreasing_by
  have h := List.sizeOf_lt_of_mem mem
  simp only [Prod.mk.sizeOf_spec, Namespace.bind.sizeOf_spec] at h ⊢
  omega

/-- Mapping commutes with appending namespaces. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsMap_nsAppend"]
theorem nsMap_nsAppend {M N V W : Type} (n1 n2 : Namespace M N V) (f : V → W) :
    nsMap f (nsAppend n1 n2) = nsAppend (nsMap f n1) (nsMap f n2) := by
  cases n1
  cases n2
  simp [nsAppend, nsMap, List.map_append]

/-- Mapping association-list values commutes with first-match lookup. -/
private theorem lookupMapValues {K V W : Type} [BEq K]
    (entries : List (K × V)) (key : K) (f : V → W) :
    (entries.map (fun p => (p.1, f p.2))).lookup key = (entries.lookup key).map f := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨k, v⟩
    simp only [List.map_cons, List.lookup]
    split <;> simp_all

@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_nsMap"]
theorem nsLookup_nsMap {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (env : Namespace M N V) (id : Ident M N) (f : V → W) :
    nsLookup (nsMap f env) id = (nsLookup env id).map f := by
  induction id generalizing env with
  | short name =>
    cases env with
    | bind values modules => simp [nsMap, nsLookup, lookupMapValues]
  | long mn id ih =>
    cases env with
    | bind values modules =>
      simp only [nsMap, nsLookup, lookupMapValues]
      cases found : modules.lookup mn with
      | none => simp
      | some nested => simp [ih]

@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookupMod_nsMap"]
theorem nsLookupMod_nsMap {M N V W : Type} [DecidableEq M]
    (env : Namespace M N V) (path : List M) (f : V → W) :
    nsLookupMod (nsMap f env) path = (nsLookupMod env path).map (nsMap f) := by
  induction path generalizing env with
  | nil => rfl
  | cons mn path ih =>
    cases env with
    | bind values modules =>
      simp only [nsMap, nsLookupMod, lookupMapValues]
      cases found : modules.lookup mn with
      | none => simp
      | some nested => simp [ih]

@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll_nsMap"]
theorem nsAll_nsMap {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (f : V → W) (env : Namespace M N V) (P : Ident M N → W → Prop) :
    nsAll P (nsMap f env) ↔ nsAll (fun id value => P id (f value)) env := by
  simp only [nsAll, nsLookup_nsMap]
  constructor
  · intro h id value found
    exact h id (f value) (by simp [found])
  · intro h id value found
    cases source : nsLookup env id with
    | none => simp [source] at found
    | some v =>
      simp [source] at found
      subst value
      exact h id v source

/-- Mapping association-list values maps the stored value in every entry. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsMap_alist_to_ns"]
theorem nsMap_alistToNs {M N V W : Type} (f : V → W) (l : Alist N V) :
    nsMap f (alistToNs (ModuleName := M) l) =
      alistToNs (ModuleName := M) (l.map fun p => (p.1, f p.2)) := by
  simp [nsMap, alistToNs]

/-- A sub-relation between mapped namespaces is the sub-relation between the
original namespaces under the mapped relation. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsSub_nsMap"]
theorem nsSub_nsMap {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → W → W → Prop) (f : V → W) (n1 n2 : Namespace M N V) :
    nsSub R (nsMap f n1) (nsMap f n2) ↔
      nsSub (fun id x y => R id (f x) (f y)) n1 n2 := by
  constructor
  · intro sub
    constructor
    · intro id v1 found
      have mapped : nsLookup (nsMap f n1) id = some (f v1) := by
        simp [nsLookup_nsMap, found]
      obtain ⟨w2, found2, rel⟩ := sub.1 id (f v1) mapped
      rw [nsLookup_nsMap] at found2
      cases h2 : nsLookup n2 id with
      | none => simp [h2] at found2
      | some v2 =>
        simp only [h2, Option.map_some, Option.some.injEq] at found2
        refine ⟨v2, rfl, ?_⟩
        change R id (f v1) (f v2)
        rw [found2]
        exact rel
    · intro path absent
      have mapped : nsLookupMod (nsMap f n2) path = none := by
        simp [nsLookupMod_nsMap, absent]
      have h := sub.2 path mapped
      simp [nsLookupMod_nsMap] at h
      exact h
  · intro sub
    constructor
    · intro id w1 found
      rw [nsLookup_nsMap] at found
      cases h1 : nsLookup n1 id with
      | none => simp [h1] at found
      | some v1 =>
        simp only [h1, Option.map_some, Option.some.injEq] at found
        obtain ⟨v2, found2, rel⟩ := sub.1 id v1 h1
        refine ⟨f v2, by simp [nsLookup_nsMap, found2], ?_⟩
        rw [← found]
        exact rel
    · intro path absent
      have h2 : nsLookupMod n2 path = none := by
        simpa [nsLookupMod_nsMap] using absent
      simpa [nsLookupMod_nsMap] using sub.2 path h2

end Flapjack.NamespaceHOL
