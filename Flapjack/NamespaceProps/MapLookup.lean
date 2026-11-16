module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Lookup and quantification through a mapped namespace. -/
namespace Flapjack.NamespaceHOL

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

end Flapjack.NamespaceHOL
