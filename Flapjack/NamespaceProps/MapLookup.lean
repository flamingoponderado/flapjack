module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Lookup and quantification through a mapped namespace. -/
namespace Flapjack.NamespaceHOL

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
