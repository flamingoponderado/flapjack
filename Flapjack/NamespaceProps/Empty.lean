module

public import Flapjack.NamespaceHOL
public import Mathlib.Data.Set.Basic

@[expose] public section

/-! Original namespace laws for the empty namespace. -/
namespace Flapjack.NamespaceHOL

/-- The empty association list builds the empty namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "alist_to_ns_nil"]
theorem alistToNs_nil {M N V : Type} : alistToNs ([] : Alist N V) = (nsEmpty : Namespace M N V) :=
  rfl

/-- The empty namespace is a sub-namespace of every namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsSub_nsEmpty"]
theorem nsSub_nsEmpty {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (r : Ident M N → V → W → Prop) (env : Namespace M N W) :
    nsSub r (nsEmpty : Namespace M N V) env := by
  constructor
  · intro id value found
    cases id
    all_goals simp [nsEmpty, nsLookup, List.lookup] at found
  · intro path found
    cases path with
    | nil => simp [nsLookupMod] at found
    | cons mn rest => simp [nsEmpty, nsLookupMod, List.lookup]

/-- Every predicate holds throughout the empty namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll_nsEmpty"]
theorem nsAll_nsEmpty {M N V : Type} [DecidableEq M] [DecidableEq N]
    (f : Ident M N → V → Prop) : nsAll f (nsEmpty : Namespace M N V) := by
  intro id value found
  cases id
  all_goals simp [nsEmpty, nsLookup, List.lookup] at found

/-- Two empty namespaces are related by any three-place relation. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll2_nsEmpty"]
theorem nsAll2_nsEmpty {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (r : Ident M N → V → W → Prop) :
    nsAll2 r (nsEmpty : Namespace M N V) (nsEmpty : Namespace M N W) :=
  ⟨nsSub_nsEmpty r nsEmpty, nsSub_nsEmpty (fun id left right => r id right left) nsEmpty⟩

/-- The empty namespace has no identifiers in its domain. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDom_nsEmpty"]
theorem nsDom_nsEmpty {M N V : Type} [DecidableEq M] [DecidableEq N] :
    nsDom (nsEmpty : Namespace M N V) = (∅ : Set (Ident M N)) := by
  funext id
  apply propext
  change (∃ v, nsLookup (nsEmpty : Namespace M N V) id = some v) ↔ False
  cases id
  all_goals simp [nsEmpty, nsLookup, List.lookup]

/-- The empty namespace's module domain contains only the empty path. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDomMod_nsEmpty"]
theorem nsDomMod_nsEmpty {M N V : Type} [DecidableEq M] :
    nsDomMod (nsEmpty : Namespace M N V) = ({[]} : Set (List M)) := by
  funext path
  apply propext
  change (∃ v, nsLookupMod (nsEmpty : Namespace M N V) path = some v) ↔ path = []
  cases path with
  | nil => simp [nsEmpty, nsLookupMod]
  | cons mn rest => simp [nsEmpty, nsLookupMod, List.lookup]

/-- Mapping over the empty namespace is the empty namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsMap_nsEmpty"]
theorem nsMap_nsEmpty {M N V W : Type} (f : V → W) :
    nsMap f (nsEmpty : Namespace M N V) = (nsEmpty : Namespace M N W) := by
  simp [nsMap, nsEmpty]

/-- Binding into any namespace never yields the empty namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsBind_nsEmpty"]
theorem nsBind_nsEmpty {M N V : Type} (name : N) (value : V) (env : Namespace M N V) :
    nsBind name value env ≠ (nsEmpty : Namespace M N V) := by
  intro same
  cases env with
  | bind vs ms => simp [nsBind, nsEmpty] at same

end Flapjack.NamespaceHOL
