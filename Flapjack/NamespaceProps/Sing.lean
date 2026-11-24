module

public import Flapjack.NamespaceProps.Bind
public import Mathlib.Data.Set.Basic

@[expose] public section

/-! Original laws for single-entry namespaces. -/
namespace Flapjack.NamespaceHOL

/-- Appending a singleton namespace is binding into the other namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAppend_nsSing"]
theorem nsAppend_nsSing {M N V : Type} (n : N) (x : V) (e : Namespace M N V) :
    nsAppend (nsSing n x) e = nsBind n x e := by
  cases e with | bind v m =>
  simp [nsSing, nsBind, nsAppend]

/-- Looking up in a singleton namespace finds exactly the short name. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_nsSing"]
theorem nsLookup_nsSing {M N V : Type} [DecidableEq M] [DecidableEq N]
    (n : N) (v : V) (id : Ident M N) :
    nsLookup (nsSing n v) id = if id = .short n then some v else none := by
  cases id with
  | short name =>
    simp [nsSing, nsLookup, List.lookup, BEq.beq]
    by_cases same : name = n
    · subst n
      simp
    · simp [same]
  | long mn rest => simp [nsSing, nsLookup, List.lookup]

/-- Mapping a singleton namespace maps its single value. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsMap_nsSing"]
theorem nsMap_nsSing {M N V W : Type} (f : V → W) (x : N) (v : V) :
    (nsMap f (nsSing x v) : Namespace M N W) = nsSing x (f v) := by
  simp [nsMap, nsSing]

/-- Looking up a module path in a singleton finds the singleton only at the empty path. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookupMod_nsSing"]
theorem nsLookupMod_nsSing {M N V : Type} [DecidableEq M] (path : List M) (n : N) (v : V) :
    nsLookupMod (nsSing n v) path =
      if path = [] then some (nsSing n v) else none := by
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn rest => simp [nsSing, nsLookupMod, List.lookup]

/-- The value domain of a singleton is its single short identifier. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDom_nsSing"]
theorem nsDom_nsSing {M N V : Type} [DecidableEq M] [DecidableEq N] (x : N) (y : V) :
    nsDom (nsSing x y) = ({.short x} : Set (Ident M N)) := by
  funext id
  apply propext
  change (∃ v, nsLookup (nsSing x y) id = some v) ↔ id = .short x
  cases id with
  | short name =>
    simp [nsSing, nsLookup, List.lookup, BEq.beq]
    by_cases same : name = x
    · subst x
      simp
    · simp [same]
  | long mn rest => simp [nsSing, nsLookup, List.lookup]

/-- The module domain of a singleton contains only the empty path. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDomMod_nsSing"]
theorem nsDomMod_nsSing {M N V : Type} [DecidableEq M] (x : N) (y : V) :
    nsDomMod (nsSing x y) = ({[]} : Set (List M)) := by
  funext path
  apply propext
  change (∃ v, nsLookupMod (nsSing x y) path = some v) ↔ path = []
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn rest => simp [nsSing, nsLookupMod, List.lookup]

end Flapjack.NamespaceHOL
