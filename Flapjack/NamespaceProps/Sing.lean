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

/-- A singleton is sub-related to a singleton exactly when the names match and
values are related. -/
private theorem nsSub_nsSing {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → W → Prop) (n1 : N) (v1 : V) (n2 : N) (v2 : W) :
    nsSub R (nsSing n1 v1) (nsSing n2 v2) ↔ n1 = n2 ∧ R (.short n1) v1 v2 := by
  constructor
  · intro sub
    have left : nsLookup (nsSing n1 v1 : Namespace M N V) (.short n1) = some v1 := by
      rw [nsLookup_nsSing, if_pos rfl]
    obtain ⟨w, found, rel⟩ := sub.1 (.short n1) v1 left
    rw [nsLookup_nsSing] at found
    by_cases same : n1 = n2
    · have sameId : (.short n1 : Ident M N) = .short n2 := by simp [same]
      rw [if_pos sameId] at found
      simp at found
      refine ⟨same, ?_⟩
      rw [found]
      exact rel
    · have neId : (.short n1 : Ident M N) ≠ .short n2 := by simpa using same
      rw [if_neg neId] at found
      simp at found
  · rintro ⟨same, rel⟩
    subst same
    constructor
    · intro id value found
      rw [nsLookup_nsSing] at found
      by_cases sameId : id = .short n1
      · rw [if_pos sameId] at found
        simp at found
        refine ⟨v2, ?_, ?_⟩
        · rw [nsLookup_nsSing, if_pos sameId]
        · rw [sameId, ← found]
          exact rel
      · rw [if_neg sameId] at found
        simp at found
    · intro path absent
      rw [nsLookupMod_nsSing] at absent
      by_cases empty : path = []
      · rw [if_pos empty] at absent
        simp at absent
      · rw [if_neg empty] at absent
        rw [nsLookupMod_nsSing, if_neg empty]

/-- Two singleton namespaces are two-way related exactly when the names match
and their values are related. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll2_nsSing"]
theorem nsAll2_nsSing {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → W → Prop) (n1 : N) (v1 : V) (n2 : N) (v2 : W) :
    nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ↔ n1 = n2 ∧ R (.short n1) v1 v2 := by
  constructor
  · intro both
    obtain ⟨same, rel⟩ := (nsSub_nsSing R n1 v1 n2 v2).1 both.1
    exact ⟨same, rel⟩
  · rintro ⟨same, rel⟩
    subst same
    exact ⟨(nsSub_nsSing R n1 v1 n1 v2).2 ⟨rfl, rel⟩,
      (nsSub_nsSing (fun x y z => R x z y) n1 v2 n1 v1).2 ⟨rfl, rel⟩⟩

end Flapjack.NamespaceHOL
