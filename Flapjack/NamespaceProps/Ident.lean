module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Original identifier construction and projection laws. -/
namespace Flapjack.NamespaceHOL

/-- Constructing an identifier from modules and a name is injective in both parts. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "mk_id_11"]
theorem mkId_eq {M N : Type} (left : List M) (name : N) (right : List M) (other : N) :
    mkId left name = mkId right other ↔ left = right ∧ name = other := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => simp [mkId]
    | cons head tail => simp [mkId]
  | cons head tail ih =>
    cases right with
    | nil => simp [mkId]
    | cons head' tail' => simp [mkId, ih, and_assoc]

/-- The module path of a constructed identifier is its module list. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "id_to_mods_mk_id"]
theorem idToMods_mkId {M N : Type} (modules : List M) (name : N) :
    idToMods (mkId modules name) = modules := by
  induction modules with
  | nil => rfl
  | cons head tail ih => simp [mkId, idToMods, ih]

/-- The name of a constructed identifier is its name. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "id_to_namemods_mk_id"]
theorem idToN_mkId {M N : Type} (modules : List M) (name : N) :
    idToN (mkId modules name) = name := by
  induction modules with
  | nil => rfl
  | cons head tail ih => simp [mkId, idToN, ih]

/-- Every identifier is constructed from its module path and name. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "mk_id_surj"]
theorem mkId_surjective {M N : Type} (id : Ident M N) :
    ∃ modules name, id = mkId modules name := by
  induction id with
  | short name => exact ⟨[], name, rfl⟩
  | long head rest ih =>
    obtain ⟨modules, name, rfl⟩ := ih
    exact ⟨head :: modules, name, rfl⟩

/-- Rebuilding an identifier from its own module path and name is the identity. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "mk_id_thm"]
theorem mkId_idToMods_idToN {M N : Type} (id : Ident M N) :
    mkId (idToMods id) (idToN id) = id := by
  induction id with
  | short name => rfl
  | long head rest ih => simp [mkId, idToMods, idToN, ih]

end Flapjack.NamespaceHOL
