module

public import Flapjack.NamespaceHOL
public import Flapjack.NamespaceProps.Ident
public import Flapjack.NamespaceProps.LiftLookup

@[expose] public section

/-! Lookup through a right fold of module lifting. -/
namespace Flapjack.NamespaceHOL

/-- Folding lifts along a module path keeps the innermost short-name lookup. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_FOLDR_nsLift"]
theorem nsLookup_foldr_nsLift {M N V : Type} [DecidableEq M] [DecidableEq N]
    (e : Namespace M N V) (p : List M) (k : N) :
    nsLookup (p.foldr nsLift e) (mkId p k) = nsLookup e (.short k) := by
  induction p with
  | nil => rfl
  | cons mn p ih => simp [mkId, nsLift, nsLookup, ih]

/-- Flapjack infrastructure: a lifted identifier equation peels its leading
module. -/
private theorem mkId_cons_eq {M N : Type} (mn : M) (rest : Ident M N) (p p2 : List M)
    (n : N) : Ident.long mn rest = mkId ((mn :: p) ++ p2) n ↔ rest = mkId (p ++ p2) n := by
  simp [mkId]

/-- Flapjack infrastructure: a successful lookup can be re-expressed through the
identifier decomposition `mk_id (id_to_mods id) (id_to_n id)`. -/
private theorem lookup_exists_mkId {M N V : Type} [DecidableEq M] [DecidableEq N]
    (e : Namespace M N V) (rest : Ident M N) (v : V) :
    (nsLookup e rest = some v) ↔
      ∃ (p2 : List M) (n : N), rest = mkId p2 n ∧ nsLookup e (mkId p2 n) = some v := by
  constructor
  · intro found
    exact ⟨idToMods rest, idToN rest, (mkId_idToMods_idToN rest).symm,
      by simpa [mkId_idToMods_idToN] using found⟩
  · rintro ⟨p2, n, sameId, found⟩
    rw [sameId]
    exact found

/-- A successful lookup through a right fold of module lifting is either the
unlifted lookup or an unlifted lookup at the remaining module path. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_FOLDR_nsLift_some"]
theorem nsLookup_foldr_nsLift_some {M N V : Type} [DecidableEq M] [DecidableEq N]
    (e : Namespace M N V) (p : List M) (id : Ident M N) (v : V) :
    nsLookup (p.foldr nsLift e) id = some v ↔
      (p = [] ∧ nsLookup e id = some v) ∨
      (p ≠ [] ∧ ∃ (p2 : List M) (n : N), id = mkId (p ++ p2) n ∧
        nsLookup e (mkId p2 n) = some v) := by
  induction p generalizing id with
  | nil => simp
  | cons mn p ih =>
    cases id with
    | short name => simp [nsLift, nsLookup, mkId]
    | long m' rest =>
      simp only [List.foldr_cons, nsLookup_nsLift]
      by_cases same : mn = m'
      · subst same
        rw [if_pos rfl, ih rest]
        constructor
        · rintro (⟨empty, found⟩ | ⟨ne, p2, n, sameId, found⟩)
          · subst empty
            obtain ⟨p2, n, sameId, found⟩ := (lookup_exists_mkId e rest v).mp found
            exact Or.inr ⟨by simp, p2, n, (mkId_cons_eq mn rest [] p2 n).mpr sameId, found⟩
          · exact Or.inr ⟨by simp, p2, n, (mkId_cons_eq mn rest p p2 n).mpr sameId, found⟩
        · rintro (⟨nilEq, _⟩ | ⟨_, p2, n, sameId, found⟩)
          · simp at nilEq
          · have sameRest : rest = mkId (p ++ p2) n := (mkId_cons_eq mn rest p p2 n).mp sameId
            by_cases empty : p = []
            · subst empty
              exact Or.inl ⟨rfl, sameRest ▸ found⟩
            · exact Or.inr ⟨empty, p2, n, sameRest, found⟩
      · rw [if_neg same]
        constructor
        · intro h
          simp at h
        · rintro (⟨nilEq, _⟩ | ⟨_, p2, n, sameId, found⟩)
          · simp at nilEq
          · simp only [List.cons_append, mkId] at sameId
            simp [Ne.symm same] at sameId

/-- A failed module lookup through a right fold of module lifting, when the two
paths are prefix-related, reaches a failed lookup at the remaining path. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookupMod_FOLDR_nsLift_none"]
theorem nsLookupMod_foldr_nsLift_none {M N V : Type} [DecidableEq M]
    (e : Namespace M N V) (p1 p2 : List M) :
    nsLookupMod (p1.foldr nsLift e) p2 = none ↔
      (List.IsPrefix p1 p2 ∨ List.IsPrefix p2 p1) →
        ∃ p3, p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none := by
  induction p1 generalizing p2 with
  | nil =>
    constructor
    · intro h
      intro _
      exact ⟨p2, by simp, h⟩
    · intro h
      obtain ⟨p3, same, h3⟩ := h (Or.inl ⟨p2, by simp⟩)
      simpa [same] using h3
  | cons mn p1 ih =>
    cases p2 with
    | nil =>
      constructor
      · intro h
        simp [nsLookupMod] at h
      · intro h
        obtain ⟨p3, same, _⟩ := h (Or.inr ⟨mn :: p1, rfl⟩)
        simp at same
    | cons mn' rest =>
      simp only [List.foldr_cons, nsLookupMod_nsLift]
      by_cases sameModule : mn = mn'
      · subst sameModule
        rw [if_pos rfl]
        have prefLeft : List.IsPrefix (mn :: p1) (mn :: rest) ↔ List.IsPrefix p1 rest := by
          constructor
          · rintro ⟨t, same⟩
            exact ⟨t, by simpa using same⟩
          · rintro ⟨t, same⟩
            exact ⟨t, by simp [same]⟩
        have prefRight : List.IsPrefix (mn :: rest) (mn :: p1) ↔ List.IsPrefix rest p1 := by
          constructor
          · rintro ⟨t, same⟩
            exact ⟨t, by simpa using same⟩
          · rintro ⟨t, same⟩
            exact ⟨t, by simp [same]⟩
        rw [prefLeft, prefRight]
        constructor
        · intro h
          intro pref
          obtain ⟨p3, same, h3⟩ := (ih rest).mp h pref
          exact ⟨p3, by simpa using same, h3⟩
        · intro h
          apply (ih rest).mpr
          intro pref
          obtain ⟨p3, same, h3⟩ := h pref
          exact ⟨p3, by simpa using same, h3⟩
      · rw [if_neg sameModule]
        constructor
        · intro _
          intro pref
          rcases pref with ⟨t, same⟩ | ⟨t, same⟩
          · simp only [List.cons_append, List.cons.injEq] at same
            exact (sameModule same.1).elim
          · simp only [List.cons_append, List.cons.injEq] at same
            exact (sameModule same.1.symm).elim
        · intro _
          rfl

end Flapjack.NamespaceHOL
