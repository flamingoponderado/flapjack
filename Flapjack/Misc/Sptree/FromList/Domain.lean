module

public import Flapjack.Misc.Sptree.FromList
public import Mathlib.Data.List.Induction
public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order

@[expose] public section

/-! Domain of sequential sparse-tree construction. -/
namespace Flapjack

/-- HOL's recursive domain equations, established for the executable
lookup-based domain predicate. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "domain_def"]
theorem sptDomain_def {α : Type} :
    sptDomain (.ln : Spt α) = (∅ : Set Nat) ∧
    (∀ value : α, sptDomain (.ls value) = ({0} : Set Nat)) ∧
    (∀ left right : Spt α, sptDomain (.bn left right) =
      (fun n => 2 * n + 2) '' sptDomain left ∪ (fun n => 2 * n + 1) '' sptDomain right) ∧
    (∀ (left : Spt α) (value : α) (right : Spt α), sptDomain (.bs left value right) =
      {0} ∪ (fun n => 2 * n + 2) '' sptDomain left ∪ (fun n => 2 * n + 1) '' sptDomain right) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext key
    change sptMem key (.ln : Spt α) ↔ False
    exact iff_false_intro (sptMem_ln key)
  · intro value; ext key
    change sptMem key (.ls value) ↔ key = 0
    exact sptMem_ls key value
  · intro left right; ext key
    change sptMem key (.bn left right) ↔
      (∃ m, sptDomain left m ∧ 2 * m + 2 = key) ∨
        (∃ m, sptDomain right m ∧ 2 * m + 1 = key)
    simpa [sptMem, eq_comm] using sptMem_bn left right key
  · intro left value right; ext key
    change sptMem key (.bs left value right) ↔
      (key = 0 ∨ (∃ m, sptDomain left m ∧ 2 * m + 2 = key)) ∨
        (∃ m, sptDomain right m ∧ 2 * m + 1 = key)
    simpa [sptMem, eq_comm, or_assoc] using
      sptMem_bs left value right key

private theorem fromListFoldIndex {α : Type} (values : List α) (start : Nat) (tree : Spt α) :
    (values.foldl (fun (acc : Nat × Spt α) value => (acc.1 + 1, sptInsert acc.1 value acc.2))
      (start, tree)).1 = start + values.length := by
  induction values generalizing start tree with
  | nil => simp
  | cons value values ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    omega

/-- The domain of a sequentially constructed sparse tree is the initial
segment whose length is the input list length. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "domain_fromList"]
theorem sptDomainFromList {α : Type} (values : List α) :
    sptDomain (sptFromList values) = fun key => key < values.length := by
  induction values using List.reverseRecOn with
  | nil =>
    funext key
    simp [sptDomain, sptFromList]
  | append_singleton values value ih =>
    have inserted : sptFromList (values ++ [value]) =
        sptInsert values.length value (sptFromList values) := by
      simp only [sptFromList, List.foldl_append, List.foldl_cons, List.foldl_nil,
        fromListFoldIndex, Nat.zero_add]
    rw [inserted]
    funext key
    apply propext
    change sptMem key (sptInsert values.length value (sptFromList values)) ↔ _
    rw [sptMem_sptInsert]
    change key = values.length ∨ sptDomain (sptFromList values) key ↔ _
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

/-- Lookup in a sequential sparse tree follows the list's optional indexing.
This Flapjack helper packages the same lookup used by HOL's guarded EL theorem. -/
theorem sptLookupFromList_getElem? {α : Type} (values : List α) (key : Nat) :
    sptLookup key (sptFromList values) = values[key]? := by
  induction values using List.reverseRecOn with
  | nil => simp [sptFromList]
  | append_singleton values value ih =>
    have inserted : sptFromList (values ++ [value]) =
        sptInsert values.length value (sptFromList values) := by
      simp only [sptFromList, List.foldl_append, List.foldl_cons, List.foldl_nil,
        fromListFoldIndex, Nat.zero_add]
    rw [inserted]
    by_cases equal : key = values.length
    · subst key
      simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne values.length key value (sptFromList values) equal, ih]
      by_cases bound : key < values.length
      · simp [List.getElem?_append, bound]
      · have beyond : values.length < key := by omega
        simp [List.getElem?_append, bound, List.getElem?_eq_none, show 1 ≤ key - values.length by omega]

/-- A sequential sparse-tree lookup returns the corresponding list element in bounds. -/
@[hol "HOL/src/finite_maps/sptreeScript.sml" "lookup_fromList"]
theorem sptLookupFromList {α : Type} (key : Nat) (values : List α) :
    sptLookup key (sptFromList values) =
      if bound : key < values.length then some values[key] else none := by
  rw [sptLookupFromList_getElem?]
  split <;> simp_all

end Flapjack
