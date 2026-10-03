import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicCosts
import Std.Data.TreeMap.Lemmas

namespace Flapjack.WordAlloc
open Std.DTreeMap.Internal
open Std.DTreeMap.Internal.Impl

/-! Actual balanced TreeMap merge behavior used by the executed heuristic
counter join. Untagged implementation infrastructure without a HOL original.
The proof observes the real mergeWith fold; it does not replace its algorithm. -/

private def balanceView {β : Type} (tree : Std.TreeMap Nat β) : BalancedTree Nat (fun _ => β) :=
  ⟨tree.inner.inner, tree.inner.wf.balanced⟩

private def mergeEntry {β : Type} (f : Nat → β → β → β)
    (tree : Std.TreeMap Nat β) (entry : Nat × β) : Std.TreeMap Nat β :=
  tree.alter entry.1 (fun previous => match previous with
    | none => some entry.2
    | some value => some (f entry.1 value entry.2))

private theorem treeMapEq {β : Type} (left right : Std.TreeMap Nat β)
    (same : left.inner.inner = right.inner.inner) : left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      cases left with
      | mk left leftWf =>
        cases right with
        | mk right rightWf =>
          cases same
          rfl

/-- The actual internal balanced fold is the public alter fold over the actual
right map traversal. This equation retains the real balanced implementation. -/
theorem treeMapMergeWith_fold {β : Type} (f : Nat → β → β → β)
    (left right : Std.TreeMap Nat β) :
    left.mergeWith f right = right.toList.foldl (mergeEntry f) left := by
  apply treeMapEq
  change (Impl.Const.mergeWith f left.inner.inner right.inner.inner left.inner.wf.balanced).impl = _
  unfold Impl.Const.mergeWith
  rw [Impl.Const.foldl_eq_foldl_toList]
  have hom := List.foldl_hom (balanceView (β := β))
    (g₁ := mergeEntry f)
    (g₂ := fun tree entry =>
      (Impl.Const.alter entry.1 (fun previous => match previous with
        | none => some entry.2
        | some value => some (f entry.1 value entry.2)) tree.impl tree.balanced_impl).toBalancedTree)
    (l := right.toList) (init := left) (by intro tree entry; rfl)
  exact congrArg BalancedTree.impl hom


private theorem assocLookupAbsent {β : Type} (key : Nat) (entries : List (Nat × β))
    (missing : key ∉ entries.map Prod.fst) : sptAListLookup key entries = none := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨name, value⟩
      have parts : key ≠ name ∧ key ∉ rest.map Prod.fst := by simpa using missing
      simp only [sptAListLookup, parts.1, if_false, ih parts.2]

private theorem mergeFold_lookup {β : Type} (f : Nat → β → β → β)
    (entries : List (Nat × β)) (unique : (entries.map Prod.fst).Nodup)
    (tree : Std.TreeMap Nat β) (key : Nat) :
    (entries.foldl (mergeEntry f) tree)[key]? =
      match sptAListLookup key entries with
      | none => tree[key]?
      | some right => match tree[key]? with
        | none => some right
        | some left => some (f key left right) := by
  induction entries generalizing tree with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨name, value⟩
      have parts := List.nodup_cons.mp unique
      rw [List.foldl_cons, ih parts.2]
      by_cases same : key = name
      · subst key
        rw [assocLookupAbsent name rest parts.1]
        simp only [sptAListLookup, if_true, mergeEntry, Std.TreeMap.getElem?_alter_self]
      · have different : compare name key ≠ Ordering.eq := by
          intro equal
          exact same (Std.LawfulEqCmp.compare_eq_iff_eq.mp equal).symm
        simp only [sptAListLookup, same, if_false, mergeEntry,
          Std.TreeMap.getElem?_alter, different]

private theorem assocLookupTreeMap {β : Type} (tree : Std.TreeMap Nat β) (key : Nat) :
    sptAListLookup key tree.toList = tree[key]? := by
  cases found : tree[key]? with
  | none =>
      apply assocLookupAbsent
      simp only [Std.TreeMap.map_fst_toList_eq_keys, Std.TreeMap.mem_keys]
      intro member
      have present := Std.TreeMap.mem_iff_isSome_getElem?.mp member
      simp [found] at present
  | some value =>
      apply sptAListLookup_eq_of_mem_unique key value tree.toList
      · exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr found
      · intro other member
        have same := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
        rw [found] at same
        exact (Option.some.inj same).symm

/-- Exact lookup of the actual mergeWith: one-sided keys retain their payload,
and overlapping keys apply the merge function in left/right order. -/
theorem treeMapMergeWith_lookup {β : Type} (f : Nat → β → β → β)
    (left right : Std.TreeMap Nat β) (key : Nat) :
    (left.mergeWith f right)[key]? =
      match right[key]? with
      | none => left[key]?
      | some value => match left[key]? with
        | none => some value
        | some other => some (f key other value) := by
  rw [treeMapMergeWith_fold]
  have unique : (right.toList.map Prod.fst).Nodup := by
    rw [Std.TreeMap.map_fst_toList_eq_keys]
    exact Std.TreeMap.nodup_keys
  rw [mergeFold_lookup f right.toList unique left key, assocLookupTreeMap]

end Flapjack.WordAlloc

