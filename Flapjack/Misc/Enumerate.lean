module

public import Flapjack.HolRef
public import Flapjack.Basis.Pure.MlList.MapIndexed
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Consecutive indexing from the CakeML misc theory. -/
namespace Flapjack

open Flapjack.Basis.Pure.MlList

/-- Pair each list element with its index, starting at `offset`. -/
@[simp, hol "cakeml/misc/miscScript.sml" "enumerate_def"]
def enumerate {A : Type} : Nat → List A → List (Nat × A)
  | _, [] => []
  | offset, x :: xs => (offset, x) :: enumerate (offset + 1) xs

/-- Original `LENGTH_enumerate`: enumerating preserves the list length. -/
@[hol "cakeml/misc/miscScript.sml" "LENGTH_enumerate"]
theorem length_enumerate {A : Type} (xs : List A) (k : Nat) :
    (enumerate k xs).length = xs.length := by
  induction xs generalizing k with
  | nil => simp [enumerate]
  | cons x rest ih => simp only [enumerate, List.length_cons, ih]

/-- Original `MEM_enumerate_IMP`: an enumerated pair's second component is a
member of the list. -/
@[hol "cakeml/misc/miscScript.sml" "MEM_enumerate_IMP"]
theorem mem_enumerate_imp {A : Type} (ls : List A) (k : Nat) (i : Nat) (e : A) :
    (i, e) ∈ enumerate k ls → e ∈ ls := by
  intro h
  induction ls generalizing k with
  | nil => simp [enumerate] at h
  | cons x rest ih =>
    simp only [enumerate, List.mem_cons] at h ⊢
    rcases h with h | h
    · exact Or.inl (Prod.mk.inj h).2
    · exact Or.inr (ih (k + 1) h)

/-- Original `EL_enumerate`: the index stored in an enumerated pair is the
position shifted by the starting offset. -/
@[hol "cakeml/misc/miscScript.sml" "EL_enumerate"
  (total_function_inhabitants := [α])]
theorem el_enumerate {α : Type} [Nonempty α] (xs : List α) (n k : Nat)
    (h : n < xs.length) : holEl n (enumerate k xs) = (n + k, holEl n xs) := by
  induction xs generalizing n k with
  | nil => simp at h
  | cons x rest ih =>
    cases n with
    | zero => simp [enumerate, holEl, holHd]
    | succ n =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      simp only [enumerate, holEl_cons_succ]
      rw [ih n (k + 1) h]
      rw [show n + (k + 1) = n + 1 + k by omega]

/-- Original `ALOOKUP_enumerate`: looking up an index in an enumeration gives
the element at that position when the index lies in the enumerated range. -/
@[hol "cakeml/misc/miscScript.sml" "ALOOKUP_enumerate"
  (total_function_inhabitants := [α])]
theorem alookupEnumerate {α : Type} [Nonempty α] (ls : List α) (k x : Nat) :
    List.lookup x (enumerate k ls) =
      if k ≤ x ∧ x < ls.length + k then some (holEl (x - k) ls) else none := by
  induction ls generalizing k with
  | nil =>
    rw [enumerate]
    simp
  | cons a as ih =>
    rw [enumerate, List.lookup_cons]
    simp only [List.length_cons]
    split
    · rename_i hbeq
      have hk : x = k := by
        rw [beq_iff_eq] at hbeq
        exact hbeq
      subst hk
      rw [if_pos (by omega)]
      rw [Nat.sub_self]
      rfl
    · rename_i hbeq
      have hne : x ≠ k := by
        simp at hbeq
        exact hbeq
      rw [ih (k + 1)]
      by_cases hcond : k ≤ x ∧ x < as.length + 1 + k
      · have h1 : k ≤ x := hcond.1
        have h2 : x < as.length + 1 + k := hcond.2
        have hcond2 : k + 1 ≤ x ∧ x < as.length + (k + 1) := ⟨by omega, by omega⟩
        rw [if_pos hcond2, if_pos hcond]
        rw [show x - k = (x - (k + 1)) + 1 by omega]
        rw [holEl_cons_succ]
      · have hcond2 : ¬ (k + 1 ≤ x ∧ x < as.length + (k + 1)) := by omega
        rw [if_neg hcond2, if_neg hcond]

/-- The shifted form of `MAP_enumerate_MAPi` and `MAPi_enumerate_MAP`: mapping
over an enumeration started at `k` is `holMapi` with the offset added. -/
private theorem map_enumerate_eq_holMapi {α β : Type} (f : Nat × α → β) :
    ∀ (xs : List α) (k : Nat),
      List.map f (enumerate k xs) = holMapi (fun n e => f (n + k, e)) xs
  | [], _ => rfl
  | x :: rest, k => by
      simp only [enumerate, List.map_cons, holMapi]
      rw [map_enumerate_eq_holMapi f rest (k + 1)]
      simp only [Nat.zero_add]
      have hfun : (fun n e => f (n + (k + 1), e)) = fun n e => f (n + 1 + k, e) := by
        funext n e
        rw [show n + (k + 1) = n + 1 + k by omega]
      rw [hfun]

/-- Original `MAP_enumerate_MAPi`: mapping over an enumeration from zero is
HOL's `MAPi` with the pair taken apart. -/
@[hol "cakeml/misc/miscScript.sml" "MAP_enumerate_MAPi"]
theorem map_enumerate_holMapi {α β : Type} (f : Nat × α → β) (xs : List α) :
    List.map f (enumerate 0 xs) = holMapi (fun n e => f (n, e)) xs := by
  simpa using map_enumerate_eq_holMapi f xs 0

/-- Original `MAPi_enumerate_MAP`: HOL's `MAPi` is a map over the enumeration
from zero. -/
@[hol "cakeml/misc/miscScript.sml" "MAPi_enumerate_MAP"]
theorem holMapi_eq_map_enumerate {α β : Type} (f : Nat → α → β) (xs : List α) :
    holMapi f xs = List.map (fun p : Nat × α => f p.1 p.2) (enumerate 0 xs) := by
  simpa using (map_enumerate_eq_holMapi (fun p : Nat × α => f p.1 p.2) xs 0).symm

/-- Every index produced by an enumeration is at least its start offset. -/
private theorem fst_enumerate_ge {A : Type} (j : Nat) (xs : List A) :
    ∀ p ∈ enumerate j xs, j ≤ p.1 := by
  induction xs generalizing j with
  | nil => simp
  | cons x rest ih =>
    intro p hp
    simp only [enumerate, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · have hge := ih (j + 1) p hp
      omega

/-- Flapjack infrastructure: the general-offset form of `MEM_enumerate`, proved
by induction over the offset so that the tail case can shift it by one. -/
private theorem memEnumerateAux {α : Type} [Nonempty α] :
    ∀ (xs : List α) (k i : Nat) (e : α), i < xs.length →
      ((i + k, e) ∈ enumerate k xs ↔ holEl i xs = e) := by
  intro xs
  induction xs with
  | nil =>
    intro k i e hi
    simp at hi
  | cons a as ih =>
    intro k i e hi
    have henum : enumerate k (a :: as) = (k, a) :: enumerate (k + 1) as := by
      rw [enumerate]
    cases i with
    | zero =>
      rw [henum, List.mem_cons, Nat.zero_add]
      constructor
      · rintro (h | h)
        · have hea : e = a := (Prod.mk.inj h).2
          exact hea.symm
        · exact absurd (fst_enumerate_ge (k + 1) as (k, e) h) (by omega)
      · intro h
        exact Or.inl (Prod.ext rfl h.symm)
    | succ j =>
      have hlt : j < as.length := by simpa using hi
      rw [henum, List.mem_cons]
      rw [show j + 1 + k = j + (k + 1) by omega]
      rw [show holEl (j + 1) (a :: as) = holEl j as by rw [holEl_cons_succ]]
      constructor
      · rintro (h | h)
        · have h1 : j + (k + 1) = k := (Prod.mk.inj h).1
          omega
        · exact (ih (k + 1) j e hlt).mp h
      · intro h
        exact Or.inr ((ih (k + 1) j e hlt).mpr h)

/-- Original `MEM_enumerate`: an in-range index is enumerated with the element
at that position. -/
@[hol "cakeml/misc/miscScript.sml" "MEM_enumerate"
  (total_function_inhabitants := [α])]
theorem memEnumerate {α : Type} [Nonempty α] (xs : List α) (i : Nat) (e : α)
    (hi : i < xs.length) : ((i, e) ∈ enumerate 0 xs ↔ holEl i xs = e) := by
  simpa using memEnumerateAux xs 0 i e hi

/-- Original `ALL_DISTINCT_MAP_FST_enumerate`: the indices of an enumeration
are distinct. -/
@[hol "cakeml/misc/miscScript.sml" "ALL_DISTINCT_MAP_FST_enumerate"]
theorem nodup_map_fst_enumerate {A : Type} (k : Nat) (ls : List A) :
    ((enumerate k ls).map Prod.fst).Nodup := by
  induction ls generalizing k with
  | nil => simp
  | cons x xs ih =>
    simp only [enumerate, List.map_cons]
    rw [List.nodup_cons]
    constructor
    · intro hmem
      obtain ⟨p, hp, hfst⟩ := List.mem_map.mp hmem
      have hge := fst_enumerate_ge (k + 1) xs p hp
      omega
    · exact ih (k + 1)

/-- Original `MAP_FST_enumerate`: the keys of an enumeration are the shifted
indices. -/
@[hol "cakeml/misc/miscScript.sml" "MAP_FST_enumerate"]
theorem mapFstEnumerate {A : Type} (k : Nat) :
    ∀ ls : List A,
      (enumerate k ls).map Prod.fst = (List.range ls.length).map (fun i => k + i)
  | [] => rfl
  | x :: xs => by
      rw [enumerate, List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_cons]
      rw [mapFstEnumerate (k + 1) xs, Nat.add_zero]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      omega

end Flapjack
