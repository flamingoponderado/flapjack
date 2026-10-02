import Flapjack.HolRef
import Flapjack.Misc.Sorting
import Flapjack.Basis.Pure.MlList

/-!
# HOL `mergesort`: sortedness and tail-recursive correctness

Lean counterpart of the sortedness and tail-correctness part of
`HOL/src/sort/mergesortScript.sml`: the non-tail `sort2`, `sort3`, `merge` and
`mergesortN`, the theorems that they sort, and the theorems relating the
tail-recursive `sort2_tail`, `sort3_tail`, `merge_tail` and `mergesortN_tail` (rendered,
untagged, in `Flapjack.Basis.Pure.MlList`) to them. As in `MlList`, a HOL relation
`R : 'a -> 'a -> bool` is a Lean `r : α → α → Bool`; where HOL uses `R` as a proposition
(`SORTED R`, `transitive R`, `total R`, `R x y`), Lean uses `fun x y => r x y = true`.
HOL `DIV2 n` is `n / 2` and `REV l acc` is `l.reverse ++ acc`.
-/

namespace Flapjack.Mergesort

open Flapjack Flapjack.Basis.Pure.MlList

/-- Exact HOL `sort2_def` (`mergesortScript.sml:38-44`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "sort2_def"]
def sort2 {α : Type} (r : α → α → Bool) (x y : α) : List α :=
  if r x y then [x, y] else [y, x]

/-- Exact HOL `sort3_def` (`mergesortScript.sml:46-62`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "sort3_def"]
def sort3 {α : Type} (r : α → α → Bool) (x y z : α) : List α :=
  if r x y then
    if r y z then [x, y, z]
    else if r x z then [x, z, y]
    else [z, x, y]
  else if r y z then
    if r x z then [y, x, z]
    else [y, z, x]
  else [z, y, x]

/-- Exact HOL `merge_def` (`mergesortScript.sml:64-73`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "merge_def"]
def merge {α : Type} (r : α → α → Bool) : List α → List α → List α
  | [], [] => []
  | l, [] => l
  | [], l => l
  | x :: l1, y :: l2 =>
      if r x y then x :: merge r l1 (y :: l2) else y :: merge r (x :: l1) l2
  termination_by l1 l2 => l1.length + l2.length
  decreasing_by all_goals simp +arith

/-- Exact HOL `mergesortN_def` (`mergesortScript.sml:75-91`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "mergesortN_def"]
def mergesortN {α : Type} (r : α → α → Bool) : Nat → List α → List α
  | 0, _ => []
  | 1, x :: _ => [x]
  | 1, [] => []
  | 2, x :: y :: _ => sort2 r x y
  | 2, [x] => [x]
  | 2, [] => []
  | 3, x :: y :: z :: _ => sort3 r x y z
  | 3, [x, y] => sort2 r x y
  | 3, [x] => [x]
  | 3, [] => []
  | n + 4, l =>
      let len1 := (n + 4) / 2
      merge r (mergesortN r ((n + 4) / 2) l) (mergesortN r (n + 4 - len1) (l.drop len1))
  termination_by n _ => n
  decreasing_by
    all_goals
      have hdiv : (n + 4) / 2 < n + 4 := Nat.div_lt_self (by omega) (by decide)
      omega

/-- Membership of `merge` (Flapjack infrastructure; a consequence of HOL `merge_perm`). -/
private theorem mem_merge {α : Type} (r : α → α → Bool) (z : α) :
    ∀ (l1 l2 : List α), z ∈ merge r l1 l2 ↔ z ∈ l1 ∨ z ∈ l2 := by
  intro l1 l2
  fun_induction merge r l1 l2 <;> simp_all [List.mem_cons, or_assoc, or_left_comm]

/-- Exact HOL `mem_sorted_append` (`mergesortScript.sml:18-31`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "mem_sorted_append"]
theorem memSortedAppend {α : Type} :
    ∀ (R : α → α → Prop) (l1 l2 : List α) (x y : α),
      holTransitive R ∧ holSorted R (l1 ++ l2) ∧ x ∈ l1 ∧ y ∈ l2 → R x y := by
  intro R l1
  induction l1 with
  | nil => intro _ _ _ ⟨_, _, h, _⟩; cases h
  | cons _a l1 ih =>
      intro l2 x y ⟨ht, hs, hx, hy⟩
      rw [List.cons_append, holSortedEq _ _ _ ht] at hs
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hs.2 y (List.mem_append_right _ hy)
      · exact ih l2 x y ⟨ht, hs.1, hx, hy⟩

/-- `SORTED` of a prefix (Flapjack infrastructure; HOL `SORTED_APPEND_GEN`). -/
private theorem sorted_prefix {α : Type} (R : α → α → Prop) :
    ∀ (l1 l2 : List α), holSorted R (l1 ++ l2) → holSorted R l1
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | _ :: b :: l1, l2, h => ⟨h.1, sorted_prefix R (b :: l1) l2 h.2⟩

/-- Exact HOL `sort2_sorted` (`mergesortScript.sml:216-224`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "sort2_sorted"]
theorem sort2Sorted {α : Type} :
    ∀ (r : α → α → Bool) (x y : α),
      holTotal (fun a b => r a b = true) → holSorted (fun a b => r a b = true) (sort2 r x y) := by
  intro r x y ht
  unfold sort2
  by_cases h : r x y = true
  · rw [if_pos h]; exact ⟨h, trivial⟩
  · rw [if_neg h]
    exact ⟨(ht x y).resolve_left h, trivial⟩

/-- Exact HOL `sort3_sorted` (`mergesortScript.sml:226-234`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "sort3_sorted"]
theorem sort3Sorted {α : Type} :
    ∀ (r : α → α → Bool) (x y z : α),
      holTotal (fun a b => r a b = true) →
      holSorted (fun a b => r a b = true) (sort3 r x y z) := by
  intro r x y z ht
  have t : ∀ a b, r a b = false → r b a = true := fun a b h =>
    (ht a b).resolve_left (by simp [h])
  unfold sort3
  cases hxy : r x y <;> cases hyz : r y z <;> cases hxz : r x z <;>
    simp only [↓reduceIte, Bool.false_eq_true] <;>
    first
    | exact ⟨‹_›, ‹_›, trivial⟩
    | exact ⟨hxy, hyz, trivial⟩
    | exact ⟨hxz, t _ _ hyz, trivial⟩
    | exact ⟨t _ _ hxz, hxy, trivial⟩
    | exact ⟨t _ _ hxy, hxz, trivial⟩
    | exact ⟨hyz, t _ _ hxz, trivial⟩
    | exact ⟨t _ _ hyz, t _ _ hxy, trivial⟩

/-- Exact HOL `merge_sorted` (`mergesortScript.sml:236-255`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "merge_sorted"]
theorem mergeSorted {α : Type} :
    ∀ (r : α → α → Bool) (l1 l2 : List α),
      holTransitive (fun a b => r a b = true) ∧ holTotal (fun a b => r a b = true) ∧
        holSorted (fun a b => r a b = true) l1 ∧ holSorted (fun a b => r a b = true) l2 →
      holSorted (fun a b => r a b = true) (merge r l1 l2) := by
  intro r l1 l2 ⟨htr, hto, h1, h2⟩
  fun_induction merge r l1 l2 with
  | case1 => trivial
  | case2 l _ => exact h1
  | case3 l _ => exact h2
  | case4 x l1 y l2 hxy ih =>
      rw [holSortedEq _ _ _ htr] at h1 ⊢
      refine ⟨ih h1.1 h2, fun z hz => ?_⟩
      have h2' := (holSortedEq _ _ _ htr).mp h2
      rcases (mem_merge r z l1 (y :: l2)).mp hz with hz | hz
      · exact h1.2 z hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · exact htr _ _ _ ⟨hxy, h2'.2 z hz⟩
  | case5 x l1 y l2 hxy ih =>
      have hyx : r y x = true := (hto x y).resolve_left hxy
      rw [holSortedEq _ _ _ htr] at h2 ⊢
      refine ⟨ih h1 h2.1, fun z hz => ?_⟩
      have h1' := (holSortedEq _ _ _ htr).mp h1
      rcases (mem_merge r z (x :: l1) l2).mp hz with hz | hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact hyx
        · exact htr _ _ _ ⟨hyx, h1'.2 z hz⟩
      · exact h2.2 z hz

/-- Exact HOL `mergesortN_sorted` (`mergesortScript.sml:257-280`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "mergesortN_sorted"]
theorem mergesortNSorted {α : Type} :
    ∀ (r : α → α → Bool) (n : Nat) (l : List α),
      holTotal (fun a b => r a b = true) ∧ holTransitive (fun a b => r a b = true) →
      holSorted (fun a b => r a b = true) (mergesortN r n l) := by
  intro r n l ⟨hto, htr⟩
  fun_induction mergesortN r n l <;>
    first
    | trivial
    | exact sort2Sorted r _ _ hto
    | exact sort3Sorted r _ _ _ hto
    | exact mergeSorted r _ _ ⟨htr, hto, ‹_›, ‹_›⟩

/-- Exact HOL `sort2_tail_correct` (`mergesortScript.sml:419-425`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "sort2_tail_correct"]
theorem sort2TailCorrect {α : Type} :
    ∀ (neg : Bool) (r : α → α → Bool) (x y : α),
      sort2Tail neg r x y = if neg then (sort2 r x y).reverse else sort2 r x y := by
  intro neg r x y
  cases neg <;> cases h : r x y <;> simp [sort2Tail, sort2, h]

/-- Exact HOL `sort3_tail_correct` (`mergesortScript.sml:427-432`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "sort3_tail_correct"]
theorem sort3TailCorrect {α : Type} :
    ∀ (neg : Bool) (r : α → α → Bool) (x y z : α),
      sort3Tail neg r x y z = if neg then (sort3 r x y z).reverse else sort3 r x y z := by
  intro neg r x y z
  cases neg <;> cases h1 : r x y <;> cases h2 : r y z <;> cases h3 : r x z <;>
    simp [sort3Tail, sort3, h1, h2, h3]

/-- Exact HOL `merge_tail_correct1` (`mergesortScript.sml:434-442`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "merge_tail_correct1"]
theorem mergeTailCorrect1 {α : Type} :
    ∀ (neg : Bool) (r : α → α → Bool) (l1 l2 acc : List α),
      neg = false → mergeTail neg r l1 l2 acc = (merge r l1 l2).reverse ++ acc := by
  intro neg r l1 l2 acc hneg
  subst hneg
  fun_induction mergeTail false r l1 l2 acc <;> simp_all [merge]

/-- Exact HOL `merge_empty` (`mergesortScript.sml:444-451`). HOL binds an `acc` that
occurs nowhere in the statement; its kernel type is a free type variable and it is kept as
the vacuous binder `(_acc : β)`. -/
@[hol "HOL/src/sort/mergesortScript.sml" "merge_empty"]
theorem mergeEmpty {α β : Type} :
    ∀ (r : α → α → Bool) (l : List α) (_acc : β), merge r l [] = l ∧ merge r [] l = l := by
  intro r l _
  cases l <;> simp [merge]

/-- Exact HOL `merge_last_lem1` (`mergesortScript.sml:453-464`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "merge_last_lem1"]
theorem mergeLastLem1 {α : Type} :
    ∀ (r : α → α → Bool) (l1 l2 : List α) (x : α),
      (∀ y, y ∈ l2 → ¬ r x y = true) → merge r (l1 ++ [x]) l2 = merge r l1 l2 ++ [x] := by
  intro r l1 l2 x h
  induction l2 generalizing l1 with
  | nil => rw [(mergeEmpty r _ ()).1, (mergeEmpty r _ ()).1]
  | cons y ys ihy =>
      have hy : r x y = false := by simpa using h y List.mem_cons_self
      have hys : ∀ z, z ∈ ys → ¬ r x z = true := fun z hz => h z (List.mem_cons_of_mem _ hz)
      induction l1 with
      | nil =>
          rw [List.nil_append, (mergeEmpty r _ ()).2]
          simp only [merge, hy, Bool.false_eq_true, ↓reduceIte]
          rw [show [x] = [] ++ [x] from rfl, ihy [] hys, (mergeEmpty r _ ()).2]
          rfl
      | cons a as iha =>
          rw [List.cons_append]
          by_cases hay : r a y = true
          · simp only [merge, hay, ↓reduceIte]
            rw [iha]
            rfl
          · simp only [merge, hay, Bool.false_eq_true, ↓reduceIte]
            rw [← List.cons_append, ihy (a :: as) hys]
            rfl

/-- Exact HOL `merge_last_lem2` (`mergesortScript.sml:466-477`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "merge_last_lem2"]
theorem mergeLastLem2 {α : Type} :
    ∀ (r : α → α → Bool) (l1 l2 : List α) (y : α),
      (∀ x, x ∈ l1 → r x y = true) → merge r l1 (l2 ++ [y]) = merge r l1 l2 ++ [y] := by
  intro r l1 l2 y h
  induction l1 generalizing l2 with
  | nil => rw [(mergeEmpty r _ ()).2, (mergeEmpty r _ ()).2]
  | cons a as iha =>
      have hay : r a y = true := h a List.mem_cons_self
      have has : ∀ z, z ∈ as → r z y = true := fun z hz => h z (List.mem_cons_of_mem _ hz)
      induction l2 with
      | nil =>
          have hi := iha [] has
          rw [List.nil_append] at hi
          rw [List.nil_append, (mergeEmpty r _ ()).1]
          simp only [merge, hay, ↓reduceIte]
          rw [hi, (mergeEmpty r _ ()).1]
          rfl
      | cons b bs ihb =>
          rw [List.cons_append]
          by_cases hab : r a b = true
          · simp only [merge, hab, ↓reduceIte]
            rw [← List.cons_append, iha (b :: bs) has]
            rfl
          · simp only [merge, hab, Bool.false_eq_true, ↓reduceIte]
            rw [ihb]
            rfl

/-- Exact HOL `merge_tail_correct2` (`mergesortScript.sml:479-506`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "merge_tail_correct2"]
theorem mergeTailCorrect2 {α : Type} :
    ∀ (neg : Bool) (r : α → α → Bool) (l1 l2 acc : List α),
      neg = true ∧ holTransitive (fun a b => r a b = true) ∧
        holSorted (fun a b => r a b = true) l1.reverse ∧
        holSorted (fun a b => r a b = true) l2.reverse →
      mergeTail neg r l1 l2 acc = merge r l1.reverse l2.reverse ++ acc := by
  intro neg r l1 l2 acc ⟨hneg, htr, h1, h2⟩
  subst hneg
  fun_induction mergeTail true r l1 l2 acc with
  | case1 acc => simp [merge]
  | case2 l acc hl => simp [(mergeEmpty r _ ()).1]
  | case3 l acc hl =>
      cases l with
      | nil => exact absurd rfl hl
      | cons _ _ => simp [(mergeEmpty r _ ()).2]
  | case4 x l1 y l2 acc hxy ih =>
      have hxy' : r x y = false := by simpa using hxy
      simp only [List.reverse_cons] at h1 h2 ih ⊢
      rw [ih (sorted_prefix _ _ _ h1) h2,
        mergeLastLem1 r l1.reverse (l2.reverse ++ [y]) x (fun z hz hxz => ?_)]
      · simp
      · rcases List.mem_append.mp hz with hz | hz
        · have hzy : r z y = true :=
            memSortedAppend _ _ _ z y ⟨htr, h2, hz, List.mem_singleton_self y⟩
          have hxy2 : r x y = true := htr _ _ _ ⟨hxz, hzy⟩
          rw [hxy'] at hxy2
          cases hxy2
        · rw [List.mem_singleton.mp hz, hxy'] at hxz
          cases hxz
  | case5 x l1 y l2 acc hxy ih =>
      have hxy' : r x y = true := by simpa using hxy
      simp only [List.reverse_cons] at h1 h2 ih ⊢
      rw [ih h1 (sorted_prefix _ _ _ h2),
        mergeLastLem2 r (l1.reverse ++ [x]) l2.reverse y (fun z hz => ?_)]
      · simp
      · rcases List.mem_append.mp hz with hz | hz
        · have hzx : r z x = true :=
            memSortedAppend _ _ _ z x ⟨htr, h1, hz, List.mem_singleton_self x⟩
          exact htr _ _ _ ⟨hzx, hxy'⟩
        · rw [List.mem_singleton.mp hz]
          exact hxy'

/-- Exact HOL `mergesortN_correct` (`mergesortScript.sml:508-526`). -/
@[hol "HOL/src/sort/mergesortScript.sml" "mergesortN_correct"]
theorem mergesortNCorrect {α : Type} :
    ∀ (negate : Bool) (r : α → α → Bool) (n : Nat) (l : List α),
      holTotal (fun a b => r a b = true) ∧ holTransitive (fun a b => r a b = true) →
      mergesortNTail negate r n l =
        if negate then (mergesortN r n l).reverse else mergesortN r n l := by
  intro negate r n l ⟨hto, htr⟩
  fun_induction mergesortNTail negate r n l with
  | case1 negate l => cases negate <;> simp [mergesortN]
  | case2 negate x l => cases negate <;> simp [mergesortN]
  | case3 negate => cases negate <;> simp [mergesortN]
  | case4 negate x y l => simp only [mergesortN, sort2TailCorrect]
  | case5 negate x => cases negate <;> simp [mergesortN]
  | case6 negate => cases negate <;> simp [mergesortN]
  | case7 negate x y z l => simp only [mergesortN, sort3TailCorrect]
  | case8 negate x y => simp only [mergesortN, sort2TailCorrect]
  | case9 negate x => cases negate <;> simp [mergesortN]
  | case10 negate => cases negate <;> simp [mergesortN]
  | case11 negate n l len1 neg ihA ihB =>
      rw [ihA, ihB, mergesortN]
      simp only [len1, neg]
      cases negate with
      | false =>
          simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
          rw [mergeTailCorrect2 true r _ _ [] ⟨rfl, htr, by
              rw [List.reverse_reverse]; exact mergesortNSorted r _ _ ⟨hto, htr⟩, by
              rw [List.reverse_reverse]; exact mergesortNSorted r _ _ ⟨hto, htr⟩⟩,
            List.reverse_reverse, List.reverse_reverse, List.append_nil]
      | true =>
          simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true]
          rw [mergeTailCorrect1 false r _ _ [] rfl, List.append_nil]

end Flapjack.Mergesort
