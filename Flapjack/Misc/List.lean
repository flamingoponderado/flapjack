module

public import Flapjack.HolRef
public import Flapjack.Misc.ListEl
public import Batteries.Data.List.Basic

@[expose] public section

/-! List relation results from HOL list. -/
namespace Flapjack

/-- Exact port of HOL `oHD` (`HOL/src/list/src/listScript.sml:5474`): the head
    of a list, if any. -/
@[hol "HOL/src/list/src/listScript.sml" "oHD_def"]
def oHD {α : Type} : List α → Option α
  | [] => none
  | head :: _ => some head

/-- Updating corresponding positions with related values preserves the list relation. -/
@[hol "HOL/src/list/src/listScript.sml" "EVERY2_LUPDATE_same"]
theorem forall₂_set {α β : Type} (relation : α → β → Prop)
    (left : List α) (right : List β) (value : α) (nextValue : β) (index : Nat)
    (premise : relation value nextValue ∧ List.Forall₂ relation left right) :
    List.Forall₂ relation (left.set index value) (right.set index nextValue) := by
  obtain ⟨replacement, related⟩ := premise
  induction related generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.set_cons_zero]; exact .cons replacement tail
    | succ n => simp only [List.set_cons_succ]; exact .cons head (ih n)

/-- Flapjack infrastructure (no HOL original): related nonempty lists have
related HOL last elements, for any relation on the element type. -/
theorem holLast_related {α : Type} (inst : Nonempty α) (rel : α → α → Prop)
    {left right : List α} (related : List.Forall₂ rel left right) (nonempty : left ≠ []) :
    rel (@holLast α inst left) (@holLast α inst right) := by
  induction related with
  | nil => exact (nonempty rfl).elim
  | @cons first nextFirst rest nextRest head tail ih =>
    cases tail with
    | nil => simpa [holLast] using head
    | @cons second nextSecond tail nextTail nextHead restRel =>
      simp only [holLast]
      exact ih (by simp)

/-- Exact HOL `GENLIST` (`HOL/src/list/src/listScript.sml`):
`GENLIST f n = [f 0, …, f (n-1)]`, built by appending `f n` to the
previous list. -/
@[hol "HOL/src/list/src/listScript.sml" "GENLIST"]
def genlist {α : Type} (f : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => genlist f n ++ [f n]

/-- Flapjack infrastructure: the original `GENLIST` is the mapped range. -/
theorem genlist_range {α : Type} (f : Nat → α) (n : Nat) :
    genlist f n = (List.range n).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [genlist, ih, List.range_succ, List.map_append]
    rfl

/-- Original `GENLIST_eq_MAP`: a generated list equals a mapped list exactly
when the lengths agree and every index picks values related by the two
functions. -/
@[hol "cakeml/misc/miscScript.sml" "GENLIST_eq_MAP"
  (total_function_inhabitants := [β])]
theorem genlistEqMap {α β : Type} [Nonempty β] (f : Nat → α) (n : Nat) (g : β → α)
    (ls : List β) :
    genlist f n = ls.map g ↔ ls.length = n ∧ ∀ m, m < n → f m = g (holEl m ls) := by
  rw [genlist_range]
  constructor
  · intro h
    have hlen : ls.length = n := by
      have hmap := congrArg List.length h
      simpa using hmap.symm
    refine ⟨hlen, ?_⟩
    intro m hm
    have hget : ((List.range n).map f)[m]? = (ls.map g)[m]? := congrArg (fun l => l[m]?) h
    simp only [List.getElem?_map] at hget
    have hm2 : m < ls.length := by omega
    rw [List.getElem?_range hm, List.getElem?_eq_getElem hm2] at hget
    simp only [Option.map_some] at hget
    rw [holEl_eq_getElem m ls hm2]
    exact Option.some.inj hget
  · rintro ⟨hlen, hpt⟩
    apply List.ext_getElem
    · simp [hlen]
    · intro m h1 h2
      have hm : m < n := by simpa using h1
      have hm2 : m < ls.length := by simpa using h2
      rw [List.getElem_map, List.getElem_map, List.getElem_range (by simpa using hm)]
      rw [← holEl_eq_getElem m ls hm2]
      exact hpt m hm

/-- Original `ZIP_GENLIST1`: zipping a generated list with a list of the same
length regenerates the pairs index by index. -/
@[hol "cakeml/misc/miscScript.sml" "ZIP_GENLIST1"
  (total_function_inhabitants := [α])]
theorem zipGenlist1 {α β : Type} [Nonempty α] (l : List α) (f : Nat → β) (n : Nat)
    (hlen : l.length = n) :
    List.zip (genlist f n) l = genlist (fun x => (f x, holEl x l)) n := by
  rw [← hlen, genlist_range, genlist_range]
  apply List.ext_getElem
  · simp [List.length_zip]
  · intro i h1 h2
    have hi : i < l.length := by simpa using h2
    rw [List.getElem_zip, List.getElem_map, List.getElem_map,
      List.getElem_range (by simpa using hi)]
    rw [holEl_eq_getElem i l hi]

/-- Original `ALOOKUP_GENLIST`: looking up a key in the index/value list built
from a function returns that function's value at the key in bounds. -/
@[hol "cakeml/misc/miscScript.sml" "ALOOKUP_GENLIST"]
theorem alookupGenlist {α : Type} (f : Nat → α) (n k : Nat) :
    List.lookup k ((List.range n).map (fun i => (i, f i))) =
      if k < n then some (f k) else none := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    have hsingle : List.lookup k [(n, f n)] =
        if (k == n) = true then some (f n) else none := by
      rw [List.lookup_cons, List.lookup_nil]
      cases hb : (k == n) with
      | true => simp
      | false => simp
    rw [List.range_succ, List.map_append, List.lookup_append, ih]
    simp only [List.map_cons, List.map_nil]
    rw [hsingle]
    by_cases hlt : k < n
    · rw [if_pos hlt]
      have hne : ¬ ((k == n) = true) := by
        rw [beq_iff_eq]
        omega
      rw [if_neg hne]
      simp only [Option.or]
      rw [if_pos (by omega)]
    · by_cases heq : k = n
      · subst heq
        rw [if_neg hlt]
        rw [if_pos (by simp)]
        simp only [Option.or]
        rw [if_pos (by omega)]
      · have hne : ¬ ((k == n) = true) := by
          rw [beq_iff_eq]
          exact heq
        rw [if_neg hlt, if_neg hne]
        simp only [Option.or]
        rw [if_neg (by omega)]

end Flapjack