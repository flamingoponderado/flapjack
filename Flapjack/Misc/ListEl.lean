import Flapjack.HolRef
import Flapjack.HolArb

/-!
# HOL list `HD` and `EL`

Exact ports of HOL `HD` (`HOL/src/list/src/listScript.sml:128-130`) and
`EL_def` (`listScript.sml:225-228`), cited in the pinned upstream HOL
submodule. `HD` has only the `h::t` clause, so `HD []` is an unspecified value
of the (inhabited) element type: `holHdNil` aliases the shared opaque
`holArb` at that type. This preserves equality with other missing clauses
completed by the same HOL `ARB`, without choosing a concrete value.
`EL 0 l = HD l` and `EL (SUC n) l = EL n (TL l)` with
HOL `TL` as `List.tail` (`TL [] = []`, `TL_DEF` 132-135), so `EL n l` past the
end of `l` is that same unspecified value; under the bound `holEl n l` is the
ordinary `l[n]` (`holEl_eq_getElem`).
-/

namespace Flapjack

/-- HOL's unspecified `HD []` at each (inhabited) type. -/
noncomputable abbrev holHdNil (α : Type) [Nonempty α] : α := holArb α

/-- Exact HOL `HD` (`listScript.sml:128-130`); the missing `[]` clause is the
unspecified `holHdNil`. -/
@[hol "HOL/src/list/src/listScript.sml" "HD"]
noncomputable def holHd {α : Type} [Nonempty α] : List α → α
  | [] => holHdNil α
  | h :: _ => h

/-- Representation infrastructure for the independently unspecified `LAST []`.
There is no separate HOL declaration for this residual value: the primitive
recursive specification `LAST_DEF` constrains only cons lists. This dedicated
opaque constant retains its per-type identity without equating it to `HD []`
or the distinct HOL `ARB` constant. -/
noncomputable opaque holLastNil (α : Type) [Nonempty α] : α

/-- Exact HOL `LAST_DEF` (`listScript.sml:2052-2054`). The cons equation is
implemented by singleton/longer-cons matching; the unspecified empty-list
value is retained independently, without a concrete or shared `ARB` default. -/
@[hol "HOL/src/list/src/listScript.sml" "LAST_DEF"]
noncomputable def holLast {α : Type} [Nonempty α] : List α → α
  | [] => holLastNil α
  | [h] => h
  | _ :: t@(_ :: _) => holLast t

/-- Flapjack equation relating constructor matching to HOL's equality-guarded
cons clause; this is comparison infrastructure for `LAST_DEF`, not a separately
named upstream theorem. -/
theorem holLast_cons {α : Type} [Nonempty α] (h : α) (t : List α) :
    holLast (h :: t) = if t = [] then h else holLast t := by
  classical
  cases t <;> simp [holLast]

/-- Complete original singleton and longer-cons conjunction. -/
@[hol "HOL/src/list/src/listScript.sml" "LAST_CONS"]
theorem holLastCons {α : Type} [Nonempty α] :
    (∀ x : α, holLast [x] = x) ∧
    (∀ (x y : α) (z : List α), holLast (x :: y :: z) = holLast (y :: z)) := by
  constructor <;> intros <;> simp only [holLast]

/-- Exact HOL `EL_def` (`listScript.sml:225-228`). -/
@[hol "HOL/src/list/src/listScript.sml" "EL_def"]
noncomputable def holEl {α : Type} [Nonempty α] : Nat → List α → α
  | 0, l => holHd l
  | n + 1, l => holEl n l.tail

theorem holEl_eq_getElem {α : Type} [Nonempty α] :
    ∀ (n : Nat) (l : List α) (h : n < l.length), holEl n l = l[n]'h
  | 0, x :: _, _ => rfl
  | n + 1, _ :: l, h => by
      simp only [holEl, List.tail_cons, List.getElem_cons_succ]
      exact holEl_eq_getElem n l (by simp at h; omega)

theorem holEl_of_length_le {α : Type} [Nonempty α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → holEl n l = holHdNil α
  | 0, [], _ => rfl
  | n + 1, [], _ => by
      simp only [holEl, List.tail_nil]
      exact holEl_of_length_le n [] (by simp)
  | n + 1, _ :: l, h => by
      simp only [holEl, List.tail_cons]
      exact holEl_of_length_le n l (by simp at h; omega)

theorem holEl_cons_succ {α : Type} [Nonempty α] (x : α) (l : List α) (n : Nat) :
    holEl (n + 1) (x :: l) = holEl n l := rfl

theorem holEl_set {α : Type} [Nonempty α] (l : List α) (i j : Nat) (v : α) (hi : i < l.length) :
    holEl j (l.set i v) = if i = j then v else holEl j l := by
  by_cases hj : j < l.length
  · rw [holEl_eq_getElem j _ (by simpa using hj), holEl_eq_getElem j l hj, List.getElem_set]
  · rw [holEl_of_length_le j _ (by simp; omega), holEl_of_length_le j l (by omega)]
    rw [if_neg (by omega)]

end Flapjack
