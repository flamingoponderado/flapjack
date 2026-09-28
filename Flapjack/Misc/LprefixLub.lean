import Flapjack.Misc.LList

/-!
# HOL `lprefix_lub` (least upper bounds of lazy-list prefix chains)

Untagged rendering of HOL4's `examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml`
(HOL library, outside the CakeML submodule, so no `@[hol]` tags), plus HOL's
option-choice binder `some` (`HOL/src/coretypes/optionScript.sml:794`).  HOL sets
`'a llist set` are rendered as predicates `HolLList α → Prop`.  These are the
ingredients of the Pancake observational `semantics_def`s
(`build_lprefix_lub (IMAGE ... UNIV)`).  Noncomputable exactly where HOL uses
Hilbert choice.
-/

namespace Flapjack

open Classical in
/-- HOL `some P = if ?x. P x then SOME (@x. P x) else NONE`
    (`optionScript.sml:794-796`); under the guard, `Classical.choose` is a
    witness of `P` exactly as HOL's `@x. P x`. -/
noncomputable def holOptionSome {α : Type} (P : α → Prop) : Option α :=
  if h : ∃ x, P x then some (Classical.choose h) else none

theorem holOptionSome_some {α : Type} {P : α → Prop} {x : α}
    (h : holOptionSome P = some x) : P x := by
  unfold holOptionSome at h
  split at h
  · rename_i hex; cases h; exact Classical.choose_spec hex
  · cases h

theorem holOptionSome_none {α : Type} {P : α → Prop}
    (h : holOptionSome P = none) : ∀ x, ¬ P x := by
  unfold holOptionSome at h
  split at h
  · cases h
  · rename_i hn; exact fun x hx => hn ⟨x, hx⟩

namespace HolLList

variable {α : Type}

/-- HOL `lprefix_chain ls ⇔ !ll1 ll2. ll1 ∈ ls ∧ ll2 ∈ ls ⇒ LPREFIX ll1 ll2 ∨ LPREFIX ll2 ll1`
    (`lprefix_lubScript.sml:171-174`). -/
def lprefixChain (ls : HolLList α → Prop) : Prop :=
  ∀ ll1 ll2, ls ll1 → ls ll2 → lprefix ll1 ll2 ∨ lprefix ll2 ll1

/-- HOL `lprefix_chain_nth n ls = some x. ?l. l ∈ ls ∧ LNTH n l = SOME x`
    (`lprefix_lubScript.sml:200-203`). -/
noncomputable def lprefixChainNth (n : Nat) (ls : HolLList α → Prop) : Option α :=
  holOptionSome (fun x => ∃ l, ls l ∧ lnth n l = some x)

/-- HOL `lprefix_lub ls lub ⇔ (!ll. ll ∈ ls ⇒ LPREFIX ll lub) ∧
    (∀ub. (!ll. ll ∈ ls ⇒ LPREFIX ll ub) ⇒ LPREFIX lub ub)` (`lprefix_lubScript.sml:306-310`). -/
def lprefixLub (ls : HolLList α → Prop) (lub : HolLList α) : Prop :=
  (∀ ll, ls ll → lprefix ll lub) ∧ (∀ ub, (∀ ll, ls ll → lprefix ll ub) → lprefix lub ub)

/-- HOL `build_lprefix_lub_f ls n = OPTION_MAP (λx. (n+1, x)) (lprefix_chain_nth n ls)`
    (`lprefix_lubScript.sml:430-433`). -/
noncomputable def buildLprefixLubF (ls : HolLList α → Prop) (n : Nat) : Option (Nat × α) :=
  (lprefixChainNth n ls).map (fun x => (n + 1, x))

/-- HOL `build_lprefix_lub ls = LUNFOLD (build_lprefix_lub_f ls) 0`
    (`lprefix_lubScript.sml:435-438`). -/
noncomputable def buildLprefixLub (ls : HolLList α → Prop) : HolLList α :=
  lunfold (buildLprefixLubF ls) 0

/-! ### `rep`/`lnth` bridge lemmas

`HolLrepOk` makes `rep` downward-closed (a `none` persists), so `lnth` is exactly
`rep`.  These connect the `ltl`/`lhd`-based `lnth` to the `rep` function. -/

/-- A `none` at `k` forces a `none` at `k+1` (downward closure of `HolLrepOk`). -/
theorem rep_none_succ (ll : HolLList α) {k : Nat} (h : ll.rep k = none) :
    ll.rep (k + 1) = none := by
  rw [Option.eq_none_iff_forall_ne_some]
  intro v hv
  have hk' : (ll.rep (k + 1)) ≠ none := by rw [hv]; exact Option.some_ne_none v
  exact (Option.isSome_iff_ne_none.mp (ll.ok k (Option.isSome_iff_ne_none.mpr hk'))) h

/-- A `none` in the representation persists to every larger index. -/
theorem rep_none_of_le (ll : HolLList α) {m n : Nat} (hm : ll.rep m = none) (hle : m ≤ n) :
    ll.rep n = none := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hle
  clear hle
  induction d with
  | zero => simpa using hm
  | succ d ih =>
      rw [Nat.add_succ]
      exact rep_none_succ ll ih

/-- `lnth` reads the underlying representation. -/
theorem lnth_eq_rep (n : Nat) (ll : HolLList α) : lnth n ll = ll.rep n := by
  induction n generalizing ll with
  | zero => rfl
  | succ n ih =>
      show (ll.ltl.map (lnth n)).join = ll.rep (n + 1)
      cases h0 : ll.rep 0 with
      | none =>
          have hrep : ll.rep (n + 1) = none := rep_none_of_le ll h0 (Nat.zero_le _)
          have hltl : ll.ltl = none := by simp [ltl, lhd, h0]
          simp [hltl, hrep]
      | some hd =>
          have ht : ll.ltl =
              some ⟨fun k => ll.rep (k + 1), fun k hk => ll.ok (k + 1) hk⟩ := by
            simp [ltl, lhd, h0]
          rw [ht]
          simp only [Option.map_some, Option.join]
          rw [ih]
          rfl

/-- `lnth` is `none` from `m` on whenever it is `none` at `m` and `m ≤ n`. -/
theorem lnth_none_mono {m n : Nat} (ll : HolLList α) (h : lnth m ll = none) (hle : m ≤ n) :
    lnth n ll = none := by
  rw [lnth_eq_rep] at h ⊢
  exact rep_none_of_le ll h hle

/-- HOL `not_exists_lprefix_chain_nth`
    (`lprefix_lubScript.sml:215-218`), unconditional in Lean: if no member of the
    family has a value at `n`, then `lprefix_chain_nth n ls` is `none`. -/
theorem lprefixChainNth_eq_none {n : Nat} {ls : HolLList α → Prop}
    (h : ∀ l, ls l → lnth n l = none) : lprefixChainNth n ls = none := by
  unfold lprefixChainNth holOptionSome
  split
  · rename_i hx
    rcases hx with ⟨x, l, hl, hlth⟩
    rw [h l hl] at hlth
    cases hlth
  · rfl

/-- When `x` is the unique witness of `P`, `holOptionSome P` returns exactly
    `some x` (HOL's `some` picks a fixed but unknown witness; uniqueness pins it). -/
theorem holOptionSome_eq_some {P : α → Prop} {x : α} (hP : P x)
    (huniq : ∀ y, P y → y = x) : holOptionSome P = some x := by
  unfold holOptionSome
  split
  · rename_i h
    rw [huniq _ (Classical.choose_spec h)]
  · rename_i h
    exact absurd ⟨x, hP⟩ h

/-- HOL `lprefix_chain_nth_none_mono`
    (`lprefix_lubScript.sml:225-228`): over a chain, if the family has no value at
    `m` then it has none at any `n ≥ m`.  The chain binder is kept for HOL's
    shape; the Lean proof does not need it. -/
theorem lprefixChainNth_none_mono {m n : Nat} {ls : HolLList α → Prop}
    (_hchain : lprefixChain ls) (hle : m ≤ n) (hm : lprefixChainNth m ls = none) :
    lprefixChainNth n ls = none := by
  apply lprefixChainNth_eq_none
  intro l hl
  cases hnn : lnth n l with
  | none => rfl
  | some x =>
      have hmne : lnth m l ≠ none := by
        intro hmn
        rw [lnth_none_mono l hmn hle] at hnn
        cases hnn
      cases hmn : lnth m l with
      | none => exact absurd hmn hmne
      | some y => exact absurd ⟨l, hl, hmn⟩ ((holOptionSome_none hm) y)

end HolLList

end Flapjack
