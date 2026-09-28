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

/-- The tail of a cons exposes the shifted representation. Untagged Flapjack
    infrastructure used to relate `lprefix` (defined via `toList`/`ltake`) to the
    representation `rep`/`lnth`; HOL's `llist` library is outside the cakeml
    submodule, so there is no taggable HOL original. -/
theorem ltl_rep {ll tl : HolLList α} (h : ll.ltl = some tl) (j : Nat) :
    tl.rep j = ll.rep (j + 1) := by
  cases h0 : ll.rep 0 with
  | none => simp [ltl, lhd, h0] at h
  | some hd =>
      simp only [ltl, lhd, h0] at h
      injection h with h'
      subst h'
      rfl

/-- `ltake` reads the representation: if `ltake k ll = some xs` then `xs` has
    length `k` and `ll.rep i = some (xs[i])` for every in-range `i`.  Untagged
    Flapjack infrastructure (no taggable HOL original). -/
theorem ltake_spec (k : Nat) (ll : HolLList α) (xs : List α)
    (h : ltake k ll = some xs) :
    xs.length = k ∧ ∀ i (hi : i < xs.length), ll.rep i = some xs[i] := by
  induction k generalizing ll xs with
  | zero =>
      simp only [ltake] at h
      injection h with hxs
      subst hxs
      exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | succ k ih =>
      cases h0 : ll.rep 0 with
      | none => simp [ltake, lhd, h0] at h
      | some hd =>
          cases h1 : ll.ltl with
          | none => simp [ltake, lhd, h0, h1] at h
          | some tl =>
              cases hrest : ltake k tl with
              | none => simp [ltake, lhd, h0, h1, hrest] at h
              | some rest =>
                  simp only [ltake, lhd, h0, h1, hrest] at h
                  injection h with hxs
                  subst hxs
                  obtain ⟨hlen, hrep⟩ := ih tl rest hrest
                  refine ⟨by simp [hlen], ?_⟩
                  intro i hi
                  cases i with
                  | zero => simp [h0]
                  | succ j =>
                      have hj : j < rest.length := by simpa [hlen] using hi
                      rw [← ltl_rep h1 j]
                      simpa using hrep j hj

/-- A finite lazy list has a length relation witness. -/
theorem exists_LLengthRel_of_LFinite {ll : HolLList α} (h : LFinite ll) :
    ∃ n, LLengthRel ll n :=
  LFinite.rec (motive := fun ll _ => ∃ n, LLengthRel ll n)
    ⟨0, LLengthRel.lnil⟩
    (fun hd t _ ih => by obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, LLengthRel.lcons hd n t hn⟩)
    h

/-- For a finite lazy list, `llength` returns a length relation witness. -/
theorem llength_spec {ll : HolLList α} (h : LFinite ll) :
    ∃ n, llength ll = some n ∧ LLengthRel ll n := by
  have hex : ∃ n, LLengthRel ll n := exists_LLengthRel_of_LFinite h
  refine ⟨Classical.epsilon (fun n => LLengthRel ll n), ?_, Classical.epsilon_spec hex⟩
  unfold llength
  rw [if_pos h]

/-- Beyond a length relation bound the representation is `none`. -/
theorem rep_none_of_LLengthRel {ll : HolLList α} {n : Nat} (h : LLengthRel ll n) :
    ∀ i, n ≤ i → ll.rep i = none :=
  LLengthRel.rec (motive := fun ll n _ => ∀ i, n ≤ i → ll.rep i = none)
    (fun i _ => rfl)
    (fun hd k t _ ih i hi => by
      cases i with
      | zero => exact absurd hi (Nat.not_succ_le_zero k)
      | succ j =>
          have hj : k ≤ j := Nat.le_of_succ_le_succ hi
          have hshift : (lcons hd t).rep (j + 1) = t.rep j := by simp [lcons]
          rw [hshift]
          exact ih j hj)
    h

/-- `toList ll = some xs` exposes the representation as `xs` with `none` beyond. -/
theorem toList_eq_some_rep {ll : HolLList α} {xs : List α} (h : toList ll = some xs) :
    ∀ i, ll.rep i = if hi : i < xs.length then some xs[i] else none := by
  unfold toList at h
  split at h
  · rename_i hfin
    obtain ⟨n, hnlen, hnrel⟩ := llength_spec hfin
    rw [hnlen] at h
    simp only [Option.getD_some] at h
    obtain ⟨hlen, hrep⟩ := ltake_spec n ll xs h
    intro i
    by_cases hi : i < xs.length
    · rw [dif_pos hi]; simpa using hrep i hi
    · rw [dif_neg hi]
      have hnrel' : LLengthRel ll xs.length := by rw [hlen]; exact hnrel
      exact rep_none_of_LLengthRel hnrel' i (Nat.le_of_not_lt hi)
  · simp at h

/-- Membership is inherited along `lprefix` at the representation level: an
    `lprefix`-smaller list is `some` at `n` only where the larger one is. -/
theorem lprefix_rep {a b : HolLList α} (h : lprefix a b) {n : Nat} {x : α}
    (ha : a.rep n = some x) : b.rep n = some x := by
  unfold lprefix at h
  cases hta : toList a with
  | none =>
      rw [hta] at h
      subst h
      exact ha
  | some xs =>
      rw [hta] at h
      have hra := toList_eq_some_rep hta n
      rw [hra] at ha
      by_cases hn : n < xs.length
      · rw [dif_pos hn] at ha
        injection ha with hx
        cases htb : toList b with
        | none =>
            rw [htb] at h
            obtain ⟨_, hrep⟩ := ltake_spec xs.length b xs h
            rw [hrep n hn, hx]
        | some ys =>
            rw [htb] at h
            have hrb := toList_eq_some_rep htb n
            rw [hrb]
            have hnys : n < ys.length := Nat.lt_of_lt_of_le hn h.length_le
            rw [dif_pos hnys]
            obtain ⟨zs, rfl⟩ := h
            rw [List.getElem_append_left hn, hx]
      · rw [dif_neg hn] at ha
        exact absurd ha (by simp)

/-- `lprefix` is reflexive. -/
theorem lprefix_refl (ll : HolLList α) : lprefix ll ll := by
  unfold lprefix
  cases toList ll with
  | none => rfl
  | some xs => exact ⟨[], by simp⟩

/-- HOL `LPREFIX_NTH`-direction: an `lprefix`-smaller list agrees at every
    index where it is defined. -/
theorem lprefix_lnth {a b : HolLList α} (h : lprefix a b) {n : Nat} {x : α}
    (ha : lnth n a = some x) : lnth n b = some x := by
  rw [lnth_eq_rep] at ha ⊢
  exact lprefix_rep h ha

/-- HOL `LPREFIX_ANTISYM`: two lists that prefix each other are equal. -/
theorem lprefix_antisym {a b : HolLList α} (hab : lprefix a b) (hba : lprefix b a) :
    a = b := by
  have hrep : a.rep = b.rep := funext fun n => by
    cases ha : a.rep n with
    | none =>
        cases hb : b.rep n with
        | none => rfl
        | some y =>
            have := lprefix_rep hba hb
            rw [ha] at this
            exact absurd this (by simp)
    | some x => exact (lprefix_rep hab ha).symm
  obtain ⟨ra, oka⟩ := a
  obtain ⟨rb, okb⟩ := b
  subst hrep
  exact congrArg (fun o => (⟨ra, o⟩ : HolLList α)) (Subsingleton.elim oka okb)

/-- HOL `lprefix_chain_LNTHs_agree` (`lprefix_lubScript.sml:182-187`): on a chain,
    any two members defined at `n` carry the same value there. -/
theorem lprefixChain_LNTHs_agree {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    {l1 l2 : HolLList α} (h1 : ls l1) (h2 : ls l2) {n : Nat} {x1 x2 : α}
    (hx1 : lnth n l1 = some x1) (hx2 : lnth n l2 = some x2) : x1 = x2 := by
  rcases hchain l1 l2 h1 h2 with h | h
  · rw [lprefix_lnth h hx1] at hx2
    exact Option.some.inj hx2
  · rw [lprefix_lnth h hx2] at hx1
    exact (Option.some.inj hx1).symm

/-- HOL `exists_lprefix_chain_nth` (`lprefix_lubScript.sml:205-208`): on a chain,
    if a member has value `x` at `n`, `lprefixChainNth` returns `x`. -/
theorem exists_lprefixChainNth {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    {n : Nat} {x : α} (hx : ∃ l, ls l ∧ lnth n l = some x) :
    lprefixChainNth n ls = some x := by
  obtain ⟨l0, hl0, hl0n⟩ := hx
  apply holOptionSome_eq_some
  · exact ⟨l0, hl0, hl0n⟩
  · intro y hy
    obtain ⟨l, hl, hln⟩ := hy
    exact lprefixChain_LNTHs_agree hchain hl hl0 hln hl0n

/-- On a chain the `lunfold` index underlying `build_lprefix_lub` advances by
    exactly one, so its step stays at `buildLprefixLubF`. -/
theorem lunfoldStep_buildLprefixLubF {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    ∀ k : Nat, lunfoldStep (buildLprefixLubF ls) 0 k = buildLprefixLubF ls k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [lunfoldStep]
      rw [ih]
      cases hk : lprefixChainNth k ls with
      | none =>
          have hk1 : lprefixChainNth (k + 1) ls = none :=
            lprefixChainNth_none_mono hchain (Nat.le_succ k) hk
          simp [buildLprefixLubF, hk, hk1]
      | some x =>
          simp [buildLprefixLubF, hk]

/-- HOL `build_lprefix_lub_lem` (`lprefix_lubScript.sml:440-445`): on a chain,
    `buildLprefixLub` reads back exactly `lprefixChainNth` at every index. -/
theorem lnth_buildLprefixLub {ls : HolLList α → Prop} (hchain : lprefixChain ls) (k : Nat) :
    lnth k (buildLprefixLub ls) = lprefixChainNth k ls := by
  rw [lnth_eq_rep, buildLprefixLub]
  change (lunfoldStep (buildLprefixLubF ls) 0 k).map Prod.snd = lprefixChainNth k ls
  rw [lunfoldStep_buildLprefixLubF hchain k]
  cases hk : lprefixChainNth k ls with
  | none => simp [buildLprefixLubF, hk]
  | some x => simp [buildLprefixLubF, hk]

end HolLList

end Flapjack
