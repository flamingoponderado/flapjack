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

/-- Converse of `ltake_spec`: if the representation agrees with `xs` on its
    indices, `ltake` returns `xs`. -/
theorem ltake_of_rep (xs : List α) (ll : HolLList α)
    (h : ∀ i (hi : i < xs.length), ll.rep i = some xs[i]) :
    ltake xs.length ll = some xs := by
  induction xs generalizing ll with
  | nil => simp [ltake]
  | cons x xs ih =>
      rw [List.length_cons]
      cases h0 : ll.rep 0 with
      | none => exact absurd (h 0 (by simp)) (by simp [h0])
      | some hd =>
          have hhd : hd = x := by
            have := h 0 (by simp)
            rw [h0] at this
            exact Option.some.inj this
          subst hhd
          have htl : ll.ltl =
              some ⟨fun n => ll.rep (n + 1), fun n hk => ll.ok (n + 1) hk⟩ := by
            simp [ltl, lhd, h0]
          have h' : ∀ i (hi : i < xs.length),
              (⟨fun n => ll.rep (n + 1), fun n hk => ll.ok (n + 1) hk⟩ : HolLList α).rep i =
                some xs[i] := by
            intro i hi
            have hhi := h (i + 1) (by simp [hi])
            rw [List.getElem_cons_succ] at hhi
            exact hhi
          simp only [ltake, lhd, h0, htl]
          rw [ih _ h']

/-- Two lazy lists with pointwise-equal representations are equal. -/
theorem ext_of_rep {a b : HolLList α} (h : ∀ n, a.rep n = b.rep n) : a = b := by
  have hrep : a.rep = b.rep := funext h
  obtain ⟨ra, oka⟩ := a
  obtain ⟨rb, okb⟩ := b
  simp only at hrep
  subst hrep
  exact congrArg (fun o => (⟨ra, o⟩ : HolLList α)) (Subsingleton.elim oka okb)

/-- The empty lazy list is the only one whose representation is everywhere `none`. -/
theorem eq_lnil_of_rep_none {ll : HolLList α} (h : ∀ n, ll.rep n = none) : ll = lnil :=
  ext_of_rep (fun n => by rw [h n]; rfl)

/-- A lazy list that has a `none` in its representation is finite. -/
theorem LFinite_of_rep_none {ll : HolLList α} {n : Nat} (h : ll.rep n = none) :
    LFinite ll := by
  induction n generalizing ll with
  | zero =>
      have hr : ∀ k, ll.rep k = none := fun k => rep_none_of_le ll h (Nat.zero_le k)
      rw [eq_lnil_of_rep_none hr]
      exact LFinite.lnil
  | succ n ih =>
      cases h0 : ll.rep 0 with
      | none =>
          have hr : ∀ k, ll.rep k = none := fun k => rep_none_of_le ll h0 (Nat.zero_le k)
          rw [eq_lnil_of_rep_none hr]
          exact LFinite.lnil
      | some hd =>
          have htail : (⟨fun k => ll.rep (k + 1),
              fun k hk => ll.ok (k + 1) hk⟩ : HolLList α).rep n = none := h
          have ihf : LFinite ⟨fun k => ll.rep (k + 1), fun k hk => ll.ok (k + 1) hk⟩ :=
            ih htail
          have heq : ll = lcons hd ⟨fun k => ll.rep (k + 1), fun k hk => ll.ok (k + 1) hk⟩ := by
            apply ext_of_rep
            intro k
            cases k with
            | zero => rw [h0]; rfl
            | succ k => rfl
          rw [heq]
          exact LFinite.lcons hd _ ihf

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

/-- HOL `unique_lprefix_lub` (`lprefix_lubScript.sml:419-422`): two least upper
    bounds of the same family are equal. -/
theorem unique_lprefix_lub {ls : HolLList α → Prop} {ll1 ll2 : HolLList α}
    (h1 : lprefixLub ls ll1) (h2 : lprefixLub ls ll2) : ll1 = ll2 :=
  lprefix_antisym (h1.2 ll2 h2.1) (h2.2 ll1 h1.1)

/-- A cons peels its head. -/
theorem lhd_lcons (h : α) (t : HolLList α) : lhd (lcons h t) = some h := by
  simp [lhd, lcons]

/-- The tail of a cons is the original tail. -/
theorem ltl_lcons (h : α) (t : HolLList α) : ltl (lcons h t) = some t := by
  have hrep : (⟨fun n => (lcons h t).rep (n + 1),
      fun n hk => (lcons h t).ok (n + 1) hk⟩ : HolLList α) = t :=
    ext_of_rep (fun n => by simp [lcons])
  simp only [ltl, lhd_lcons, Option.some.injEq]
  exact hrep

/-- A finite lazy list has a `some` prefix of any length up to its length. -/
theorem ltake_of_LLengthRel {ll : HolLList α} {n : Nat} (h : LLengthRel ll n) :
    ∃ xs : List α, ltake n ll = some xs := by
  induction h with
  | lnil => exact ⟨[], rfl⟩
  | lcons hd k t _ ih =>
      obtain ⟨xs, hxs⟩ := ih
      exact ⟨hd :: xs, by simp [ltake, lhd_lcons, ltl_lcons, hxs]⟩

/-- A finite lazy list has a finite `toList`. -/
theorem toList_of_LFinite {ll : HolLList α} (h : LFinite ll) :
    ∃ xs : List α, toList ll = some xs := by
  obtain ⟨n, hnlen, hnrel⟩ := llength_spec h
  obtain ⟨xs, hxs⟩ := ltake_of_LLengthRel hnrel
  refine ⟨xs, ?_⟩
  unfold toList
  rw [if_pos h, hnlen]
  simp only [Option.getD_some]
  exact hxs

/-- A finite lazy list is never the `none` of `toList`. -/
theorem toList_ne_none_of_LFinite {ll : HolLList α} (h : LFinite ll) :
    toList ll ≠ none := by
  obtain ⟨xs, hxs⟩ := toList_of_LFinite h
  rw [hxs]
  exact Option.some_ne_none xs

/-- If `toList` is `none` the list is infinite and defined at every index. -/
theorem rep_some_of_toList_none {ll : HolLList α} (h : toList ll = none) :
    ∀ n, ∃ x, ll.rep n = some x := by
  intro n
  by_cases hn : ll.rep n = none
  · exact absurd h (toList_ne_none_of_LFinite (LFinite_of_rep_none hn))
  · exact Option.ne_none_iff_exists'.mp hn

/-- Converse of `lprefix_rep`: if `b` is defined wherever `a` is, then `a` is
    an `lprefix` of `b`. -/
theorem lprefix_of_rep_agree {a b : HolLList α}
    (h : ∀ n x, a.rep n = some x → b.rep n = some x) : lprefix a b := by
  unfold lprefix
  cases ha : toList a with
  | none =>
      dsimp only
      apply ext_of_rep
      intro n
      obtain ⟨x, hx⟩ := rep_some_of_toList_none ha n
      rw [hx, h n x hx]
  | some xs =>
      dsimp only
      cases hb : toList b with
      | none =>
          dsimp only
          apply ltake_of_rep
          intro i hi
          have hai : a.rep i = some xs[i] := by
            rw [toList_eq_some_rep ha i, dif_pos hi]
          exact h i xs[i] hai
      | some ys =>
          dsimp only
          have hlt : xs.length ≤ ys.length := Nat.le_of_not_lt fun hys => by
            have hai : a.rep ys.length = some xs[ys.length] := by
              rw [toList_eq_some_rep ha ys.length, dif_pos hys]
            have hbi : b.rep ys.length = some xs[ys.length] := h _ _ hai
            have hby : b.rep ys.length = none := by
              rw [toList_eq_some_rep hb ys.length, dif_neg (Nat.lt_irrefl ys.length)]
            rw [hby] at hbi
            cases hbi
          rw [List.prefix_iff_eq_take]
          apply List.ext_getElem
          · simp [List.length_take, Nat.min_eq_left hlt]
          · intro j hj1 hj2
            rw [List.getElem_take]
            have haj : a.rep j = some xs[j] := by
              rw [toList_eq_some_rep ha j, dif_pos hj1]
            have hbj : b.rep j = some xs[j] := h j _ haj
            have hby : b.rep j = some ys[j] := by
              rw [toList_eq_some_rep hb j, dif_pos (Nat.lt_of_lt_of_le hj1 hlt)]
            rw [hby] at hbj
            exact (Option.some.inj hbj).symm

/-- Exact full form of HOL `build_lprefix_lub_lem`
    (`lprefix_lubScript.sml:440-445`): on a chain, the `m`-th `LUNFOLD` step
    carries the `(m+n)`-th chain value.  This is the general `m` companion of
    `lnth_buildLprefixLub` (the `m = 0` case). -/
theorem buildLprefixLubF_step {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    ∀ m n : Nat, lunfoldStep (buildLprefixLubF ls) m n =
      (lprefixChainNth (m + n) ls).map (fun x => (m + n + 1, x)) := by
  intro m n
  induction n generalizing m with
  | zero => simp [lunfoldStep, buildLprefixLubF]
  | succ n ih =>
      rw [lunfoldStep, ih]
      cases hk : lprefixChainNth (m + n) ls with
      | none =>
          have hk1 : lprefixChainNth (m + n + 1) ls = none :=
            lprefixChainNth_none_mono hchain (Nat.le_succ (m + n)) hk
          have harith : m + (n + 1) = m + n + 1 := rfl
          rw [harith, hk1]
          rfl
      | some x =>
          have harith : m + (n + 1) = m + n + 1 := rfl
          rw [harith]
          rfl

/-- HOL `build_lprefix_lub_lem` (`lprefix_lubScript.sml:440-445`) in full:
    `∀ m n, lnth n (lunfold (buildLprefixLubF ls) m) = lprefixChainNth (m+n) ls`
    on a chain. -/
theorem lnth_buildLprefixLub_full {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    (m n : Nat) :
    lnth n (lunfold (buildLprefixLubF ls) m) = lprefixChainNth (m + n) ls := by
  rw [lnth_eq_rep]
  change (lunfoldStep (buildLprefixLubF ls) m n).map Prod.snd =
    lprefixChainNth (m + n) ls
  rw [buildLprefixLubF_step hchain m n]
  cases lprefixChainNth (m + n) ls with
  | none => rfl
  | some x => rfl

/-- Upper-bound half of `buildLprefixLub_thm`: every chain member is an
    `lprefix` of `buildLprefixLub ls`. -/
theorem buildLprefixLub_upper {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    ∀ ll, ls ll → lprefix ll (buildLprefixLub ls) := by
  intro ll hl
  apply lprefix_of_rep_agree
  intro n x hx
  rw [← lnth_eq_rep] at hx
  have hcn : lprefixChainNth n ls = some x :=
    exists_lprefixChainNth hchain ⟨ll, hl, hx⟩
  rw [← lnth_eq_rep]
  rw [lnth_buildLprefixLub hchain n]
  exact hcn

/-- Least-upper-bound half of `buildLprefixLub_thm`: `buildLprefixLub ls` is
    below every upper bound of the chain. -/
theorem buildLprefixLub_least {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    ∀ ub, (∀ ll, ls ll → lprefix ll ub) → lprefix (buildLprefixLub ls) ub := by
  intro ub hub
  apply lprefix_of_rep_agree
  intro n x hx
  rw [← lnth_eq_rep] at hx
  rw [lnth_buildLprefixLub hchain n] at hx
  obtain ⟨l, hl, hln⟩ := holOptionSome_some hx
  rw [← lnth_eq_rep]
  exact lprefix_lnth (hub l hl) hln

/-- HOL `build_lprefix_lub_thm` (`lprefix_lubScript.sml:451-454`). -/
theorem buildLprefixLub_thm {ls : HolLList α → Prop} (hchain : lprefixChain ls) :
    lprefixLub ls (buildLprefixLub ls) :=
  ⟨buildLprefixLub_upper hchain, buildLprefixLub_least hchain⟩

/-- HOL `lprefix_lub_nth` (`lprefix_lubScript.sml:319-322`). -/
theorem lprefix_lub_nth {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    {lub : HolLList α} :
    (lprefixLub ls lub ↔ ∀ n, lnth n lub = lprefixChainNth n ls) := by
  constructor
  · intro hlub n
    rw [unique_lprefix_lub hlub (buildLprefixLub_thm hchain)]
    exact lnth_buildLprefixLub hchain n
  · intro hnth
    constructor
    · intro ll hl
      apply lprefix_of_rep_agree
      intro n x hx
      rw [← lnth_eq_rep] at hx
      have hcn : lprefixChainNth n ls = some x :=
        exists_lprefixChainNth hchain ⟨ll, hl, hx⟩
      rw [← lnth_eq_rep]
      rw [hnth n]
      exact hcn
    · intro ub hub
      apply lprefix_of_rep_agree
      intro n x hx
      rw [← lnth_eq_rep] at hx
      rw [hnth n] at hx
      obtain ⟨l, hl, hln⟩ := holOptionSome_some hx
      rw [← lnth_eq_rep]
      exact lprefix_lnth (hub l hl) hln

/-- HOL `build_prefix_lub_intro` (`lprefix_lubScript.sml:515-517`). -/
theorem build_prefix_lub_intro {ls : HolLList α → Prop} (hchain : lprefixChain ls)
    {lub : HolLList α} :
    (lprefixLub ls lub ↔ lub = buildLprefixLub ls) := by
  constructor
  · intro hlub
    exact unique_lprefix_lub hlub (buildLprefixLub_thm hchain)
  · intro h
    rw [h]
    exact buildLprefixLub_thm hchain

/-! ### Chain/equality lemmas

HOL `equiv_lprefix_chain`, `lprefix_rel` and the derived equality facts
(`lprefix_lubScript.sml:242-558`). -/

/-- HOL `equiv_lprefix_chain ls1 ls2 ⇔
    !n. lprefix_chain_nth n ls1 = lprefix_chain_nth n ls2`
    (`lprefix_lubScript.sml:242-245`). -/
def equivLprefixChain (ls1 ls2 : HolLList α → Prop) : Prop :=
  ∀ n, lprefixChainNth n ls1 = lprefixChainNth n ls2

/-- HOL `lprefix_rel s1 s2 ⇔ ∀l1. l1 IN s1 ⇒ ∃l2. l2 IN s2 ∧ LPREFIX l1 l2`
    (`lprefix_lubScript.sml:522-523`); HOL sets `'a llist set` are predicates
    `HolLList α → Prop`. -/
def lprefixRel (s1 s2 : HolLList α → Prop) : Prop :=
  ∀ l1, s1 l1 → ∃ l2, s2 l2 ∧ lprefix l1 l2

/-- HOL `prefixes_lprefix_total` (`llistScript.sml:2744-2746`): two lazy lists
    that are both `lprefix`-below a common list are `lprefix`-comparable.  This
    is the generic `llist` helper used by `lprefix_lub_is_chain`. -/
theorem lprefix_total_of_common {a b c : HolLList α} (ha : lprefix a c) (hb : lprefix b c) :
    lprefix a b ∨ lprefix b a := by
  by_cases hab : lprefix a b
  · exact Or.inl hab
  · right
    have hnot : ¬ ∀ n x, a.rep n = some x → b.rep n = some x :=
      fun hall => hab (lprefix_of_rep_agree hall)
    obtain ⟨n, hnotn⟩ : ∃ n, ¬ ∀ x, a.rep n = some x → b.rep n = some x :=
      Classical.not_forall.mp hnot
    obtain ⟨x, hnotx⟩ : ∃ x, ¬ (a.rep n = some x → b.rep n = some x) :=
      Classical.not_forall.mp hnotn
    have han : a.rep n = some x := by
      apply Classical.byContradiction
      intro h
      exact hnotx (fun h' => absurd h' h)
    have hbn : b.rep n ≠ some x := by
      intro h'
      exact hnotx (fun _ => h')
    have hbnone : b.rep n = none := by
      cases hbn' : b.rep n with
      | none => rfl
      | some y =>
          exfalso
          have hcx : c.rep n = some x := lprefix_rep ha han
          have hcy : c.rep n = some y := lprefix_rep hb hbn'
          rw [hcx] at hcy
          have hxy : x = y := Option.some.inj hcy
          exact hbn (by rw [hbn', hxy])
    apply lprefix_of_rep_agree
    intro m y hbm
    have hlt : m < n := by
      apply Classical.byContradiction
      intro hge
      have hmn : n ≤ m := Nat.le_of_not_lt hge
      have hnone := rep_none_of_le b hbnone hmn
      rw [hbm] at hnone
      exact absurd hnone (by simp)
    have hcy : c.rep m = some y := lprefix_rep hb hbm
    cases ham : a.rep m with
    | none =>
        have hnone := rep_none_of_le a ham (Nat.le_of_lt hlt)
        rw [han] at hnone
        exact absurd hnone (by simp)
    | some w =>
        have hcw : c.rep m = some w := lprefix_rep ha ham
        rw [hcw] at hcy
        have hwy : w = y := Option.some.inj hcy
        rw [← hwy]

/-- HOL `lprefix_lub_is_chain` (`lprefix_lubScript.sml:312-317`). -/
theorem lprefix_lub_is_chain {ls : HolLList α → Prop} {ll : HolLList α}
    (h : lprefixLub ls ll) : lprefixChain ls := by
  intro a b ha hb
  exact lprefix_total_of_common (h.1 a ha) (h.1 b hb)

/-- HOL `equiv_lprefix_chain_thm` (`lprefix_lubScript.sml:247-262`). -/
theorem equivLprefixChain_thm {ls1 ls2 : HolLList α → Prop}
    (h1 : lprefixChain ls1) (h2 : lprefixChain ls2) :
    (equivLprefixChain ls1 ls2 ↔
      (∀ ll1 n x, ls1 ll1 → lnth n ll1 = some x →
        ∃ ll2, ls2 ll2 ∧ lnth n ll2 = some x) ∧
      (∀ ll2 n x, ls2 ll2 → lnth n ll2 = some x →
        ∃ ll1, ls1 ll1 ∧ lnth n ll1 = some x)) := by
  constructor
  · intro heq
    refine ⟨?_, ?_⟩
    · intro ll1 n x hl1 hln
      have hc1 : lprefixChainNth n ls1 = some x :=
        exists_lprefixChainNth h1 ⟨ll1, hl1, hln⟩
      have hc2 : lprefixChainNth n ls2 = some x := by
        rw [← heq n]; exact hc1
      exact holOptionSome_some (P := fun z => ∃ l, ls2 l ∧ lnth n l = some z) (x := x) hc2
    · intro ll2 n x hl2 hln
      have hc2 : lprefixChainNth n ls2 = some x :=
        exists_lprefixChainNth h2 ⟨ll2, hl2, hln⟩
      have hc1 : lprefixChainNth n ls1 = some x := by
        rw [heq n]; exact hc2
      exact holOptionSome_some (P := fun z => ∃ l, ls1 l ∧ lnth n l = some z) (x := x) hc1
  · intro hdir
    rw [equivLprefixChain]
    intro n
    cases hc1 : lprefixChainNth n ls1 with
    | none =>
        symm
        apply lprefixChainNth_eq_none
        intro l2 hl2
        cases hln : lnth n l2 with
        | none => rfl
        | some y =>
            obtain ⟨l1, hl1, hln1⟩ := hdir.2 l2 n y hl2 hln
            have hcontra := exists_lprefixChainNth h1 ⟨l1, hl1, hln1⟩
            rw [hc1] at hcontra
            exact absurd hcontra (by simp)
    | some x =>
        obtain ⟨l1, hl1, hln1⟩ :=
          holOptionSome_some (P := fun z => ∃ l, ls1 l ∧ lnth n l = some z) (x := x) hc1
        obtain ⟨l2, hl2, hln2⟩ := hdir.1 l1 n x hl1 hln1
        exact (exists_lprefixChainNth h2 ⟨l2, hl2, hln2⟩).symm

/-! ### Deferred: HOL `equiv_lprefix_chain_thm2` (`lprefix_lubScript.sml:264-304`)

HOL's `equiv_lprefix_chain_thm2` is stated entirely over the `llist_shorter`
relation (`llistScript.sml:122-129`) with its characterisation
`llist_shorter_lnth`, and its proof uses `LTAKE_LLENGTH_SOME`,
`LTAKE_LNTH_EL` and `lnth_some_down_closed`.  None of these are ported in
`Flapjack/Misc/LList.lean`, so the theorem is not stated here rather than
weakened; it needs a separate commit-sized `llist_shorter` port (child bead
`flapjack-pxn.18.5.2.22.3.2.1.1`). -/

/-- HOL `lprefix_rel_lnth` (`lprefix_lubScript.sml:526-538`). -/
theorem lprefix_rel_lnth {ls1 ls2 : HolLList α → Prop} (h : lprefixRel ls1 ls2) :
    ∀ ll1 n x, ls1 ll1 → lnth n ll1 = some x →
      ∃ ll2, ls2 ll2 ∧ lnth n ll2 = some x := by
  intro ll1 n x hl1 hln
  obtain ⟨l2, hl2, hpre⟩ := h ll1 hl1
  exact ⟨l2, hl2, lprefix_lnth hpre hln⟩

/-- HOL `IMP_equiv_lprefix_chain` (`lprefix_lubScript.sml:540-548`). -/
theorem IMP_equiv_lprefix_chain {ls1 ls2 : HolLList α → Prop}
    (h1 : lprefixChain ls1) (h2 : lprefixChain ls2)
    (hr12 : lprefixRel ls1 ls2) (hr21 : lprefixRel ls2 ls1) :
    equivLprefixChain ls1 ls2 := by
  rw [equivLprefixChain_thm h1 h2]
  exact ⟨lprefix_rel_lnth hr12, lprefix_rel_lnth hr21⟩

/-- HOL `lprefix_lub_equiv_chain2` (`lprefix_lubScript.sml:471-484`). -/
theorem lprefix_lub_equiv_chain2 {ls1 ls2 : HolLList α → Prop} {ll1 ll2 : HolLList α}
    (h1 : lprefixLub ls1 ll1) (h2 : lprefixLub ls2 ll2) :
    (ll1 = ll2 ↔ equivLprefixChain ls1 ls2) := by
  have hc1 := lprefix_lub_is_chain h1
  have hc2 := lprefix_lub_is_chain h2
  constructor
  · intro heq
    subst heq
    rw [equivLprefixChain]
    intro n
    rw [← (lprefix_lub_nth hc1).mp h1 n, ← (lprefix_lub_nth hc2).mp h2 n]
  · intro heq
    apply ext_of_rep
    intro n
    rw [← lnth_eq_rep n ll1, ← lnth_eq_rep n ll2]
    rw [(lprefix_lub_nth hc1).mp h1 n, (lprefix_lub_nth hc2).mp h2 n]
    exact heq n

/-- HOL `IMP_build_lprefix_lub_EQ` (`lprefix_lubScript.sml:550-558`). -/
theorem IMP_build_lprefix_lub_EQ {ls1 ls2 : HolLList α → Prop}
    (h1 : lprefixChain ls1) (h2 : lprefixChain ls2)
    (hr12 : lprefixRel ls1 ls2) (hr21 : lprefixRel ls2 ls1) :
    buildLprefixLub ls1 = buildLprefixLub ls2 :=
  (lprefix_lub_equiv_chain2 (buildLprefixLub_thm h1) (buildLprefixLub_thm h2)).mpr
    (IMP_equiv_lprefix_chain h1 h2 hr12 hr21)

end HolLList

end Flapjack
