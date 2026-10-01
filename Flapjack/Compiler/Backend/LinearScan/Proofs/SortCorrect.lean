import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.PassInvariants
import Flapjack.Misc.Sorting

/-!
# linear_scanProof: in-array quicksort of registers and moves

Ports of `linear_scanProofScript.sml:3821-4330`: swapping two array cells,
the list lemmas used to reason about it, and the correctness of the in-array
partition and quicksort `partition_regs`/`sort_regs` (registers ordered by
interval beginning) and `partition_moves`/`sort_moves` (moves by priority).
HOL `EL` is the exact `holEl`, `PERM` the exact `holPerm`, `LEX` the exact
`holLex`, `LUPDATE v n l` is `l.set n v`, `TAKE` is `List.take`, and HOL's
`let x = e in t` is a Lean `let`.
-/

namespace Flapjack.LinearScan

open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-! ### List helpers (Flapjack infrastructure) -/

private theorem count_set {α : Type} [DecidableEq α] (a v : α) :
    ∀ (l : List α) (i : Nat) (h : i < l.length),
      (l.set i v).count a + (if l[i] = a then 1 else 0) = l.count a + (if v = a then 1 else 0)
  | x :: xs, 0, _ => by
      simp only [List.set_cons_zero, List.count_cons, List.getElem_cons_zero, beq_iff_eq]
      split <;> split <;> omega
  | x :: xs, i + 1, h => by
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ]
      have := count_set a v xs i (by simp at h; omega)
      omega

/-- Swapping two cells permutes a list. -/
private theorem perm_swap {α : Type} (l : List α) (i1 i2 : Nat) (h1 : i1 < l.length)
    (h2 : i2 < l.length) : l.Perm ((l.set i1 l[i2]).set i2 l[i1]) := by
  classical
  by_cases e : i1 = i2
  · subst e; simp
  rw [List.perm_iff_count]
  intro a
  have hA := count_set a l[i2] l i1 h1
  have hB := count_set a l[i1] (l.set i1 l[i2]) i2 (by simpa using h2)
  have hget : (l.set i1 l[i2])[i2]'(by simpa using h2) = l[i2] := by
    rw [List.getElem_set_ne e]
  rw [hget] at hB
  by_cases c1 : l[i1] = a <;> by_cases c2 : l[i2] = a
  · simp only [if_pos c1, if_pos c2] at hA hB; omega
  · simp only [if_pos c1, if_neg c2] at hA hB; omega
  · simp only [if_neg c1, if_pos c2] at hA hB; omega
  · simp only [if_neg c1, if_neg c2] at hA hB; omega

/-- A permutation that leaves every cell from `r` on unchanged permutes every
prefix of length at least `r`. -/
private theorem perm_take_of_agree {α : Type} [Nonempty α] {a b : List α} {r n : Nat}
    (hp : a.Perm b) (hag : ∀ i, r ≤ i → holEl i b = holEl i a) (hrn : r ≤ n) :
    (a.take n).Perm (b.take n) := by
  have hlen := hp.length_eq
  have hdrop : a.drop n = b.drop n := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp only [List.getElem_drop]
    have ha : n + i < a.length := by simp at h1; omega
    have hb : n + i < b.length := by simp at h2; omega
    rw [← holEl_eq_getElem _ _ ha, ← holEl_eq_getElem _ _ hb, hag (n + i) (by omega)]
  have h := hp
  rw [← List.take_append_drop n a, ← List.take_append_drop n b, hdrop] at h
  exact List.perm_append_right_iff _ |>.mp h

/-- `holEl` reads the same cell of a prefix. -/
private theorem holEl_take {α : Type} [Nonempty α] (l : List α) (n i : Nat) (hi : i < n) :
    holEl i (l.take n) = holEl i l := by
  by_cases h : i < l.length
  · rw [holEl_eq_getElem _ _ (by simp; omega), holEl_eq_getElem _ _ h, List.getElem_take]
  · rw [holEl_of_length_le _ _ (by simp; omega), holEl_of_length_le _ _ (by omega)]

/-- Exact HOL `swap_regs_eq` (`linear_scanProofScript.sml:3821-3828`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "swap_regs_eq"]
theorem swapRegsEq :
    ∀ (sth : LinearScanHiddenState) (i1 i2 : Nat),
      i1 < sth.sorted_regs.length ∧ i2 < sth.sorted_regs.length →
      ∃ sthout, swapRegs i1 i2 sth = (.success (), sthout) ∧
        sthout = { sth with sorted_regs :=
          ((sth.sorted_regs.set i1 (holEl i2 sth.sorted_regs)).set i2
            (holEl i1 sth.sorted_regs)) } := by
  intro sth i1 i2 ⟨h1, h2⟩
  refine ⟨_, ?_, rfl⟩
  simp only [swapRegs, Translator.Monadic.MonadBase.bind, ignoreBind, sortedRegsSubEqn,
    if_pos h1, if_pos h2, updateSortedRegsEqn, List.length_set]

/-- Exact HOL `if_thm` (`linear_scanProofScript.sml:3831-3835`); the HOL
condition `b : bool` is a `Bool`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "if_thm"]
theorem ifThm {α : Type} :
    ∀ (b : Bool) (x y z : α),
      ((if b then x else y) = z) ↔ ((b = true ∧ x = z) ∨ (¬ b = true ∧ y = z)) := by
  intro b x y z
  cases b <;> simp

/-- Exact HOL `split_at_indice_sing` (`linear_scanProofScript.sml:3837-3857`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "split_at_indice_sing"]
theorem splitAtIndiceSing {α : Type} :
    ∀ (l : List α) (i : Nat), i < l.length →
      ∃ l1 x l2, l = l1 ++ [x] ++ l2 ∧ l1.length = i := by
  intro l i h
  refine ⟨l.take i, l[i], l.drop (i + 1), ?_, by simp; omega⟩
  conv => lhs; rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons h]
  simp

/-- Exact HOL `split_at_indice` (`linear_scanProofScript.sml:3859-3877`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "split_at_indice"]
theorem splitAtIndice {α : Type} :
    ∀ (l : List α) (i : Nat), i ≤ l.length → ∃ l1 l2, l = l1 ++ l2 ∧ l1.length = i := by
  intro l i h
  exact ⟨l.take i, l.drop i, (List.take_append_drop i l).symm, by simp; omega⟩

/-- Exact HOL `swap_perm_lemma` (`linear_scanProofScript.sml:3879-3912`); HOL
types are inhabited, so the element type carries `[Nonempty α]` for `holEl`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "swap_perm_lemma"]
theorem swapPermLemma {α : Type} [Nonempty α] :
    ∀ (l : List α) (i1 i2 : Nat), i1 < l.length ∧ i2 < l.length →
      holPerm l ((l.set i1 (holEl i2 l)).set i2 (holEl i1 l)) := by
  intro l i1 i2 ⟨h1, h2⟩
  rw [holPerm_iff, holEl_eq_getElem _ _ h1, holEl_eq_getElem _ _ h2]
  exact perm_swap l i1 i2 h1 h2

/-- Exact HOL `LUPDATE_TAKE` (`linear_scanProofScript.sml:3914-3922`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "LUPDATE_TAKE"]
theorem lupdateTake {α : Type} :
    ∀ (n x : Nat) (y : α) (l : List α), x < n ∧ n ≤ l.length →
      (l.set x y).take n = (l.take n).set x y := by
  intro n x y l _
  exact List.take_set

/-- Exact HOL `swap_regs_perm` (`linear_scanProofScript.sml:3924-3935`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "swap_regs_perm"]
theorem swapRegsPerm :
    ∀ (sth : LinearScanHiddenState) (i1 i2 : Nat) (sthout : LinearScanHiddenState),
      swapRegs i1 i2 sth = (.success (), sthout) →
      ∀ n, i1 < n ∧ i2 < n ∧ n ≤ sth.sorted_regs.length →
        holPerm (sth.sorted_regs.take n) (sthout.sorted_regs.take n) := by
  intro sth i1 i2 sthout h n ⟨h1, h2, hn⟩
  obtain ⟨s, hs, rfl⟩ := swapRegsEq sth i1 i2 ⟨by omega, by omega⟩
  rw [hs] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  show holPerm _ (((sth.sorted_regs.set i1 _).set i2 _).take n)
  rw [List.take_set, List.take_set, ← holEl_take sth.sorted_regs n i2 h2,
    ← holEl_take sth.sorted_regs n i1 h1]
  exact swapPermLemma _ i1 i2 ⟨by simp; omega, by simp; omega⟩

/-- Exact HOL `PERM_EVERY_EQ` (`linear_scanProofScript.sml:4016-4025`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "PERM_EVERY_EQ"]
theorem permEveryEq {α : Type} :
    ∀ (P : α → Prop) (l1 l2 : List α), holPerm l1 l2 →
      ((∀ x, x ∈ l1 → P x) ↔ (∀ x, x ∈ l2 → P x)) := by
  intro P l1 l2 h
  rw [holPerm_iff] at h
  exact ⟨fun h1 x hx => h1 x (h.mem_iff.mpr hx), fun h2 x hx => h2 x (h.mem_iff.mp hx)⟩

/-- Exact HOL `sort_regs_prop_lemma` (`linear_scanProofScript.sml:4027-4069`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "sort_regs_prop_lemma"]
theorem sortRegsPropLemma :
    ∀ (P : Nat → Prop) (l1 l2 : List Nat) (l r : Nat),
      l ≤ l1.length ∧ r ≤ l1.length ∧
      (∀ ind, ind < l ∨ r ≤ ind → holEl ind l2 = holEl ind l1) ∧
      (∀ ind, l ≤ ind ∧ ind < r → P (holEl ind l1)) ∧ holPerm l1 l2 →
      ∀ ind, l ≤ ind ∧ ind < r → P (holEl ind l2) := by
  intro P l1 l2 l r ⟨hl, hr, hag, hP, hperm⟩ ind ⟨hi1, hi2⟩
  rw [holPerm_iff] at hperm
  have hlen := hperm.length_eq
  -- the middle segments are permutations of each other
  have hA : l2.take l = l1.take l := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp only [List.getElem_take]
    have := hag i (Or.inl (by simp at h1; omega))
    rwa [holEl_eq_getElem _ _ (by simp at h1; omega),
      holEl_eq_getElem _ _ (by simp at h2; omega)] at this
  have hB : l2.drop r = l1.drop r := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp only [List.getElem_drop]
    have := hag (r + i) (Or.inr (by omega))
    rwa [holEl_eq_getElem _ _ (by simp at h1; omega),
      holEl_eq_getElem _ _ (by simp at h2; omega)] at this
  have hsplit : ∀ m : List Nat, m = m.take l ++ (m.take r).drop l ++ m.drop r := by
    intro m
    have e : m.take l = (m.take r).take l := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    calc m = m.take r ++ m.drop r := (List.take_append_drop r m).symm
      _ = ((m.take r).take l ++ (m.take r).drop l) ++ m.drop r := by
          rw [List.take_append_drop l (m.take r)]
      _ = m.take l ++ (m.take r).drop l ++ m.drop r := by rw [e]
  have hM : ((l1.take r).drop l).Perm ((l2.take r).drop l) := by
    have h := hperm
    rw [hsplit l1, hsplit l2, hA, hB] at h
    exact (List.perm_append_left_iff _).mp ((List.perm_append_right_iff _).mp h)
  have hmem : holEl ind l2 ∈ (l2.take r).drop l := by
    rw [holEl_eq_getElem _ _ (by omega)]
    refine List.mem_iff_getElem.mpr ⟨ind - l, by simp; omega, ?_⟩
    have e : l + (ind - l) = ind := by omega
    simp only [List.getElem_drop, List.getElem_take, e]
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp (hM.mem_iff.mpr hmem)
  simp only [List.getElem_drop, List.getElem_take] at he
  rw [← he, ← holEl_eq_getElem _ _ (by simp at hk; omega)]
  exact hP (l + k) ⟨by omega, by simp at hk; omega⟩

/-- Reading a cell after `swap_regs`/`swap_moves`. -/
private theorem holEl_swap {α : Type} [Nonempty α] (l : List α) (i1 i2 j : Nat)
    (h1 : i1 < l.length) (h2 : i2 < l.length) :
    holEl j ((l.set i1 (holEl i2 l)).set i2 (holEl i1 l)) =
      if i2 = j then holEl i1 l else if i1 = j then holEl i2 l else holEl j l := by
  rw [holEl_set _ _ _ _ (by simpa using h2), holEl_set _ _ _ _ h1]

/-- `partition_regs` in invariant form: a permutation that fixes the cells
outside `[l, r)` and splits them around the pivot. -/
private theorem partitionRegsAux (rpiv : Nat) (begrpiv : Int) :
    ∀ (k l r : Nat) (sth : LinearScanHiddenState), r - l = k →
      (∀ i, l ≤ i ∧ i < r → holEl i sth.sorted_regs < sth.int_beg.length) →
      l ≤ sth.sorted_regs.length → r ≤ sth.sorted_regs.length →
      ∃ mid sthout, partitionRegs l rpiv begrpiv r sth = (.success mid, sthout) ∧
        sthout = { sth with sorted_regs := sthout.sorted_regs } ∧
        sth.sorted_regs.Perm sthout.sorted_regs ∧
        (∀ ind, ind < l ∨ r ≤ ind → holEl ind sthout.sorted_regs = holEl ind sth.sorted_regs) ∧
        (l ≤ r → l ≤ mid ∧ mid ≤ r) ∧
        (∀ ind, l ≤ ind ∧ ind < mid →
          holLex (· < ·) (· ≤ ·)
            (holEl (holEl ind sthout.sorted_regs) sth.int_beg, holEl ind sthout.sorted_regs)
            (begrpiv, rpiv)) ∧
        (∀ ind, mid ≤ ind ∧ ind < r →
          holLex (· < ·) (· ≤ ·) (begrpiv, rpiv)
            (holEl (holEl ind sthout.sorted_regs) sth.int_beg, holEl ind sthout.sorted_regs)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro l r sth hk hb hl hr
  rw [partitionRegs]
  by_cases hrl : r ≤ l
  · rw [dif_pos hrl]
    refine ⟨l, sth, rfl, rfl, List.Perm.refl _, fun _ _ => rfl, fun h => ⟨Nat.le_refl _, h⟩,
      fun ind h => by omega, fun ind h => by omega⟩
  rw [dif_neg hrl]
  have hlen : l < sth.sorted_regs.length := by omega
  have hreg := hb l ⟨Nat.le_refl _, by omega⟩
  simp only [Translator.Monadic.MonadBase.bind, sortedRegsSubEqn, if_pos hlen, intBegSubEqn,
    if_pos hreg]
  split
  · next hc =>
    obtain ⟨mid, sthout, hrun, hst, hp, hag, hmid, hleft, hright⟩ :=
      ih (r - (l + 1)) (by omega) (l + 1) r sth rfl
        (fun i ⟨h1, h2⟩ => hb i ⟨by omega, h2⟩) (by omega) hr
    refine ⟨mid, sthout, hrun, hst, hp, fun ind h => hag ind (by omega), fun _ => ?_,
      fun ind ⟨h1, h2⟩ => ?_, hright⟩
    · have := hmid (by omega); omega
    · by_cases e : ind = l
      · subst e
        rw [hag ind (Or.inl (by omega))]
        exact hc
      · exact hleft ind ⟨by omega, h2⟩
  · next hc =>
    obtain ⟨s', hs', hs'eq⟩ := swapRegsEq sth l (r - 1) ⟨hlen, by omega⟩
    simp only [ignoreBind, hs']
    have hsw : ∀ j, holEl j s'.sorted_regs =
        if r - 1 = j then holEl l sth.sorted_regs
        else if l = j then holEl (r - 1) sth.sorted_regs else holEl j sth.sorted_regs := by
      intro j; rw [hs'eq]; exact holEl_swap _ _ _ _ hlen (by omega)
    have hs'len : s'.sorted_regs.length = sth.sorted_regs.length := by rw [hs'eq]; simp
    obtain ⟨mid, sthout, hrun, hst, hp, hag, hmid, hleft, hright⟩ :=
      ih (r - 1 - l) (by omega) l (r - 1) s' rfl
        (fun i ⟨h1, h2⟩ => by
          rw [hsw, hs'eq]
          split
          · omega
          · split
            · exact hb _ ⟨by omega, by omega⟩
            · exact hb i ⟨h1, by omega⟩)
        (by omega) (by omega)
    have hbeg : s'.int_beg = sth.int_beg := by rw [hs'eq]
    refine ⟨mid, sthout, hrun, by rw [hst, hs'eq], ?_, fun ind h => ?_, fun _ => ?_,
      fun ind h => ?_, fun ind ⟨h1, h2⟩ => ?_⟩
    · have hperm : sth.sorted_regs.Perm s'.sorted_regs := by
        rw [hs'eq]
        have := perm_swap sth.sorted_regs l (r - 1) hlen (by omega)
        rwa [← holEl_eq_getElem _ _ hlen, ← holEl_eq_getElem _ _ (by omega)] at this
      exact hperm.trans hp
    · rw [hag ind (by omega), hsw, if_neg (by omega), if_neg (by omega)]
    · have := hmid (by omega); omega
    · have := hleft ind h; rwa [hbeg] at this
    · by_cases e : ind = r - 1
      · subst e
        rw [hag _ (Or.inr (Nat.le_refl _)), hsw, if_pos rfl]
        simp only [holLex] at hc ⊢
        omega
      · have := hright ind ⟨h1, by omega⟩; rwa [hbeg] at this

/-- Exact HOL `partition_regs_correct` (`linear_scanProofScript.sml:3937-4014`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "partition_regs_correct"]
theorem partitionRegsCorrect :
    ∀ (l rpiv : Nat) (begrpiv : Int) (r : Nat) (sth : LinearScanHiddenState),
      (∀ i, l ≤ i ∧ i < r → holEl i sth.sorted_regs < sth.int_beg.length) ∧
      l ≤ sth.sorted_regs.length ∧ r ≤ sth.sorted_regs.length →
      ∃ mid sthout, partitionRegs l rpiv begrpiv r sth = (.success mid, sthout) ∧
        sthout = { sth with sorted_regs := sthout.sorted_regs } ∧
        sthout.sorted_regs.length = sth.sorted_regs.length ∧
        (l ≤ r → l ≤ mid ∧ mid ≤ r) ∧
        (∀ n, l ≤ n ∧ r ≤ n ∧ n ≤ sth.sorted_regs.length →
          holPerm (sth.sorted_regs.take n) (sthout.sorted_regs.take n)) ∧
        (∀ ind, ind < l ∨ r ≤ ind → holEl ind sthout.sorted_regs = holEl ind sth.sorted_regs) ∧
        (∀ ind, l ≤ ind ∧ ind < mid →
          let reg := holEl ind sthout.sorted_regs
          holLex (· < ·) (· ≤ ·) (holEl reg sth.int_beg, reg) (begrpiv, rpiv)) ∧
        (∀ ind, mid ≤ ind ∧ ind < r →
          let reg := holEl ind sthout.sorted_regs
          holLex (· < ·) (· ≤ ·) (begrpiv, rpiv) (holEl reg sth.int_beg, reg)) := by
  intro l rpiv begrpiv r sth ⟨hb, hl, hr⟩
  obtain ⟨mid, sthout, hrun, hst, hp, hag, hmid, hleft, hright⟩ :=
    partitionRegsAux rpiv begrpiv (r - l) l r sth rfl hb hl hr
  exact ⟨mid, sthout, hrun, hst, hp.length_eq.symm, hmid,
    fun n ⟨_, hrn, _⟩ => (holPerm_iff _ _).mpr
      (perm_take_of_agree hp (fun i hi => hag i (Or.inr hi)) hrn),
    hag, hleft, hright⟩

private theorem intbegLess_refl (beg : List Int) (x : Nat) : intbegLess beg x x :=
  Or.inr ⟨rfl, Nat.le_refl _⟩

/-- `sort_regs` in invariant form. -/
private theorem sortRegsAux :
    ∀ (k l r : Nat) (sth : LinearScanHiddenState), r - l = k →
      (∀ i, l ≤ i ∧ i < r → holEl i sth.sorted_regs < sth.int_beg.length) →
      l ≤ sth.sorted_regs.length → r ≤ sth.sorted_regs.length →
      ∃ sthout, sortRegs l r sth = (.success (), sthout) ∧
        sthout = { sth with sorted_regs := sthout.sorted_regs } ∧
        sth.sorted_regs.Perm sthout.sorted_regs ∧
        (∀ ind, ind < l ∨ r ≤ ind → holEl ind sthout.sorted_regs = holEl ind sth.sorted_regs) ∧
        (∀ i1 i2, l ≤ i1 ∧ i1 ≤ i2 ∧ i2 < r →
          intbegLess sth.int_beg (holEl i1 sthout.sorted_regs) (holEl i2 sthout.sorted_regs)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro l r sth hk hb hl hr
  rw [sortRegs]
  by_cases hrl : r ≤ l + 1
  · rw [dif_pos hrl]
    refine ⟨sth, rfl, rfl, List.Perm.refl _, fun _ _ => rfl, fun i1 i2 ⟨h1, h2, h3⟩ => ?_⟩
    have e : i1 = i2 := by omega
    rw [e]; exact intbegLess_refl _ _
  rw [dif_neg hrl]
  have hlen : l < sth.sorted_regs.length := by omega
  have hpb := hb l ⟨Nat.le_refl _, by omega⟩
  -- partition the cells after the pivot
  obtain ⟨mid, s1, hrun1, hst1, hp1, hag1, hmid1, hleft1, hright1⟩ :=
    partitionRegsAux (holEl l sth.sorted_regs) (holEl (holEl l sth.sorted_regs) sth.int_beg)
      (r - (l + 1)) (l + 1) r sth rfl (fun i ⟨h1, h2⟩ => hb i ⟨by omega, h2⟩) (by omega) hr
  obtain ⟨hm1, hm2⟩ := hmid1 (by omega)
  have hlen1 : s1.sorted_regs.length = sth.sorted_regs.length := hp1.length_eq.symm
  have hbeg1 : s1.int_beg = sth.int_beg := by rw [hst1]
  have hpiv1 : holEl l s1.sorted_regs = holEl l sth.sorted_regs := hag1 l (Or.inl (by omega))
  have hb1 : ∀ j, l + 1 ≤ j ∧ j < r → holEl j s1.sorted_regs < sth.int_beg.length :=
    sortRegsPropLemma (fun x => x < sth.int_beg.length) sth.sorted_regs s1.sorted_regs (l + 1) r
      ⟨by omega, hr, hag1, fun i ⟨h1, h2⟩ => hb i ⟨by omega, h2⟩, (holPerm_iff _ _).mpr hp1⟩
  -- swap the pivot into place
  obtain ⟨s2, hs2, hs2eq⟩ := swapRegsEq s1 l (mid - 1) ⟨by omega, by omega⟩
  have hsw : ∀ j, holEl j s2.sorted_regs =
      if mid - 1 = j then holEl l s1.sorted_regs
      else if l = j then holEl (mid - 1) s1.sorted_regs else holEl j s1.sorted_regs := by
    intro j; rw [hs2eq]; exact holEl_swap _ _ _ _ (by omega) (by omega)
  have hlen2 : s2.sorted_regs.length = sth.sorted_regs.length := by
    rw [hs2eq]; simp [hlen1]
  have hbeg2 : s2.int_beg = sth.int_beg := by rw [hs2eq, hbeg1]
  have hp2 : s1.sorted_regs.Perm s2.sorted_regs := by
    rw [hs2eq]
    have := perm_swap s1.sorted_regs l (mid - 1) (by omega) (by omega)
    rwa [← holEl_eq_getElem _ _ (by omega), ← holEl_eq_getElem _ _ (by omega)] at this
  have hb2 : ∀ j, l ≤ j ∧ j < r → holEl j s2.sorted_regs < sth.int_beg.length := by
    intro j ⟨h1, h2⟩
    rw [hsw]
    split
    · rw [hpiv1]; exact hpb
    · split
      · next e1 e2 =>
        by_cases e3 : mid - 1 = l
        · rw [e3, hpiv1]; exact hpb
        · exact hb1 _ ⟨by omega, by omega⟩
      · next e1 e2 => exact hb1 j ⟨by omega, h2⟩
  -- the pivot's order facts on `s2`
  let piv := holEl l sth.sorted_regs
  have hlo2 : ∀ j, l ≤ j ∧ j < mid - 1 → intbegLess sth.int_beg (holEl j s2.sorted_regs) piv := by
    intro j ⟨h1, h2⟩
    rw [hsw, if_neg (by omega)]
    split
    · exact hleft1 _ ⟨by omega, by omega⟩
    · exact hleft1 j ⟨by omega, by omega⟩
  have hpiv2 : holEl (mid - 1) s2.sorted_regs = piv := by
    rw [hsw, if_pos rfl, hpiv1]
  have hhi2 : ∀ j, mid ≤ j ∧ j < r → intbegLess sth.int_beg piv (holEl j s2.sorted_regs) := by
    intro j ⟨h1, h2⟩
    rw [hsw, if_neg (by omega), if_neg (by omega)]
    exact hright1 j ⟨h1, h2⟩
  -- sort the lower part
  obtain ⟨s3, hrun3, hst3, hp3, hag3, hsort3⟩ :=
    ih (mid - 1 - l) (by omega) l (mid - 1) s2 rfl
      (fun i ⟨h1, h2⟩ => by rw [hbeg2]; exact hb2 i ⟨h1, by omega⟩) (by omega) (by omega)
  have hlen3 : s3.sorted_regs.length = sth.sorted_regs.length := by
    rw [← hp3.length_eq, hlen2]
  have hbeg3 : s3.int_beg = sth.int_beg := by rw [hst3, hbeg2]
  have hlo3 : ∀ j, l ≤ j ∧ j < mid - 1 → intbegLess sth.int_beg (holEl j s3.sorted_regs) piv :=
    sortRegsPropLemma (fun x => intbegLess sth.int_beg x piv) s2.sorted_regs s3.sorted_regs l
      (mid - 1) ⟨by omega, by omega, hag3, hlo2, (holPerm_iff _ _).mpr hp3⟩
  -- sort the upper part
  obtain ⟨s4, hrun4, hst4, hp4, hag4, hsort4⟩ :=
    ih (r - mid) (by omega) mid r s3 rfl
      (fun i ⟨h1, h2⟩ => by
        rw [hbeg3, hag3 i (Or.inr (by omega))]; exact hb2 i ⟨by omega, h2⟩)
      (by omega) (by omega)
  have hhi3 : ∀ j, mid ≤ j ∧ j < r → intbegLess sth.int_beg piv (holEl j s3.sorted_regs) :=
    fun j hj => by rw [hag3 j (Or.inr (by omega))]; exact hhi2 j hj
  have hhi4 : ∀ j, mid ≤ j ∧ j < r → intbegLess sth.int_beg piv (holEl j s4.sorted_regs) :=
    sortRegsPropLemma (fun x => intbegLess sth.int_beg piv x) s3.sorted_regs s4.sorted_regs mid r
      ⟨by omega, by omega, hag4, hhi3, (holPerm_iff _ _).mpr hp4⟩
  have htr := intbegLessTransitive sth.int_beg
  refine ⟨s4, ?_, by rw [hst4, hst3, hs2eq, hst1], hp1.trans (hp2.trans (hp3.trans hp4)),
    fun ind h => ?_, fun i1 i2 ⟨h1, h2, h3⟩ => ?_⟩
  · simp only [Translator.Monadic.MonadBase.bind, sortedRegsSubEqn, if_pos hlen, intBegSubEqn,
      if_pos hpb, hrun1]
    simp only [ignoreBind, hs2, dif_neg (show ¬ (mid ≤ l ∨ r < mid) by omega), hrun3, hrun4]
  · rw [hag4 ind (by omega), hag3 ind (by omega), hsw, if_neg (by omega), if_neg (by omega),
      hag1 ind (by omega)]
  · rw [hbeg2] at hsort3
    rw [hbeg3] at hsort4
    -- cells below `mid` are those of `s3`
    have hlow : ∀ j, j < mid → holEl j s4.sorted_regs = holEl j s3.sorted_regs :=
      fun j hj => hag4 j (Or.inl hj)
    by_cases c1 : mid ≤ i1
    · exact hsort4 i1 i2 ⟨c1, h2, h3⟩
    by_cases c2 : i2 < mid - 1
    · rw [hlow i1 (by omega), hlow i2 (by omega)]
      exact hsort3 i1 i2 ⟨h1, h2, c2⟩
    -- `i1 < mid ≤ ...`: compare through the pivot
    have hx : intbegLess sth.int_beg (holEl i1 s4.sorted_regs) piv ∨
        holEl i1 s4.sorted_regs = piv := by
      rw [hlow i1 (by omega)]
      by_cases e : i1 = mid - 1
      · right; rw [e, hag3 _ (Or.inr (Nat.le_refl _)), hpiv2]
      · left; exact hlo3 i1 ⟨h1, by omega⟩
    have hy : intbegLess sth.int_beg piv (holEl i2 s4.sorted_regs) ∨
        holEl i2 s4.sorted_regs = piv := by
      by_cases e : i2 = mid - 1
      · right; rw [e, hlow _ (by omega), hag3 _ (Or.inr (Nat.le_refl _)), hpiv2]
      · left; exact hhi4 i2 ⟨by omega, h3⟩
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact htr _ _ _ ⟨hx, hy⟩
    · rw [hy]; exact hx
    · rw [hx]; exact hy
    · rw [hx, hy]; exact intbegLess_refl _ _

/-- Exact HOL `sort_regs_correct` (`linear_scanProofScript.sml:4071-4239`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "sort_regs_correct"]
theorem sortRegsCorrect :
    ∀ (l r : Nat) (sth : LinearScanHiddenState),
      (∀ i, l ≤ i ∧ i < r → holEl i sth.sorted_regs < sth.int_beg.length) ∧
      l ≤ sth.sorted_regs.length ∧ r ≤ sth.sorted_regs.length →
      ∃ sthout, sortRegs l r sth = (.success (), sthout) ∧
        sthout = { sth with sorted_regs := sthout.sorted_regs } ∧
        sthout.sorted_regs.length = sth.sorted_regs.length ∧
        (∀ n, l ≤ n ∧ r ≤ n ∧ n ≤ sth.sorted_regs.length →
          holPerm (sth.sorted_regs.take n) (sthout.sorted_regs.take n)) ∧
        (∀ ind, ind < l ∨ r ≤ ind → holEl ind sthout.sorted_regs = holEl ind sth.sorted_regs) ∧
        (∀ i1 i2, l ≤ i1 ∧ i1 ≤ i2 ∧ i2 < r →
          let reg1 := holEl i1 sthout.sorted_regs
          let reg2 := holEl i2 sthout.sorted_regs
          holLex (· < ·) (· ≤ ·) (holEl reg1 sth.int_beg, reg1) (holEl reg2 sth.int_beg, reg2)) := by
  intro l r sth ⟨hb, hl, hr⟩
  obtain ⟨sthout, hrun, hst, hp, hag, hsort⟩ := sortRegsAux (r - l) l r sth rfl hb hl hr
  exact ⟨sthout, hrun, hst, hp.length_eq.symm,
    fun n ⟨_, hrn, _⟩ => (holPerm_iff _ _).mpr
      (perm_take_of_agree hp (fun i hi => hag i (Or.inr hi)) hrn),
    hag, fun i1 i2 h => hsort i1 i2 h⟩

/-- Exact HOL `swap_moves_eq` (`linear_scanProofScript.sml:4241-4248`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "swap_moves_eq"]
theorem swapMovesEq :
    ∀ (sth : LinearScanHiddenState) (i1 i2 : Nat),
      i1 < sth.sorted_moves.length ∧ i2 < sth.sorted_moves.length →
      ∃ sthout, swapMoves i1 i2 sth = (.success (), sthout) ∧
        sthout = { sth with sorted_moves :=
          ((sth.sorted_moves.set i1 (holEl i2 sth.sorted_moves)).set i2
            (holEl i1 sth.sorted_moves)) } := by
  intro sth i1 i2 ⟨h1, h2⟩
  refine ⟨_, ?_, rfl⟩
  simp only [swapMoves, Translator.Monadic.MonadBase.bind, ignoreBind, sortedMovesSubEqn,
    if_pos h1, if_pos h2, updateSortedMovesEqn, List.length_set]

/-- `swap_moves` permutes the moves and fixes every other cell. -/
private theorem swapMoves_perm (sth : LinearScanHiddenState) (i1 i2 : Nat)
    (h1 : i1 < sth.sorted_moves.length) (h2 : i2 < sth.sorted_moves.length) :
    ∃ sthout, swapMoves i1 i2 sth = (.success (), sthout) ∧
      sthout = { sth with sorted_moves := sthout.sorted_moves } ∧
      sth.sorted_moves.Perm sthout.sorted_moves ∧
      (∀ j, j ≠ i1 → j ≠ i2 → holEl j sthout.sorted_moves = holEl j sth.sorted_moves) := by
  obtain ⟨s, hs, hseq⟩ := swapMovesEq sth i1 i2 ⟨h1, h2⟩
  refine ⟨s, hs, by rw [hseq], ?_, fun j e1 e2 => ?_⟩
  · rw [hseq]
    have := perm_swap sth.sorted_moves i1 i2 h1 h2
    rwa [← holEl_eq_getElem _ _ h1, ← holEl_eq_getElem _ _ h2] at this
  · rw [hseq]
    show holEl j ((sth.sorted_moves.set i1 _).set i2 _) = _
    rw [holEl_swap _ _ _ _ h1 h2, if_neg (Ne.symm e2), if_neg (Ne.symm e1)]

/-- Exact HOL `swap_moves_correct` (`linear_scanProofScript.sml:4250-4262`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "swap_moves_correct"]
theorem swapMovesCorrect :
    ∀ (sth : LinearScanHiddenState) (i1 i2 : Nat),
      i1 < sth.sorted_moves.length ∧ i2 < sth.sorted_moves.length →
      ∃ sthout, swapMoves i1 i2 sth = (.success (), sthout) ∧
        sthout = { sth with sorted_moves := sthout.sorted_moves } ∧
        sthout.sorted_moves.length = sth.sorted_moves.length ∧
        (∀ n, i1 < n ∧ i2 < n ∧ n ≤ sth.sorted_moves.length →
          holPerm (sth.sorted_moves.take n) (sthout.sorted_moves.take n)) := by
  intro sth i1 i2 ⟨h1, h2⟩
  obtain ⟨s, hs, hst, hp, hag⟩ := swapMoves_perm sth i1 i2 h1 h2
  refine ⟨s, hs, hst, hp.length_eq.symm, fun n ⟨hn1, hn2, _⟩ => (holPerm_iff _ _).mpr
    (perm_take_of_agree (r := max i1 i2 + 1) hp
      (fun j hj => hag j (by omega) (by omega)) (by omega))⟩

/-- `partition_moves` in invariant form. -/
private theorem partitionMovesAux (ppiv : Nat) :
    ∀ (k l r : Nat) (sth : LinearScanHiddenState), r - l = k →
      l ≤ sth.sorted_moves.length → r ≤ sth.sorted_moves.length →
      ∃ mid sthout, partitionMoves l ppiv r sth = (.success mid, sthout) ∧
        (l ≤ r → l ≤ mid ∧ mid ≤ r) ∧
        sthout = { sth with sorted_moves := sthout.sorted_moves } ∧
        sth.sorted_moves.Perm sthout.sorted_moves ∧
        (∀ ind, ind < l ∨ r ≤ ind →
          holEl ind sthout.sorted_moves = holEl ind sth.sorted_moves) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro l r sth hk hl hr
  rw [partitionMoves]
  by_cases hrl : r ≤ l
  · rw [dif_pos hrl]
    exact ⟨l, sth, rfl, fun h => ⟨Nat.le_refl _, h⟩, rfl, List.Perm.refl _, fun _ _ => rfl⟩
  rw [dif_neg hrl]
  have hlen : l < sth.sorted_moves.length := by omega
  simp only [Translator.Monadic.MonadBase.bind, sortedMovesSubEqn, if_pos hlen]
  split
  · obtain ⟨mid, sthout, hrun, hmid, hst, hp, hag⟩ :=
      ih (r - (l + 1)) (by omega) (l + 1) r sth rfl (by omega) hr
    exact ⟨mid, sthout, hrun, fun _ => by have := hmid (by omega); omega, hst, hp,
      fun ind h => hag ind (by omega)⟩
  · obtain ⟨s', hs', hst', hp', hag'⟩ := swapMoves_perm sth l (r - 1) hlen (by omega)
    have hs'len : s'.sorted_moves.length = sth.sorted_moves.length := hp'.length_eq.symm
    simp only [ignoreBind, hs']
    obtain ⟨mid, sthout, hrun, hmid, hst, hp, hag⟩ :=
      ih (r - 1 - l) (by omega) l (r - 1) s' rfl (by omega) (by omega)
    exact ⟨mid, sthout, hrun, fun _ => by have := hmid (by omega); omega,
      by rw [hst, hst'], hp'.trans hp,
      fun ind h => by rw [hag ind (by omega), hag' ind (by omega) (by omega)]⟩

/-- Exact HOL `partition_moves_correct` (`linear_scanProofScript.sml:4264-4295`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "partition_moves_correct"]
theorem partitionMovesCorrect :
    ∀ (l ppiv r : Nat) (sth : LinearScanHiddenState),
      l ≤ sth.sorted_moves.length ∧ r ≤ sth.sorted_moves.length →
      ∃ mid sthout, partitionMoves l ppiv r sth = (.success mid, sthout) ∧
        (l ≤ r → l ≤ mid ∧ mid ≤ r) ∧
        sthout = { sth with sorted_moves := sthout.sorted_moves } ∧
        sthout.sorted_moves.length = sth.sorted_moves.length ∧
        (∀ n, l ≤ n ∧ r ≤ n ∧ n ≤ sth.sorted_moves.length →
          holPerm (sth.sorted_moves.take n) (sthout.sorted_moves.take n)) := by
  intro l ppiv r sth ⟨hl, hr⟩
  obtain ⟨mid, sthout, hrun, hmid, hst, hp, hag⟩ := partitionMovesAux ppiv (r - l) l r sth rfl hl hr
  exact ⟨mid, sthout, hrun, hmid, hst, hp.length_eq.symm,
    fun n ⟨_, hrn, _⟩ => (holPerm_iff _ _).mpr
      (perm_take_of_agree hp (fun i hi => hag i (Or.inr hi)) hrn)⟩

/-- `sort_moves` in invariant form. -/
private theorem sortMovesAux :
    ∀ (k l r : Nat) (sth : LinearScanHiddenState), r - l = k →
      l ≤ sth.sorted_moves.length → r ≤ sth.sorted_moves.length →
      ∃ sthout, sortMoves l r sth = (.success (), sthout) ∧
        sthout = { sth with sorted_moves := sthout.sorted_moves } ∧
        sth.sorted_moves.Perm sthout.sorted_moves ∧
        (∀ ind, ind < l ∨ r ≤ ind →
          holEl ind sthout.sorted_moves = holEl ind sth.sorted_moves) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro l r sth hk hl hr
  rw [sortMoves]
  by_cases hrl : r ≤ l + 1
  · rw [dif_pos hrl]
    exact ⟨sth, rfl, rfl, List.Perm.refl _, fun _ _ => rfl⟩
  rw [dif_neg hrl]
  have hlen : l < sth.sorted_moves.length := by omega
  obtain ⟨mid, s1, hrun1, hmid1, hst1, hp1, hag1⟩ :=
    partitionMovesAux (holEl l sth.sorted_moves).1 (r - (l + 1)) (l + 1) r sth rfl (by omega) hr
  obtain ⟨hm1, hm2⟩ := hmid1 (by omega)
  have hlen1 : s1.sorted_moves.length = sth.sorted_moves.length := hp1.length_eq.symm
  obtain ⟨s2, hs2, hst2, hp2, hag2⟩ := swapMoves_perm s1 l (mid - 1) (by omega) (by omega)
  have hlen2 : s2.sorted_moves.length = sth.sorted_moves.length := by
    rw [← hp2.length_eq, hlen1]
  obtain ⟨s3, hrun3, hst3, hp3, hag3⟩ :=
    ih (mid - 1 - l) (by omega) l (mid - 1) s2 rfl (by omega) (by omega)
  have hlen3 : s3.sorted_moves.length = sth.sorted_moves.length := by
    rw [← hp3.length_eq, hlen2]
  obtain ⟨s4, hrun4, hst4, hp4, hag4⟩ := ih (r - mid) (by omega) mid r s3 rfl (by omega) (by omega)
  refine ⟨s4, ?_, by rw [hst4, hst3, hst2, hst1], hp1.trans (hp2.trans (hp3.trans hp4)),
    fun ind h => ?_⟩
  · simp only [Translator.Monadic.MonadBase.bind, sortedMovesSubEqn, if_pos hlen, hrun1]
    simp only [ignoreBind, hs2, dif_neg (show ¬ (mid ≤ l ∨ r < mid) by omega), hrun3, hrun4]
  · rw [hag4 ind (by omega), hag3 ind (by omega), hag2 ind (by omega) (by omega),
      hag1 ind (by omega)]

/-- Exact HOL `sort_moves_correct` (`linear_scanProofScript.sml:4297-4330`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "sort_moves_correct"]
theorem sortMovesCorrect :
    ∀ (l r : Nat) (sth : LinearScanHiddenState),
      l ≤ sth.sorted_moves.length ∧ r ≤ sth.sorted_moves.length →
      ∃ sthout, sortMoves l r sth = (.success (), sthout) ∧
        sthout = { sth with sorted_moves := sthout.sorted_moves } ∧
        sthout.sorted_moves.length = sth.sorted_moves.length ∧
        (∀ n, l ≤ n ∧ r ≤ n ∧ n ≤ sth.sorted_moves.length →
          holPerm (sth.sorted_moves.take n) (sthout.sorted_moves.take n)) := by
  intro l r sth ⟨hl, hr⟩
  obtain ⟨sthout, hrun, hst, hp, hag⟩ := sortMovesAux (r - l) l r sth rfl hl hr
  exact ⟨sthout, hrun, hst, hp.length_eq.symm,
    fun n ⟨_, hrn, _⟩ => (holPerm_iff _ _).mpr
      (perm_take_of_agree hp (fun i hi => hag i (Or.inr hi)) hrn)⟩

end Flapjack.LinearScan
