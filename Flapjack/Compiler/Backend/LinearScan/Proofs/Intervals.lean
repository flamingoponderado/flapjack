import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.LiveTree

/-!
# linear_scanProof: interval numbering properties

Ports of `linear_scanProofScript.sml:600-1765`: monotonicity of
`check_number_property(_strong)`, lookup/domain equations for the conditional
interval updates, and the properties of `get_intervals` and
`get_intervals_withlive` used by `check_intervals_check_live_tree`.

Rendering as in `LiveTree`: HOL sets are predicates, HOL `int` is `Int`,
`option_CASE (lookup r s) d (\x.x)` is the `match` on the lookup, and a HOL
pattern hypothesis `(n_out, beg_out, end_out) = get_intervals ...` is kept as
that equation. Predicate arguments of `check_number_property(_strong)` are the
HOL lambdas, verbatim.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc

/-- Exact HOL `check_number_property_strong_monotone_weak`
(`linear_scanProofScript.sml:600-609`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_number_property_strong_monotone_weak"]
theorem checkNumberPropertyStrongMonotoneWeak :
    ∀ (P Q : Int → NumSet → Prop) (lt : LiveTree) (n : Int) (live : NumSet),
      (∀ n' live', P n' live' → Q n' live') ∧ checkNumberPropertyStrong P lt n live →
      checkNumberPropertyStrong Q lt n live := by
  intro P Q lt
  induction lt with
  | writes l => intro n live ⟨hPQ, h⟩; exact hPQ _ _ h
  | reads l => intro n live ⟨hPQ, h⟩; exact hPQ _ _ h
  | branch lt1 lt2 ih1 ih2 =>
      intro n live ⟨hPQ, h⟩
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨ih1 _ _ ⟨hPQ, h1⟩, ih2 _ _ ⟨hPQ, h2⟩, hPQ _ _ h3⟩
  | seq lt1 lt2 ih1 ih2 =>
      intro n live ⟨hPQ, h⟩
      obtain ⟨h1, h2⟩ := h
      exact ⟨ih1 _ _ ⟨hPQ, h1⟩, ih2 _ _ ⟨hPQ, h2⟩⟩

/-- Exact HOL `check_number_property_strong_monotone`
(`linear_scanProofScript.sml:612-641`): the implication is only needed at
numbers no smaller than `n - size_of_live_tree lt`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_number_property_strong_monotone"]
theorem checkNumberPropertyStrongMonotone :
    ∀ (P Q : Int → NumSet → Prop) (lt : LiveTree) (n : Int) (live : NumSet),
      (∀ n' live', n - sizeOfLiveTree lt ≤ n' ∧ P n' live' → Q n' live') ∧
        checkNumberPropertyStrong P lt n live →
      checkNumberPropertyStrong Q lt n live := by
  intro P Q lt
  induction lt with
  | writes l =>
      intro n live ⟨hPQ, h⟩
      exact hPQ _ _ ⟨by simp [sizeOfLiveTree], h⟩
  | reads l =>
      intro n live ⟨hPQ, h⟩
      exact hPQ _ _ ⟨by simp [sizeOfLiveTree], h⟩
  | branch lt1 lt2 ih1 ih2 =>
      intro n live ⟨hPQ, h⟩
      obtain ⟨h1, h2, h3⟩ := h
      have p1 := sizeOfLiveTreePositive lt1
      have p2 := sizeOfLiveTreePositive lt2
      simp only [sizeOfLiveTree] at hPQ
      refine ⟨ih1 _ _ ⟨fun n' live' ⟨hn, hp⟩ => hPQ n' live' ⟨by omega, hp⟩, h1⟩,
        ih2 _ _ ⟨fun n' live' ⟨hn, hp⟩ => hPQ n' live' ⟨by omega, hp⟩, h2⟩,
        hPQ _ _ ⟨by simp only [sizeOfLiveTree]; omega, h3⟩⟩
  | seq lt1 lt2 ih1 ih2 =>
      intro n live ⟨hPQ, h⟩
      obtain ⟨h1, h2⟩ := h
      have p1 := sizeOfLiveTreePositive lt1
      have p2 := sizeOfLiveTreePositive lt2
      simp only [sizeOfLiveTree] at hPQ
      exact ⟨ih1 _ _ ⟨fun n' live' ⟨hn, hp⟩ => hPQ n' live' ⟨by omega, hp⟩, h1⟩,
        ih2 _ _ ⟨fun n' live' ⟨hn, hp⟩ => hPQ n' live' ⟨by omega, hp⟩, h2⟩⟩

/-- Exact HOL `check_number_property_strong_end` (`linear_scanProofScript.sml:643-654`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_number_property_strong_end"]
theorem checkNumberPropertyStrongEnd :
    ∀ (P : Int → NumSet → Prop) (lt : LiveTree) (n : Int) (live : NumSet),
      checkNumberPropertyStrong P lt n live →
      P (n - sizeOfLiveTree lt) (getLiveBackward lt live) := by
  intro P lt
  induction lt with
  | writes l =>
      intro n live h
      simp only [checkNumberPropertyStrong] at h
      simpa [sizeOfLiveTree, getLiveBackward] using h
  | reads l =>
      intro n live h
      simp only [checkNumberPropertyStrong] at h
      simpa [sizeOfLiveTree, getLiveBackward] using h
  | branch lt1 lt2 _ _ => intro n live h; exact h.2.2
  | seq lt1 lt2 ih1 _ =>
      intro n live h
      have := ih1 _ _ h.1
      simp only [sizeOfLiveTree, getLiveBackward]
      rw [show n - (sizeOfLiveTree lt1 + sizeOfLiveTree lt2) =
        n - sizeOfLiveTree lt2 - sizeOfLiveTree lt1 by omega]
      exact this

/-- Exact HOL `check_number_property_monotone_weak` (`linear_scanProofScript.sml:656-665`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_number_property_monotone_weak"]
theorem checkNumberPropertyMonotoneWeak :
    ∀ (P Q : Int → NumSet → Prop) (lt : LiveTree) (n : Int) (live : NumSet),
      (∀ n' live', P n' live' → Q n' live') ∧ checkNumberProperty P lt n live →
      checkNumberProperty Q lt n live := by
  intro P Q lt
  induction lt with
  | writes l => intro n live ⟨hPQ, h⟩; exact hPQ _ _ h
  | reads l => intro n live ⟨hPQ, h⟩; exact hPQ _ _ h
  | branch lt1 lt2 ih1 ih2 =>
      intro n live ⟨hPQ, h⟩
      exact ⟨ih1 _ _ ⟨hPQ, h.1⟩, ih2 _ _ ⟨hPQ, h.2⟩⟩
  | seq lt1 lt2 ih1 ih2 =>
      intro n live ⟨hPQ, h⟩
      exact ⟨ih1 _ _ ⟨hPQ, h.1⟩, ih2 _ _ ⟨hPQ, h.2⟩⟩

/-- Exact HOL `lookup_numset_list_add_if` (`linear_scanProofScript.sml:668-695`);
the free predicate `P` is quantified first. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "lookup_numset_list_add_if"]
theorem lookupNumsetListAddIf :
    ∀ (P : Int → Int → Bool) (r : Nat) (l : List Nat) (v : Int) (s : Spt Int),
      sptLookup r (numsetListAddIf l v s P) =
        if r ∈ l then
          (match sptLookup r s with
            | some vr => if P v vr then some v else some vr
            | none => some v)
        else sptLookup r s := by
  intro P r l
  induction l with
  | nil => intro v s; simp [numsetListAddIf]
  | cons h l ih =>
      intro v s
      have hins : ∀ t : Spt Int, sptLookup r (sptInsert h v t) =
          if r = h then some v else sptLookup r t := by
        intro t
        by_cases hr : r = h
        · subst hr; simp [sptLookup_sptInsert_same]
        · simp [hr, sptLookup_sptInsert_ne h r v t hr]
      cases hl : sptLookup h s with
      | some v' =>
          cases hP : P v v' with
          | true =>
              simp only [numsetListAddIf, hl, hP, if_true]
              rw [ih, hins]
              by_cases hr : r = h
              · subst hr; simp [hl, hP]
              · simp [hr]
          | false =>
              simp only [numsetListAddIf, hl, hP, Bool.false_eq_true, if_false]
              rw [ih]
              by_cases hr : r = h
              · subst hr; simp [hl, hP]
              · simp [hr]
      | none =>
          simp only [numsetListAddIf, hl]
          rw [ih, hins]
          by_cases hr : r = h
          · subst hr; simp [hl]
          · simp [hr]

/-- Exact HOL `lookup_numset_list_add_if_lt` (`linear_scanProofScript.sml:698-713`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "lookup_numset_list_add_if_lt"]
theorem lookupNumsetListAddIfLt :
    ∀ (r : Nat) (l : List Nat) (v : Int) (s : Spt Int),
      sptLookup r (numsetListAddIfLt l v s) =
        if r ∈ l then
          (match sptLookup r s with
            | some vr => if v ≤ vr then some v else some vr
            | none => some v)
        else sptLookup r s := by
  intro r l v s
  rw [numsetListAddIfLt, lookupNumsetListAddIf]
  simp only [decide_eq_true_eq]

/-- Exact HOL `lookup_numset_list_add_if_gt` (`linear_scanProofScript.sml:715-730`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "lookup_numset_list_add_if_gt"]
theorem lookupNumsetListAddIfGt :
    ∀ (r : Nat) (l : List Nat) (v : Int) (s : Spt Int),
      sptLookup r (numsetListAddIfGt l v s) =
        if r ∈ l then
          (match sptLookup r s with
            | some vr => if vr ≤ v then some v else some vr
            | none => some v)
        else sptLookup r s := by
  intro r l v s
  rw [numsetListAddIfGt, lookupNumsetListAddIf]
  simp only [decide_eq_true_eq]

/-- Exact HOL `domain_numset_list_add_if` (`linear_scanProofScript.sml:732-747`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "domain_numset_list_add_if"]
theorem domainNumsetListAddIf :
    ∀ (l : List Nat) (v : Int) (s : Spt Int) (P : Int → Int → Bool),
      sptDomain (numsetListAddIf l v s P) = fun x => x ∈ l ∨ sptDomain s x := by
  intro l v s P
  funext x
  apply propext
  unfold sptDomain
  rw [lookupNumsetListAddIf]
  by_cases hx : x ∈ l
  · simp only [hx, if_true, true_or, iff_true]
    split <;> (try split) <;> simp
  · simp [hx]

/-- Exact HOL `domain_numset_list_add_if_lt` (`linear_scanProofScript.sml:749-753`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "domain_numset_list_add_if_lt"]
theorem domainNumsetListAddIfLt :
    ∀ (l : List Nat) (v : Int) (s : Spt Int),
      sptDomain (numsetListAddIfLt l v s) = fun x => x ∈ l ∨ sptDomain s x := by
  intro l v s
  exact domainNumsetListAddIf l v s _

/-- Exact HOL `domain_numset_list_add_if_gt` (`linear_scanProofScript.sml:755-759`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "domain_numset_list_add_if_gt"]
theorem domainNumsetListAddIfGt :
    ∀ (l : List Nat) (v : Int) (s : Spt Int),
      sptDomain (numsetListAddIfGt l v s) = fun x => x ∈ l ∨ sptDomain s x := by
  intro l v s
  exact domainNumsetListAddIf l v s _

/-- Exact HOL `lookup_numset_list_delete` (`linear_scanProofScript.sml:761-767`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "lookup_numset_list_delete"]
theorem lookupNumsetListDelete {α : Type} :
    ∀ (l : List Nat) (s : Spt α) (x : Nat),
      sptLookup x (numsetListDelete l s) = if x ∈ l then none else sptLookup x s := by
  intro l
  induction l with
  | nil => intro s x; simp [numsetListDelete]
  | cons h l ih =>
      intro s x
      rw [numsetListDelete, ih, sptLookup_sptDelete]
      by_cases hx : x = h <;> by_cases hl : x ∈ l <;> simp [hx, hl]

/-- Exact HOL `get_intervals_nout` (`linear_scanProofScript.sml:769-780`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_nout"]
theorem getIntervalsNout :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in →
      n_out = n_in - sizeOfLiveTree lt := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in n_out beg_out end_out h
      simp only [getIntervals, Prod.mk.injEq] at h
      simp [h.1, sizeOfLiveTree]
  | reads l =>
      intro n_in beg_in end_in n_out beg_out end_out h
      simp only [getIntervals, Prod.mk.injEq] at h
      simp [h.1, sizeOfLiveTree]
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out h
      simp only [getIntervals] at h
      rcases h2 : getIntervals lt2 n_in beg_in end_in with ⟨n2, b2, e2⟩
      rw [h2] at h
      have e1 := ih1 n2 b2 e2 n_out beg_out end_out h
      have e2' := ih2 n_in beg_in end_in n2 b2 e2 h2.symm
      simp only [sizeOfLiveTree]
      omega

/-- Exact HOL `get_intervals_withlive_nout` (`linear_scanProofScript.sml:782-793`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_nout"]
theorem getIntervalsWithliveNout :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int) (live : NumSet),
      (n_out, beg_out, end_out) = getIntervalsWithlive lt n_in beg_in end_in live →
      n_out = n_in - sizeOfLiveTree lt := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in n_out beg_out end_out live h
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      simp [h.1, sizeOfLiveTree]
  | reads l =>
      intro n_in beg_in end_in n_out beg_out end_out live h
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      simp [h.1, sizeOfLiveTree]
  | branch lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out live h
      simp only [getIntervalsWithlive] at h
      rcases h2 : getIntervalsWithlive lt2 n_in beg_in end_in live with ⟨n2, b2, e2⟩
      rw [h2] at h
      simp only at h
      rcases h1 : getIntervalsWithlive lt1 n2 (sptDifference b2 live) e2 live with ⟨n1, b1, e1⟩
      rw [h1] at h
      simp only [Prod.mk.injEq] at h
      have k1 := ih1 _ _ _ _ _ _ _ h1.symm
      have k2 := ih2 _ _ _ _ _ _ _ h2.symm
      simp only [sizeOfLiveTree]
      omega
  | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out live h
      simp only [getIntervalsWithlive] at h
      rcases h2 : getIntervalsWithlive lt2 n_in beg_in end_in live with ⟨n2, b2, e2⟩
      rw [h2] at h
      simp only at h
      rcases h1 : getIntervalsWithlive lt1 n2 b2 e2 (getLiveBackward lt2 live) with ⟨n1, b1, e1⟩
      rw [h1] at h
      simp only [Prod.mk.injEq] at h
      have k1 := ih1 _ _ _ _ _ _ _ h1.symm
      have k2 := ih2 _ _ _ _ _ _ _ h2.symm
      simp only [sizeOfLiveTree]
      omega

/-- Exact HOL `get_intervals_intend_augment` (`linear_scanProofScript.sml:796-817`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_intend_augment"]
theorem getIntervalsIntendAugment :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in →
      ∀ r v, sptLookup r end_in = some v → ∃ v', sptLookup r end_out = some v' ∧ v ≤ v' := by
  intro lt
  induction lt with
  | writes l | reads l =>
      intro n_in beg_in end_in n_out beg_out end_out h r v hv
      simp only [getIntervals, Prod.mk.injEq] at h
      rw [h.2.2, lookupNumsetListAddIfGt, hv]
      by_cases hm : r ∈ l
      · rw [if_pos hm]
        by_cases hc : v ≤ n_in
        · exact ⟨n_in, by simp [hc], hc⟩
        · exact ⟨v, by simp [hc], Int.le_refl v⟩
      · exact ⟨v, by simp [hm], Int.le_refl v⟩
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out h r v hv
      simp only [getIntervals] at h
      rcases h2 : getIntervals lt2 n_in beg_in end_in with ⟨n2, b2, e2⟩
      rw [h2] at h
      obtain ⟨v', hv', hle⟩ := ih2 _ _ _ _ _ _ h2.symm r v hv
      obtain ⟨v'', hv'', hle'⟩ := ih1 _ _ _ _ _ _ h r v' hv'
      exact ⟨v'', hv'', Int.le_trans hle hle'⟩

/-- Exact HOL `check_number_property_intend` (`linear_scanProofScript.sml:819-850`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_number_property_intend"]
theorem checkNumberPropertyIntend :
    ∀ (end_out : Spt Int) (lt : LiveTree) (n_in : Int) (live_in : NumSet),
      checkNumberProperty (fun n (live : NumSet) => ∀ r, sptDomain live r →
          ∃ v, sptLookup r end_out = some v ∧ n + 1 ≤ v) lt n_in live_in →
      ∀ r, sptDomain (getLiveBackward lt live_in) r →
        ∃ v, sptLookup r end_out = some v ∧ n_in - sizeOfLiveTree lt ≤ v := by
  intro end_out lt
  induction lt with
  | writes l | reads l =>
      intro n_in live_in h r hr
      obtain ⟨v, hv, hle⟩ := h r hr
      exact ⟨v, hv, by simp only [sizeOfLiveTree]; omega⟩
  | branch lt1 lt2 ih1 ih2 =>
      intro n_in live_in h r hr
      obtain ⟨h1, h2⟩ := h
      have p1 := sizeOfLiveTreePositive lt1
      have p2 := sizeOfLiveTreePositive lt2
      simp only [getLiveBackward] at hr
      rw [domainNumsetListInsert] at hr
      rcases (branchDomainIff _ _ r).mp hr with hr | hr
      · obtain ⟨v, hv, hle⟩ := ih1 _ _ h1 r hr
        exact ⟨v, hv, by simp only [sizeOfLiveTree]; omega⟩
      · obtain ⟨v, hv, hle⟩ := ih2 _ _ h2 r hr
        exact ⟨v, hv, by simp only [sizeOfLiveTree]; omega⟩
  | seq lt1 lt2 ih1 _ =>
      intro n_in live_in h r hr
      obtain ⟨v, hv, hle⟩ := ih1 _ _ h.1 r hr
      exact ⟨v, hv, by simp only [sizeOfLiveTree]; omega⟩

/-! Structural unfolding of the compound `get_intervals` cases (Flapjack
helpers for the `pairarg_tac` steps of the HOL proofs). -/

private theorem getIntervalsBranch (lt1 lt2 : LiveTree) (n : Int) (b e : Spt Int)
    (n_out : Int) (b_out e_out : Spt Int)
    (h : (n_out, b_out, e_out) = getIntervals (.branch lt1 lt2) n b e) :
    ∃ n2 b2 e2, (n2, b2, e2) = getIntervals lt2 n b e ∧
      (n_out, b_out, e_out) = getIntervals lt1 n2 b2 e2 := by
  rcases h2 : getIntervals lt2 n b e with ⟨n2, b2, e2⟩
  simp only [getIntervals] at h
  rw [h2] at h
  exact ⟨n2, b2, e2, rfl, h⟩

private theorem getIntervalsSeq (lt1 lt2 : LiveTree) (n : Int) (b e : Spt Int)
    (n_out : Int) (b_out e_out : Spt Int)
    (h : (n_out, b_out, e_out) = getIntervals (.seq lt1 lt2) n b e) :
    ∃ n2 b2 e2, (n2, b2, e2) = getIntervals lt2 n b e ∧
      (n_out, b_out, e_out) = getIntervals lt1 n2 b2 e2 := by
  rcases h2 : getIntervals lt2 n b e with ⟨n2, b2, e2⟩
  simp only [getIntervals] at h
  rw [h2] at h
  exact ⟨n2, b2, e2, rfl, h⟩

private theorem getIntervalsWithliveBranch (lt1 lt2 : LiveTree) (n : Int) (b e : Spt Int)
    (live : NumSet) (n_out : Int) (b_out e_out : Spt Int)
    (h : (n_out, b_out, e_out) = getIntervalsWithlive (.branch lt1 lt2) n b e live) :
    ∃ n2 b2 e2 b1, (n2, b2, e2) = getIntervalsWithlive lt2 n b e live ∧
      (n_out, b1, e_out) = getIntervalsWithlive lt1 n2 (sptDifference b2 live) e2 live ∧
      b_out = sptDifference b1
        (sptUnion (getLiveBackward lt1 live) (getLiveBackward lt2 live)) := by
  rcases h2 : getIntervalsWithlive lt2 n b e live with ⟨n2, b2, e2⟩
  rcases h1 : getIntervalsWithlive lt1 n2 (sptDifference b2 live) e2 live with ⟨n1, b1, e1⟩
  simp only [getIntervalsWithlive, h2, h1, Prod.mk.injEq] at h
  refine ⟨n2, b2, e2, b1, rfl, ?_, h.2.1⟩
  rw [h1, h.1, h.2.2]

private theorem getIntervalsWithliveSeq (lt1 lt2 : LiveTree) (n : Int) (b e : Spt Int)
    (live : NumSet) (n_out : Int) (b_out e_out : Spt Int)
    (h : (n_out, b_out, e_out) = getIntervalsWithlive (.seq lt1 lt2) n b e live) :
    ∃ n2 b2 e2, (n2, b2, e2) = getIntervalsWithlive lt2 n b e live ∧
      (n_out, b_out, e_out) =
        getIntervalsWithlive lt1 n2 b2 e2 (getLiveBackward lt2 live) := by
  rcases h2 : getIntervalsWithlive lt2 n b e live with ⟨n2, b2, e2⟩
  rcases h1 : getIntervalsWithlive lt1 n2 b2 e2 (getLiveBackward lt2 live) with ⟨n1, b1, e1⟩
  simp only [getIntervalsWithlive, h2, h1] at h
  exact ⟨n2, b2, e2, rfl, h.trans h1.symm⟩

private theorem lookupDifferenceEq {α β : Type} (t : Spt α) (s : Spt β) (r : Nat) :
    sptLookup r (sptDifference t s) = if sptLookup r s = none then sptLookup r t else none :=
  sptLookupDifference t s r

/-- Exact HOL `get_intervals_live_less_end` (`linear_scanProofScript.sml:852-907`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_live_less_end"]
theorem getIntervalsLiveLessEnd :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (live_in : NumSet)
      (n_out : Int) (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in ∧
      (∀ r, sptDomain live_in r → ∃ v, sptLookup r end_in = some v ∧ n_in ≤ v) →
      checkNumberProperty (fun n (live : NumSet) => ∀ r, sptDomain live r →
        ∃ v, sptLookup r end_out = some v ∧ n + 1 ≤ v) lt n_in live_in := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, hlive⟩
      simp only [getIntervals, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      intro r hr
      rw [RegAlloc.domainNumsetListDelete] at hr
      obtain ⟨v, hv, hle⟩ := hlive r hr.1
      refine ⟨v, ?_, by omega⟩
      rw [lookupNumsetListAddIfGt, if_neg hr.2, hv]
  | reads l =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, hlive⟩
      simp only [getIntervals, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      intro r hr
      rw [domainNumsetListInsert] at hr
      rw [lookupNumsetListAddIfGt]
      by_cases hl : r ∈ l
      · rw [if_pos hl]
        split
        · split
          · exact ⟨_, rfl, by omega⟩
          · exact ⟨_, rfl, by omega⟩
        · exact ⟨_, rfl, by omega⟩
      · rw [if_neg hl]
        obtain ⟨v, hv, hle⟩ := hlive r (hr.resolve_left hl)
        exact ⟨v, hv, by omega⟩
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, hlive⟩
      first
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsBranch lt1 lt2 _ _ _ _ _ _ h
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsSeq lt1 lt2 _ _ _ _ _ _ h
      have hn2 := getIntervalsNout lt2 _ _ _ _ _ _ h2
      have p1 := sizeOfLiveTreePositive lt1
      have p2 := sizeOfLiveTreePositive lt2
      have c2 := ih2 n_in beg_in end_in live_in n2 b2 e2 ⟨h2, hlive⟩
      have c2' : checkNumberProperty (fun n (live : NumSet) => ∀ r, sptDomain live r →
          ∃ v, sptLookup r end_out = some v ∧ n + 1 ≤ v) lt2 n_in live_in := by
        refine checkNumberPropertyMonotoneWeak _ _ lt2 n_in live_in ⟨?_, c2⟩
        intro n' live' hp r hr
        obtain ⟨v, hv, hle⟩ := hp r hr
        obtain ⟨v', hv', hle'⟩ := getIntervalsIntendAugment lt1 _ _ _ _ _ _ h1 r v hv
        exact ⟨v', hv', by omega⟩
      refine ⟨?_, c2'⟩
      rw [← hn2]
      first
        | -- Branch: lt1 starts from the same live set.
          refine ih1 n2 b2 e2 live_in n_out beg_out end_out ⟨h1, ?_⟩
          intro r hr
          obtain ⟨v, hv, hle⟩ := hlive r hr
          obtain ⟨v', hv', hle'⟩ := getIntervalsIntendAugment lt2 _ _ _ _ _ _ h2 r v hv
          exact ⟨v', hv', by omega⟩
        | -- Seq: lt1 starts from the names live before lt2.
          refine ih1 n2 b2 e2 (getLiveBackward lt2 live_in) n_out beg_out end_out ⟨h1, ?_⟩
          intro r hr
          obtain ⟨v, hv, hle⟩ := checkNumberPropertyIntend e2 lt2 n_in live_in c2 r hr
          exact ⟨v, hv, by omega⟩

/-- Exact HOL `get_intervals_withlive_intbeg_reduce`
(`linear_scanProofScript.sml:909-991`). `option_CASE x d (\x.x)` is
`Option.elim x d (fun x => x)`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_intbeg_reduce"]
theorem getIntervalsWithliveIntbegReduce :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int) (live : NumSet),
      (n_out, beg_out, end_out) = getIntervalsWithlive lt n_in beg_in end_in live ∧
      (∀ r v, sptLookup r beg_in = some v → n_in ≤ v) →
      (∀ r, (sptLookup r beg_out).elim n_out (fun x => x) ≤
        (sptLookup r beg_in).elim n_in (fun x => x)) ∧
      (∀ r v, sptLookup r beg_out = some v → n_out ≤ v) := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in n_out beg_out end_out live ⟨h, hb⟩
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      constructor
      · intro r
        rw [lookupNumsetListAddIfLt]
        split
        · cases hl : sptLookup r beg_in with
          | some vr =>
              have := hb r vr hl
              by_cases hv : n_in ≤ vr <;> simp [hv] <;> omega
          | none => simp
        · cases hl : sptLookup r beg_in with
          | some vr => simp
          | none => simp; omega
      · intro r v hv
        rw [lookupNumsetListAddIfLt] at hv
        split at hv
        · cases hl : sptLookup r beg_in with
          | some vr =>
              have := hb r vr hl
              rw [hl] at hv
              by_cases hc : n_in ≤ vr <;> simp [hc] at hv <;> omega
          | none => rw [hl] at hv; simp at hv; omega
        · have := hb r v hv; omega
  | reads l =>
      intro n_in beg_in end_in n_out beg_out end_out live ⟨h, hb⟩
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      constructor
      · intro r
        rw [lookupNumsetListDelete]
        split
        · cases hl : sptLookup r beg_in with
          | some vr => have := hb r vr hl; simp; omega
          | none => simp; omega
        · cases hl : sptLookup r beg_in with
          | some vr => simp
          | none => simp; omega
      · intro r v hv
        rw [lookupNumsetListDelete] at hv
        split at hv
        · cases hv
        · have := hb r v hv; omega
  | branch lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out live ⟨h, hb⟩
      obtain ⟨n2, b2, e2, b1, h2, h1, rfl⟩ := getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h
      obtain ⟨r2, v2⟩ := ih2 _ _ _ _ _ _ _ ⟨h2, hb⟩
      have vd : ∀ r v, sptLookup r (sptDifference b2 live) = some v → n2 ≤ v := by
        intro r v hv
        rw [lookupDifferenceEq] at hv
        split at hv
        · exact v2 r v hv
        · cases hv
      obtain ⟨r1, v1⟩ := ih1 _ _ _ _ _ _ _ ⟨h1, vd⟩
      have k2 := getIntervalsWithliveNout lt2 _ _ _ _ _ _ _ h2
      have k1 := getIntervalsWithliveNout lt1 _ _ _ _ _ _ _ h1
      have p1 := sizeOfLiveTreePositive lt1
      have p2 := sizeOfLiveTreePositive lt2
      have hinge : ∀ r, n_out ≤ (sptLookup r beg_in).elim n_in (fun x => x) := by
        intro r
        cases hl : sptLookup r beg_in with
        | some v => have := hb r v hl; simp; omega
        | none => simp; omega
      have hinge2 : ∀ r, n2 ≤ (sptLookup r beg_in).elim n_in (fun x => x) := by
        intro r
        cases hl : sptLookup r beg_in with
        | some v => have := hb r v hl; simp; omega
        | none => simp; omega
      constructor
      · intro r
        have e1 := r1 r
        have e2' := r2 r
        rw [lookupDifferenceEq]
        split
        · rw [lookupDifferenceEq] at e1
          split at e1
          · exact Int.le_trans e1 e2'
          · cases hl : sptLookup r b1 with
            | some v => rw [hl] at e1; simp at e1 ⊢; have := hinge2 r; omega
            | none => rw [hl] at e1; simp at e1 ⊢; exact hinge r
        · exact hinge r
      · intro r v hv
        rw [lookupDifferenceEq] at hv
        split at hv
        · exact v1 r v hv
        · cases hv
  | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out live ⟨h, hb⟩
      obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h
      obtain ⟨r2, v2⟩ := ih2 _ _ _ _ _ _ _ ⟨h2, hb⟩
      obtain ⟨r1, v1⟩ := ih1 _ _ _ _ _ _ _ ⟨h1, v2⟩
      exact ⟨fun r => Int.le_trans (r1 r) (r2 r), v1⟩

/-- Exact HOL `get_intervals_withlive_intbeg_nout` (`linear_scanProofScript.sml:993-1000`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_intbeg_nout"]
theorem getIntervalsWithliveIntbegNout :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int) (live : NumSet),
      (n_out, beg_out, end_out) = getIntervalsWithlive lt n_in beg_in end_in live ∧
      (∀ r v, sptLookup r beg_in = some v → n_in ≤ v) →
      (∀ r v, sptLookup r beg_out = some v → n_out ≤ v) := by
  intro lt n_in beg_in end_in n_out beg_out end_out live h
  exact (getIntervalsWithliveIntbegReduce lt n_in beg_in end_in n_out beg_out end_out live h).2

/-- Exact HOL `get_intervals_intbeg_nout` (`linear_scanProofScript.sml:1002-1028`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_intbeg_nout"]
theorem getIntervalsIntbegNout :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in ∧
      (∀ r v, sptLookup r beg_in = some v → n_in ≤ v) →
      (∀ r v, sptLookup r beg_out = some v → n_out ≤ v) := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in n_out beg_out end_out ⟨h, hb⟩ r v hv
      simp only [getIntervals, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      rw [lookupNumsetListAddIfLt] at hv
      split at hv
      · cases hl : sptLookup r beg_in with
        | some vr =>
            have := hb r vr hl
            rw [hl] at hv
            by_cases hc : n_in ≤ vr <;> simp [hc] at hv <;> omega
        | none => rw [hl] at hv; simp at hv; omega
      · have := hb r v hv; omega
  | reads l =>
      intro n_in beg_in end_in n_out beg_out end_out ⟨h, hb⟩ r v hv
      simp only [getIntervals, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      have := hb r v hv; omega
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out ⟨h, hb⟩
      first
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsBranch lt1 lt2 _ _ _ _ _ _ h
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsSeq lt1 lt2 _ _ _ _ _ _ h
      exact ih1 _ _ _ _ _ _ ⟨h1, ih2 _ _ _ _ _ _ ⟨h2, hb⟩⟩

/-- Exact HOL `get_intervals_withlive_live_intbeg` (`linear_scanProofScript.sml:1031-1059`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_live_intbeg"]
theorem getIntervalsWithliveLiveIntbeg :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (live : NumSet) (n_out : Int)
      (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervalsWithlive lt n_in beg_in end_in live ∧
      (∀ r, sptDomain live r → ¬ sptDomain beg_in r) →
      (∀ r, sptDomain (getLiveBackward lt live) r → ¬ sptDomain beg_out r) := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in live n_out beg_out end_out ⟨h, hl⟩ r hr
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      simp only [getLiveBackward] at hr
      rw [RegAlloc.domainNumsetListDelete] at hr
      rw [domainNumsetListAddIfLt]
      rintro (hm | hb)
      · exact hr.2 hm
      · exact hl r hr.1 hb
  | reads l =>
      intro n_in beg_in end_in live n_out beg_out end_out ⟨h, hl⟩ r hr
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      simp only [getLiveBackward] at hr
      rw [domainNumsetListInsert] at hr
      rw [RegAlloc.domainNumsetListDelete]
      rintro ⟨hb, hm⟩
      rcases hr with hr | hr
      · exact hm hr
      · exact hl r hr hb
  | branch lt1 lt2 _ _ =>
      intro n_in beg_in end_in live n_out beg_out end_out ⟨h, _⟩ r hr
      obtain ⟨n2, b2, e2, b1, -, -, rfl⟩ := getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h
      simp only [getLiveBackward] at hr
      rw [domainNumsetListInsert] at hr
      rw [sptDomainDifference, sptDomain_sptUnion]
      rintro ⟨-, hn⟩
      exact hn ((branchDomainIff _ _ r).mp hr)
  | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in live n_out beg_out end_out ⟨h, hl⟩ r hr
      obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h
      exact ih1 _ _ _ _ _ _ _ ⟨h1, ih2 _ _ _ _ _ _ _ ⟨h2, hl⟩⟩ r hr

/-- Exact HOL `get_intervals_withlive_n_eq_get_intervals_n`
(`linear_scanProofScript.sml:1194-1204`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_n_eq_get_intervals_n"]
theorem getIntervalsWithliveNEqGetIntervalsN :
    ∀ (lt : LiveTree) (n : Int) (beg end_ beg' end' : Spt Int) (n1 : Int)
      (beg1 end1 : Spt Int) (n2 : Int) (beg2 end2 : Spt Int) (live : NumSet),
      (n1, beg1, end1) = getIntervals lt n beg end_ ∧
      (n2, beg2, end2) = getIntervalsWithlive lt n beg' end' live →
      n1 = n2 := by
  intro lt n beg end_ beg' end' n1 beg1 end1 n2 beg2 end2 live ⟨h1, h2⟩
  rw [getIntervalsNout lt _ _ _ _ _ _ h1, getIntervalsWithliveNout lt _ _ _ _ _ _ _ h2]

/-- Exact HOL `get_intervals_withlive_end_eq_get_intervals_end`
(`linear_scanProofScript.sml:1206-1217`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_end_eq_get_intervals_end"]
theorem getIntervalsWithliveEndEqGetIntervalsEnd :
    ∀ (lt : LiveTree) (n : Int) (beg beg' end_ : Spt Int) (n1 : Int)
      (beg1 end1 : Spt Int) (n2 : Int) (beg2 end2 : Spt Int) (live : NumSet),
      (n1, beg1, end1) = getIntervals lt n beg end_ ∧
      (n2, beg2, end2) = getIntervalsWithlive lt n beg' end_ live →
      end1 = end2 := by
  intro lt
  induction lt with
  | writes l | reads l =>
      intro n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live ⟨h1, h2⟩
      simp only [getIntervals, getIntervalsWithlive, Prod.mk.injEq] at h1 h2
      rw [h1.2.2, h2.2.2]
  | branch lt1 lt2 ih1 ih2 =>
      intro n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live ⟨h1, h2⟩
      obtain ⟨m2, b2, e2, g2, g1⟩ := getIntervalsBranch lt1 lt2 _ _ _ _ _ _ h1
      obtain ⟨m2', b2', e2', b1', w2, w1, -⟩ :=
        getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h2
      have hn := getIntervalsWithliveNEqGetIntervalsN lt2 _ _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      have he := ih2 _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      subst hn; subst he
      exact ih1 _ _ _ _ _ _ _ _ _ _ _ ⟨g1, w1⟩
  | seq lt1 lt2 ih1 ih2 =>
      intro n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live ⟨h1, h2⟩
      obtain ⟨m2, b2, e2, g2, g1⟩ := getIntervalsSeq lt1 lt2 _ _ _ _ _ _ h1
      obtain ⟨m2', b2', e2', w2, w1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h2
      have hn := getIntervalsWithliveNEqGetIntervalsN lt2 _ _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      have he := ih2 _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      subst hn; subst he
      exact ih1 _ _ _ _ _ _ _ _ _ _ _ ⟨g1, w1⟩

/-- Exact HOL `get_intervals_beg_subset_registers`
(`linear_scanProofScript.sml:1326-1340`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_beg_subset_registers"]
theorem getIntervalsBegSubsetRegisters :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in →
      ∀ x, sptDomain beg_out x → sptDomain beg_in x ∨ liveTreeRegisters lt x := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in n_out beg_out end_out h x hx
      simp only [getIntervals, Prod.mk.injEq] at h
      rw [h.2.1, domainNumsetListAddIfLt] at hx
      exact hx.symm
  | reads l =>
      intro n_in beg_in end_in n_out beg_out end_out h x hx
      simp only [getIntervals, Prod.mk.injEq] at h
      rw [h.2.1] at hx
      exact Or.inl hx
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out h x hx
      first
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsBranch lt1 lt2 _ _ _ _ _ _ h
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsSeq lt1 lt2 _ _ _ _ _ _ h
      simp only [liveTreeRegisters]
      rcases ih1 _ _ _ _ _ _ h1 x hx with hx | hx
      · rcases ih2 _ _ _ _ _ _ h2 x hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inr hx)
      · exact Or.inr (Or.inl hx)

/-- Exact HOL `get_intervals_withlive_beg_lipschitz`
(`linear_scanProofScript.sml:1343-1377`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_beg_lipschitz"]
theorem getIntervalsWithliveBegLipschitz :
    ∀ (lt : LiveTree) (n1 : Int) (beg1 end1 : Spt Int) (live : NumSet) (n2 : Int)
      (beg2 end2 s : Spt Int) (nout1 : Int) (begout1 endout1 : Spt Int) (nout2 : Int)
      (begout2 endout2 : Spt Int),
      (nout1, begout1, endout1) = getIntervalsWithlive lt n1 beg1 end1 live ∧
      (nout2, begout2, endout2) = getIntervalsWithlive lt n2 beg2 end2 live ∧
      (∀ x, sptDomain beg2 x → sptDomain beg1 x ∨ sptDomain s x) →
      ∀ x, sptDomain begout2 x → sptDomain begout1 x ∨ sptDomain s x := by
  intro lt
  induction lt with
  | writes l =>
      intro n1 beg1 end1 live n2 beg2 end2 s nout1 begout1 endout1 nout2 begout2 endout2
        ⟨h1, h2, hsub⟩ x hx
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h1 h2
      rw [h2.2.1, domainNumsetListAddIfLt] at hx
      rw [h1.2.1, domainNumsetListAddIfLt]
      rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact (hsub x hx).imp_left Or.inr
  | reads l =>
      intro n1 beg1 end1 live n2 beg2 end2 s nout1 begout1 endout1 nout2 begout2 endout2
        ⟨h1, h2, hsub⟩ x hx
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h1 h2
      rw [h2.2.1, RegAlloc.domainNumsetListDelete] at hx
      rw [h1.2.1, RegAlloc.domainNumsetListDelete]
      exact (hsub x hx.1).imp_left (fun h => ⟨h, hx.2⟩)
  | branch lt1 lt2 ih1 ih2 =>
      intro n1 beg1 end1 live n2 beg2 end2 s nout1 begout1 endout1 nout2 begout2 endout2
        ⟨h1, h2, hsub⟩ x hx
      obtain ⟨m2, b2, e2, b1, g2, g1, rfl⟩ := getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h1
      obtain ⟨m2', b2', e2', b1', w2, w1, rfl⟩ :=
        getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h2
      have s2 := ih2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2, hsub⟩
      have sd : ∀ x, sptDomain (sptDifference b2' live) x →
          sptDomain (sptDifference b2 live) x ∨ sptDomain s x := by
        intro x hx
        rw [sptDomainDifference] at hx ⊢
        exact (s2 x hx.1).imp_left (fun h => ⟨h, hx.2⟩)
      have s1 := ih1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨g1, w1, sd⟩
      rw [sptDomainDifference] at hx ⊢
      exact (s1 x hx.1).imp_left (fun h => ⟨h, hx.2⟩)
  | seq lt1 lt2 ih1 ih2 =>
      intro n1 beg1 end1 live n2 beg2 end2 s nout1 begout1 endout1 nout2 begout2 endout2
        ⟨h1, h2, hsub⟩
      obtain ⟨m2, b2, e2, g2, g1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h1
      obtain ⟨m2', b2', e2', w2, w1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h2
      exact ih1 _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ⟨g1, w1, ih2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2, hsub⟩⟩

/-- Exact HOL `get_intervals_withlive_live_tree_registers_subset_endout`
(`linear_scanProofScript.sml:1440-1471`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_live_tree_registers_subset_endout"]
theorem getIntervalsWithliveLiveTreeRegistersSubsetEndout :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (live_in : NumSet)
      (n_out : Int) (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervalsWithlive lt n_in beg_in end_in live_in →
      ∀ x, sptDomain end_in x ∨ liveTreeRegisters lt x → sptDomain end_out x := by
  intro lt
  induction lt with
  | writes l | reads l =>
      intro n_in beg_in end_in live_in n_out beg_out end_out h x hx
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      rw [h.2.2, domainNumsetListAddIfGt]
      simp only [liveTreeRegisters] at hx
      exact hx.symm
  | branch lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in live_in n_out beg_out end_out h x hx
      obtain ⟨n2, b2, e2, b1, h2, h1, -⟩ := getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h
      simp only [liveTreeRegisters] at hx
      refine ih1 _ _ _ _ _ _ _ h1 x ?_
      rcases hx with hx | hx | hx
      · exact Or.inl (ih2 _ _ _ _ _ _ _ h2 x (Or.inl hx))
      · exact Or.inr hx
      · exact Or.inl (ih2 _ _ _ _ _ _ _ h2 x (Or.inr hx))
  | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in live_in n_out beg_out end_out h x hx
      obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h
      simp only [liveTreeRegisters] at hx
      refine ih1 _ _ _ _ _ _ _ h1 x ?_
      rcases hx with hx | hx | hx
      · exact Or.inl (ih2 _ _ _ _ _ _ _ h2 x (Or.inl hx))
      · exact Or.inr hx
      · exact Or.inl (ih2 _ _ _ _ _ _ _ h2 x (Or.inr hx))

/-- Exact HOL `get_intervals_withlive_beg_subset_get_intervals_beg`
(`linear_scanProofScript.sml:1286-1324`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_beg_subset_get_intervals_beg"]
theorem getIntervalsWithliveBegSubsetGetIntervalsBeg :
    ∀ (lt : LiveTree) (n : Int) (beg_in1 beg_in2 end_ : Spt Int) (n1 : Int)
      (beg_out1 end1 : Spt Int) (n2 : Int) (beg_out2 end2 : Spt Int) (live : NumSet),
      (n1, beg_out1, end1) = getIntervalsWithlive lt n beg_in1 end_ live ∧
      (n2, beg_out2, end2) = getIntervals lt n beg_in2 end_ ∧
      (∀ x, sptDomain beg_in1 x → sptDomain beg_in2 x) →
      ∀ x, sptDomain beg_out1 x → sptDomain beg_out2 x := by
  intro lt
  induction lt with
  | writes l =>
      intro n beg_in1 beg_in2 end_ n1 beg_out1 end1 n2 beg_out2 end2 live ⟨h1, h2, hs⟩ x hx
      simp only [getIntervals, getIntervalsWithlive, Prod.mk.injEq] at h1 h2
      rw [h1.2.1, domainNumsetListAddIfLt] at hx
      rw [h2.2.1, domainNumsetListAddIfLt]
      exact hx.imp_right (hs x)
  | reads l =>
      intro n beg_in1 beg_in2 end_ n1 beg_out1 end1 n2 beg_out2 end2 live ⟨h1, h2, hs⟩ x hx
      simp only [getIntervals, getIntervalsWithlive, Prod.mk.injEq] at h1 h2
      rw [h1.2.1, RegAlloc.domainNumsetListDelete] at hx
      rw [h2.2.1]
      exact hs x hx.1
  | branch lt1 lt2 ih1 ih2 =>
      intro n beg_in1 beg_in2 end_ n1 beg_out1 end1 n2 beg_out2 end2 live ⟨h1, h2, hs⟩ x hx
      obtain ⟨m2, b2, e2, b1, w2, w1, rfl⟩ := getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h1
      obtain ⟨m2', b2', e2', g2, g1⟩ := getIntervalsBranch lt1 lt2 _ _ _ _ _ _ h2
      have hn := getIntervalsWithliveNEqGetIntervalsN lt2 _ _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      have he := getIntervalsWithliveEndEqGetIntervalsEnd lt2 _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      subst hn; subst he
      have s2 := ih2 _ _ _ _ _ _ _ _ _ _ _ ⟨w2, g2, hs⟩
      have sd : ∀ x, sptDomain (sptDifference b2 live) x → sptDomain b2' x := by
        intro x hx; rw [sptDomainDifference] at hx; exact s2 x hx.1
      rw [sptDomainDifference] at hx
      exact ih1 _ _ _ _ _ _ _ _ _ _ _ ⟨w1, g1, sd⟩ x hx.1
  | seq lt1 lt2 ih1 ih2 =>
      intro n beg_in1 beg_in2 end_ n1 beg_out1 end1 n2 beg_out2 end2 live ⟨h1, h2, hs⟩
      obtain ⟨m2, b2, e2, w2, w1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h1
      obtain ⟨m2', b2', e2', g2, g1⟩ := getIntervalsSeq lt1 lt2 _ _ _ _ _ _ h2
      have hn := getIntervalsWithliveNEqGetIntervalsN lt2 _ _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      have he := getIntervalsWithliveEndEqGetIntervalsEnd lt2 _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      subst hn; subst he
      exact ih1 _ _ _ _ _ _ _ _ _ _ _ ⟨w1, g1, ih2 _ _ _ _ _ _ _ _ _ _ _ ⟨w2, g2, hs⟩⟩

/-- Two `get_intervals_withlive` runs that differ only in their starting
interval beginnings produce the same ends (Flapjack consequence of
`get_intervals_withlive_end_eq_get_intervals_end`, used for the HOL proof's
auxiliary run). -/
private theorem getIntervalsWithliveEndIndep (lt : LiveTree) (n : Int) (b b' e : Spt Int)
    (live : NumSet) (n1 : Int) (b1 e1 : Spt Int) (n1' : Int) (b1' e1' : Spt Int)
    (h : (n1, b1, e1) = getIntervalsWithlive lt n b e live)
    (h' : (n1', b1', e1') = getIntervalsWithlive lt n b' e live) : e1 = e1' := by
  rcases hg : getIntervals lt n .ln e with ⟨m, bm, em⟩
  have a := getIntervalsWithliveEndEqGetIntervalsEnd lt n .ln b e m bm em n1 b1 e1 live
    ⟨hg.symm, h⟩
  have a' := getIntervalsWithliveEndEqGetIntervalsEnd lt n .ln b' e m bm em n1' b1' e1' live
    ⟨hg.symm, h'⟩
  rw [← a, ← a']

/-- Exact HOL `get_intervals_withlive_registers_subset_beg`
(`linear_scanProofScript.sml:1379-1438`). The HOL proof's auxiliary interval
map `map (K 0) (get_live_backward lt' live_in)` is any `int num_map` with that
domain; here it is built with `fromAList`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_registers_subset_beg"]
theorem getIntervalsWithliveRegistersSubsetBeg :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int) (live_in : NumSet),
      (∀ x, sptDomain end_in x → sptDomain beg_in x ∨ sptDomain live_in x) ∧
      (n_out, beg_out, end_out) = getIntervalsWithlive lt n_in beg_in end_in live_in →
      ∀ x, sptDomain end_out x →
        sptDomain beg_out x ∨ sptDomain (getLiveBackward lt live_in) x := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in n_out beg_out end_out live_in ⟨hs, h⟩ x hx
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      rw [h.2.2, domainNumsetListAddIfGt] at hx
      rw [h.2.1, domainNumsetListAddIfLt]
      simp only [getLiveBackward]
      rw [RegAlloc.domainNumsetListDelete]
      by_cases hm : x ∈ l
      · exact Or.inl (Or.inl hm)
      · rcases hx with hx | hx
        · exact absurd hx hm
        · rcases hs x hx with hb | hl
          · exact Or.inl (Or.inr hb)
          · exact Or.inr ⟨hl, hm⟩
  | reads l =>
      intro n_in beg_in end_in n_out beg_out end_out live_in ⟨hs, h⟩ x hx
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      rw [h.2.2, domainNumsetListAddIfGt] at hx
      rw [h.2.1, RegAlloc.domainNumsetListDelete]
      simp only [getLiveBackward]
      rw [domainNumsetListInsert]
      by_cases hm : x ∈ l
      · exact Or.inr (Or.inl hm)
      · rcases hx with hx | hx
        · exact absurd hx hm
        · rcases hs x hx with hb | hl
          · exact Or.inl ⟨hb, hm⟩
          · exact Or.inr (Or.inr hl)
  | branch lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out live_in ⟨hs, h⟩ x hx
      obtain ⟨n2, b2, e2, b1, h2, h1, rfl⟩ := getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h
      have s2 := ih2 _ _ _ _ _ _ _ ⟨hs, h2⟩
      -- An `int num_map` with the domain of `get_live_backward lt2 live_in`.
      let typed : Spt Int :=
        sptFromAList ((sptToAList (getLiveBackward lt2 live_in)).map (fun p => (p.1, (0 : Int))))
      have htyped : ∀ y, sptDomain typed y ↔ sptDomain (getLiveBackward lt2 live_in) y := by
        intro y
        show sptDomain (sptFromAList _) y ↔ _
        rw [sptDomainFromAList, List.map_map]
        exact sptMemMapFstToAList _ y
      let beg' := sptUnion (sptDifference b2 live_in) typed
      rcases hw : getIntervalsWithlive lt1 n2 beg' e2 live_in with ⟨n1', b1', e1'⟩
      have hsub : ∀ y, sptDomain e2 y → sptDomain beg' y ∨ sptDomain live_in y := by
        intro y hy
        show sptDomain (sptUnion _ _) y ∨ _
        rw [sptDomain_sptUnion, sptDomainDifference]
        rcases s2 y hy with hb | hl
        · by_cases hli : sptDomain live_in y
          · exact Or.inr hli
          · exact Or.inl (Or.inl ⟨hb, hli⟩)
        · exact Or.inl (Or.inr ((htyped y).mpr hl))
      have s1 := ih1 _ _ _ _ _ _ _ ⟨hsub, hw.symm⟩
      have hend := getIntervalsWithliveEndIndep lt1 _ _ _ _ _ _ _ _ _ _ _ h1 hw.symm
      subst hend
      have lip := getIntervalsWithliveBegLipschitz lt1 n2 (sptDifference b2 live_in) e2 live_in
        n2 beg' e2 typed _ _ _ _ _ _ ⟨h1, hw.symm, by
          intro y hy
          show _ ∨ _
          change sptDomain (sptUnion _ _) y at hy
          rw [sptDomain_sptUnion] at hy
          exact hy⟩
      simp only [getLiveBackward]
      rw [domainNumsetListInsert, sptDomainDifference, sptDomain_sptUnion]
      have hU : ∀ y, sptDomain (getLiveBackward lt1 live_in) y ∨
          sptDomain (getLiveBackward lt2 live_in) y →
          (y ∈ (sptToAList (sptDifference (getLiveBackward lt2 live_in)
            (getLiveBackward lt1 live_in))).map Prod.fst ∨
            sptDomain (getLiveBackward lt1 live_in) y) :=
        fun y hy => (branchDomainIff _ _ y).mpr hy
      rcases s1 x hx with hb | hl
      · rcases lip x hb with hb | ht
        · by_cases hu : sptDomain (getLiveBackward lt1 live_in) x ∨
              sptDomain (getLiveBackward lt2 live_in) x
          · exact Or.inr (hU x hu)
          · exact Or.inl ⟨hb, hu⟩
        · exact Or.inr (hU x (Or.inr ((htyped x).mp ht)))
      · exact Or.inr (hU x (Or.inl hl))
  | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out live_in ⟨hs, h⟩
      obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h
      exact ih1 _ _ _ _ _ _ _ ⟨ih2 _ _ _ _ _ _ _ ⟨hs, h2⟩, h1⟩

/-- Exact HOL `get_intervals_end_increase` (`linear_scanProofScript.sml:1546-1563`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_end_increase"]
theorem getIntervalsEndIncrease :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in →
      ∀ x, sptDomain end_in x → sptDomain end_out x := by
  intro lt n_in beg_in end_in n_out beg_out end_out h x hx
  unfold sptDomain at hx ⊢
  cases hl : sptLookup x end_in with
  | none => rw [hl] at hx; cases hx
  | some v =>
      obtain ⟨v', hv', -⟩ := getIntervalsIntendAugment lt _ _ _ _ _ _ h x v hl
      rw [hv']; rfl

/-- Exact HOL `get_intervals_intbeg_reduce` (`linear_scanProofScript.sml:1646-1692`);
HOL's unused binder `live` is retained. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_intbeg_reduce"]
theorem getIntervalsIntbegReduce :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int) (_live : NumSet),
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in ∧
      (∀ r v, sptLookup r beg_in = some v → n_in ≤ v) →
      (∀ r, (sptLookup r beg_out).elim n_out (fun x => x) ≤
        (sptLookup r beg_in).elim n_in (fun x => x)) ∧
      (∀ r v, sptLookup r beg_out = some v → n_out ≤ v) := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in n_out beg_out end_out _ ⟨h, hb⟩
      simp only [getIntervals, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      constructor
      · intro r
        rw [lookupNumsetListAddIfLt]
        split
        · cases hl : sptLookup r beg_in with
          | some vr =>
              have := hb r vr hl
              by_cases hv : n_in ≤ vr <;> simp [hv] <;> omega
          | none => simp
        · cases hl : sptLookup r beg_in with
          | some vr => simp
          | none => simp; omega
      · intro r v hv
        rw [lookupNumsetListAddIfLt] at hv
        split at hv
        · cases hl : sptLookup r beg_in with
          | some vr =>
              have := hb r vr hl
              rw [hl] at hv
              by_cases hc : n_in ≤ vr <;> simp [hc] at hv <;> omega
          | none => rw [hl] at hv; simp at hv; omega
        · have := hb r v hv; omega
  | reads l =>
      intro n_in beg_in end_in n_out beg_out end_out _ ⟨h, hb⟩
      simp only [getIntervals, Prod.mk.injEq] at h
      obtain ⟨h1, h2, -⟩ := h
      rw [h1, h2]
      constructor
      · intro r
        cases hl : sptLookup r beg_in with
        | some vr => simp
        | none => simp; omega
      · intro r v hv
        have := hb r v hv; omega
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out live ⟨h, hb⟩
      first
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsBranch lt1 lt2 _ _ _ _ _ _ h
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsSeq lt1 lt2 _ _ _ _ _ _ h
      obtain ⟨r2, v2⟩ := ih2 _ _ _ _ _ _ live ⟨h2, hb⟩
      obtain ⟨r1, v1⟩ := ih1 _ _ _ _ _ _ live ⟨h1, v2⟩
      exact ⟨fun r => Int.le_trans (r1 r) (r2 r), v1⟩

/-- Exact HOL `check_startlive_prop_monotone` (`linear_scanProofScript.sml:1694-1709`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_startlive_prop_monotone"]
theorem checkStartlivePropMonotone :
    ∀ (lt : LiveTree) (beg : Spt Int) (ndef : Int) (end_ beg' : Spt Int) (ndef' : Int)
      (end' : Spt Int) (n_in : Int),
      (∀ r, (sptLookup r beg').elim ndef' (fun x => x) ≤
        (sptLookup r beg).elim ndef (fun x => x)) ∧
      (∀ r v, sptLookup r end_ = some v → ∃ v', sptLookup r end' = some v' ∧ v ≤ v') ∧
      checkStartliveProp lt n_in beg end_ ndef →
      checkStartliveProp lt n_in beg' end' ndef' := by
  intro lt
  induction lt with
  | writes l =>
      intro beg ndef end_ beg' ndef' end' n_in ⟨hb, he, h⟩ r hr
      obtain ⟨h1, v, hv, hle⟩ := h r hr
      obtain ⟨v', hv', hle'⟩ := he r v hv
      refine ⟨?_, v', hv', Int.le_trans hle hle'⟩
      have hb' := hb r
      revert h1 hb'
      cases sptLookup r beg <;> cases sptLookup r beg' <;> simp <;> omega
  | reads l => intro _ _ _ _ _ _ _ _; trivial
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro beg ndef end_ beg' ndef' end' n_in ⟨hb, he, h⟩
      exact ⟨ih1 _ _ _ _ _ _ _ ⟨hb, he, h.1⟩, ih2 _ _ _ _ _ _ _ ⟨hb, he, h.2⟩⟩

/-- Exact HOL `check_startlive_prop_augment_ndef`
(`linear_scanProofScript.sml:1711-1735`); the free `ndef'` is quantified first. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_startlive_prop_augment_ndef"]
theorem checkStartlivePropAugmentNdef :
    ∀ (ndef' : Int) (lt : LiveTree) (n_in : Int) (beg_out end_out : Spt Int) (ndef : Int),
      checkStartliveProp lt n_in beg_out end_out ndef ∧ ndef ≤ ndef' ∧
        ndef' ≤ n_in - sizeOfLiveTree lt →
      checkStartliveProp lt n_in beg_out end_out ndef' := by
  intro ndef' lt
  induction lt with
  | writes l =>
      intro n_in beg_out end_out ndef ⟨h, h1, h2⟩ r hr
      obtain ⟨hb, hv⟩ := h r hr
      refine ⟨?_, hv⟩
      simp only [sizeOfLiveTree] at h2
      cases hl : sptLookup r beg_out with
      | none => simp only [hl] at hb ⊢; omega
      | some x => simp only [hl] at hb ⊢; exact hb
  | reads l => intro _ _ _ _ _; trivial
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_out end_out ndef ⟨h, h1, h2⟩
      have p1 := sizeOfLiveTreePositive lt1
      have p2 := sizeOfLiveTreePositive lt2
      simp only [sizeOfLiveTree] at h2
      exact ⟨ih1 _ _ _ _ ⟨h.1, h1, by omega⟩, ih2 _ _ _ _ ⟨h.2, h1, by omega⟩⟩

/-- Exact HOL `get_intervals_check_startlive_prop`
(`linear_scanProofScript.sml:1737-1765`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_check_startlive_prop"]
theorem getIntervalsCheckStartliveProp :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in ∧
      (∀ r v, sptLookup r beg_in = some v → n_in ≤ v) →
      checkStartliveProp lt n_in beg_out end_out n_out := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in n_out beg_out end_out ⟨h, hb⟩ r hr
      simp only [getIntervals, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · rw [lookupNumsetListAddIfLt, if_pos hr]
        cases hl : sptLookup r beg_in with
        | some vr =>
            by_cases hc : n_in ≤ vr <;> simp [hc] <;> omega
        | none => simp
      · rw [lookupNumsetListAddIfGt, if_pos hr]
        cases hl : sptLookup r end_in with
        | some vr =>
            by_cases hc : vr ≤ n_in
            · exact ⟨n_in, by simp [hc], Int.le_refl _⟩
            · exact ⟨vr, by simp [hc], by omega⟩
        | none => exact ⟨n_in, rfl, Int.le_refl _⟩
  | reads l => intro _ _ _ _ _ _ _; trivial
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out ⟨h, hb⟩
      first
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsBranch lt1 lt2 _ _ _ _ _ _ h
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsSeq lt1 lt2 _ _ _ _ _ _ h
      have c2 := ih2 _ _ _ _ _ _ ⟨h2, hb⟩
      have v2 := (getIntervalsIntbegReduce lt2 _ _ _ _ _ _ .ln ⟨h2, hb⟩).2
      have c1 := ih1 _ _ _ _ _ _ ⟨h1, v2⟩
      have hred := (getIntervalsIntbegReduce lt1 _ _ _ _ _ _ .ln ⟨h1, v2⟩).1
      have haug := getIntervalsIntendAugment lt1 _ _ _ _ _ _ h1
      have hn2 := getIntervalsNout lt2 _ _ _ _ _ _ h2
      refine ⟨?_, checkStartlivePropMonotone lt2 _ _ _ _ _ _ _ ⟨hred, haug, c2⟩⟩
      rw [← hn2]
      exact c1

/-- Exact HOL `get_intervals_withlive_beg_less_live`
(`linear_scanProofScript.sml:1061-1192`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_beg_less_live"]
theorem getIntervalsWithliveBegLessLive :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (live_in : NumSet)
      (n_out : Int) (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervalsWithlive lt n_in beg_in end_in live_in ∧
      (∀ r v, sptLookup r beg_in = some v → n_in ≤ v) ∧
      (∀ r, sptDomain live_in r → ¬ sptDomain beg_in r) →
      checkNumberPropertyStrong (fun n (live : NumSet) => ∀ r, sptDomain live r →
        (sptLookup r beg_out).elim n_out (fun x => x) ≤ n) lt n_in live_in := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, _, hd⟩
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      intro r hr
      rw [RegAlloc.domainNumsetListDelete] at hr
      have hn : sptLookup r beg_in = none := by
        have := hd r hr.1
        unfold sptDomain at this
        cases hl : sptLookup r beg_in with
        | none => rfl
        | some _ => rw [hl] at this; simp at this
      rw [lookupNumsetListAddIfLt, if_neg hr.2, hn]
      simp
  | reads l =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, _, hd⟩
      simp only [getIntervalsWithlive, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      intro r hr
      rw [domainNumsetListInsert] at hr
      rw [lookupNumsetListDelete]
      by_cases hm : r ∈ l
      · rw [if_pos hm]; simp
      · rw [if_neg hm]
        have := hd r (hr.resolve_left hm)
        unfold sptDomain at this
        cases hl : sptLookup r beg_in with
        | none => simp
        | some _ => rw [hl] at this; simp at this
  | branch lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, hb, hd⟩
      obtain ⟨n2, b2, e2, b1, h2, h1, rfl⟩ := getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h
      have k2 := getIntervalsWithliveNout lt2 _ _ _ _ _ _ _ h2
      have k1 := getIntervalsWithliveNout lt1 _ _ _ _ _ _ _ h1
      have p1 := sizeOfLiveTreePositive lt1
      have p2 := sizeOfLiveTreePositive lt2
      have c2 := ih2 _ _ _ _ _ _ _ ⟨h2, hb, hd⟩
      have v2 := getIntervalsWithliveIntbegNout lt2 _ _ _ _ _ _ _ ⟨h2, hb⟩
      have vd : ∀ r v, sptLookup r (sptDifference b2 live_in) = some v → n2 ≤ v := by
        intro r v hv
        rw [lookupDifferenceEq] at hv
        split at hv
        · exact v2 r v hv
        · cases hv
      have dd : ∀ r, sptDomain live_in r → ¬ sptDomain (sptDifference b2 live_in) r := by
        intro r hr
        rw [sptDomainDifference]
        exact fun h => h.2 hr
      have c1 := ih1 _ _ _ _ _ _ _ ⟨h1, vd, dd⟩
      have red1 := (getIntervalsWithliveIntbegReduce lt1 _ _ _ _ _ _ _ ⟨h1, vd⟩).1
      let U := sptUnion (getLiveBackward lt1 live_in) (getLiveBackward lt2 live_in)
      -- `oc (difference b1 U) n_out r` is `n_out` on `U` and `oc b1 n_out r` elsewhere.
      have ocd : ∀ r, (sptLookup r (sptDifference b1 U)).elim n_out (fun x => x) =
          if sptLookup r U = none then (sptLookup r b1).elim n_out (fun x => x) else n_out := by
        intro r
        rw [lookupDifferenceEq]
        split <;> simp
      refine ⟨?_, ?_, ?_⟩
      · rw [show n_in - sizeOfLiveTree lt2 = n2 by omega]
        refine checkNumberPropertyStrongMonotone _ _ lt1 n2 live_in ⟨?_, c1⟩
        intro n' live' ⟨hn', hp⟩ r hr
        rw [ocd r]
        split
        · exact hp r hr
        · omega
      · refine checkNumberPropertyStrongMonotone _ _ lt2 _ live_in ⟨?_, c2⟩
        intro n' live' ⟨hn', hp⟩ r hr
        rw [ocd r]
        split
        · have e1 := red1 r
          have e2 := hp r hr
          rw [lookupDifferenceEq] at e1
          split at e1
          · exact Int.le_trans e1 e2
          · cases hl : sptLookup r b1 with
            | some v => rw [hl] at e1; simp at e1 ⊢; omega
            | none => simp; omega
        · omega
      · intro r hr
        rw [ocd r]
        have hU : sptLookup r U ≠ none := by
          have hm : sptDomain U r := by
            show sptDomain (sptUnion _ _) r
            rw [sptDomain_sptUnion]
            simp only [getLiveBackward] at hr
            rw [domainNumsetListInsert] at hr
            exact (branchDomainIff _ _ r).mp hr
          unfold sptDomain at hm
          cases hl : sptLookup r U with
          | none => rw [hl] at hm; simp at hm
          | some _ => simp
        rw [if_neg hU]
        simp only [sizeOfLiveTree]
        omega
  | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, hb, hd⟩
      obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h
      have k2 := getIntervalsWithliveNout lt2 _ _ _ _ _ _ _ h2
      have c2 := ih2 _ _ _ _ _ _ _ ⟨h2, hb, hd⟩
      have v2 := getIntervalsWithliveIntbegNout lt2 _ _ _ _ _ _ _ ⟨h2, hb⟩
      have d2 := getIntervalsWithliveLiveIntbeg lt2 _ _ _ _ _ _ _ ⟨h2, hd⟩
      have c1 := ih1 _ _ _ _ _ _ _ ⟨h1, v2, d2⟩
      have red1 := (getIntervalsWithliveIntbegReduce lt1 _ _ _ _ _ _ _ ⟨h1, v2⟩).1
      refine ⟨?_, ?_⟩
      · rw [show n_in - sizeOfLiveTree lt2 = n2 by omega]; exact c1
      · refine checkNumberPropertyStrongMonotone _ _ lt2 _ live_in ⟨?_, c2⟩
        intro n' live' ⟨_, hp⟩ r hr
        exact Int.le_trans (red1 r) (hp r hr)

/-- Exact HOL `get_intervals_withlive_beg_eq_get_intervals_beg_when_some`
(`linear_scanProofScript.sml:1219-1284`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_beg_eq_get_intervals_beg_when_some"]
theorem getIntervalsWithliveBegEqGetIntervalsBegWhenSome :
    ∀ (lt : LiveTree) (n : Int) (beg beg' end_ : Spt Int) (n1 : Int) (beg1 end1 : Spt Int)
      (n2 : Int) (beg2 end2 : Spt Int) (live : NumSet),
      (n1, beg1, end1) = getIntervals lt n beg end_ ∧
      (n2, beg2, end2) = getIntervalsWithlive lt n beg' end_ live ∧
      (∀ r v, sptLookup r beg = some v → n ≤ v) ∧
      (∀ r v, sptLookup r beg' = some v → n ≤ v) ∧
      (∀ r v1 v2, sptLookup r beg = some v1 ∧ sptLookup r beg' = some v2 → v1 = v2) →
      ∀ r v1 v2, sptLookup r beg1 = some v1 ∧ sptLookup r beg2 = some v2 → v1 = v2 := by
  intro lt
  induction lt with
  | writes l =>
      intro n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live ⟨h1, h2, hb, hb', he⟩ r v1 v2 ⟨l1, l2⟩
      simp only [getIntervals, getIntervalsWithlive, Prod.mk.injEq] at h1 h2
      rw [h1.2.1, lookupNumsetListAddIfLt] at l1
      rw [h2.2.1, lookupNumsetListAddIfLt] at l2
      by_cases hm : r ∈ l
      · rw [if_pos hm] at l1 l2
        have a1 : v1 = n := by
          cases hl : sptLookup r beg with
          | some vr =>
              have := hb r vr hl
              rw [hl] at l1; simp [show n ≤ vr from this] at l1; omega
          | none => rw [hl] at l1; simp at l1; omega
        have a2 : v2 = n := by
          cases hl : sptLookup r beg' with
          | some vr =>
              have := hb' r vr hl
              rw [hl] at l2; simp [show n ≤ vr from this] at l2; omega
          | none => rw [hl] at l2; simp at l2; omega
        rw [a1, a2]
      · rw [if_neg hm] at l1 l2
        exact he r v1 v2 ⟨l1, l2⟩
  | reads l =>
      intro n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live ⟨h1, h2, _, _, he⟩ r v1 v2 ⟨l1, l2⟩
      simp only [getIntervals, getIntervalsWithlive, Prod.mk.injEq] at h1 h2
      rw [h1.2.1] at l1
      rw [h2.2.1, lookupNumsetListDelete] at l2
      split at l2
      · cases l2
      · exact he r v1 v2 ⟨l1, l2⟩
  | branch lt1 lt2 ih1 ih2 =>
      intro n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live ⟨h1, h2, hb, hb', he⟩ r v1 v2 ⟨l1, l2⟩
      obtain ⟨m2, b2, e2, g2, g1⟩ := getIntervalsBranch lt1 lt2 _ _ _ _ _ _ h1
      obtain ⟨m2', b2', e2', b1', w2, w1, rfl⟩ :=
        getIntervalsWithliveBranch lt1 lt2 _ _ _ _ _ _ _ h2
      have hn := getIntervalsWithliveNEqGetIntervalsN lt2 _ _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      have hend := getIntervalsWithliveEndEqGetIntervalsEnd lt2 _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      subst hn; subst hend
      have vb := getIntervalsIntbegNout lt2 _ _ _ _ _ _ ⟨g2, hb⟩
      have vb' := getIntervalsWithliveIntbegNout lt2 _ _ _ _ _ _ _ ⟨w2, hb'⟩
      have e2' := ih2 _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2, hb, hb', he⟩
      have vd : ∀ r v, sptLookup r (sptDifference b2' live) = some v → m2 ≤ v := by
        intro r v hv
        rw [lookupDifferenceEq] at hv
        split at hv
        · exact vb' r v hv
        · cases hv
      have ed : ∀ r v1 v2, sptLookup r b2 = some v1 ∧
          sptLookup r (sptDifference b2' live) = some v2 → v1 = v2 := by
        intro r v1 v2 ⟨a, b⟩
        rw [lookupDifferenceEq] at b
        split at b
        · exact e2' r v1 v2 ⟨a, b⟩
        · cases b
      have e1' := ih1 _ _ _ _ _ _ _ _ _ _ _ ⟨g1, w1, vb, vd, ed⟩
      rw [lookupDifferenceEq] at l2
      split at l2
      · exact e1' r v1 v2 ⟨l1, l2⟩
      · cases l2
  | seq lt1 lt2 ih1 ih2 =>
      intro n beg beg' end_ n1 beg1 end1 n2 beg2 end2 live ⟨h1, h2, hb, hb', he⟩
      obtain ⟨m2, b2, e2, g2, g1⟩ := getIntervalsSeq lt1 lt2 _ _ _ _ _ _ h1
      obtain ⟨m2', b2', e2', w2, w1⟩ := getIntervalsWithliveSeq lt1 lt2 _ _ _ _ _ _ _ h2
      have hn := getIntervalsWithliveNEqGetIntervalsN lt2 _ _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      have hend := getIntervalsWithliveEndEqGetIntervalsEnd lt2 _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2⟩
      subst hn; subst hend
      have vb := getIntervalsIntbegNout lt2 _ _ _ _ _ _ ⟨g2, hb⟩
      have vb' := getIntervalsWithliveIntbegNout lt2 _ _ _ _ _ _ _ ⟨w2, hb'⟩
      have e2' := ih2 _ _ _ _ _ _ _ _ _ _ _ ⟨g2, w2, hb, hb', he⟩
      exact ih1 _ _ _ _ _ _ _ _ _ _ _ ⟨g1, w1, vb, vb', e2'⟩

private theorem sptDomainLn {α : Type} (x : Nat) : ¬ sptDomain (Spt.ln : Spt α) x := by
  simp [sptDomain, sptLookup]

/-- Exact HOL `get_intervals_domain_eq_live_tree_registers`
(`linear_scanProofScript.sml:1473-1497`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_domain_eq_live_tree_registers"]
theorem getIntervalsDomainEqLiveTreeRegisters :
    ∀ (lt : LiveTree) (n : Int) (beg end_ : Spt Int),
      (n, beg, end_) = getIntervals (fixDomination lt) 0 .ln .ln →
      sptDomain beg = liveTreeRegisters (fixDomination lt) ∧
      sptDomain end_ = liveTreeRegisters (fixDomination lt) := by
  intro lt n beg end_ h
  have hfd := fixDominationFixesDomination lt
  rcases hw : getIntervalsWithlive (fixDomination lt) 0 .ln .ln .ln with ⟨n', beg', end'⟩
  have hend : end_ = end' :=
    getIntervalsWithliveEndEqGetIntervalsEnd _ _ _ _ _ _ _ _ _ _ _ _ ⟨h, hw.symm⟩
  have a := getIntervalsWithliveLiveTreeRegistersSubsetEndout _ _ _ _ _ _ _ _ hw.symm
  have b := getIntervalsWithliveRegistersSubsetBeg _ _ _ _ _ _ _ _
    ⟨fun x hx => absurd hx (sptDomainLn x), hw.symm⟩
  have c := getIntervalsWithliveBegSubsetGetIntervalsBeg _ _ _ _ _ _ _ _ _ _ _ _
    ⟨hw.symm, h, fun x hx => hx⟩
  have d := getIntervalsBegSubsetRegisters _ _ _ _ _ _ _ h
  have eb : ∀ x, sptDomain end' x → sptDomain beg x := by
    intro x hx
    rcases b x hx with hx | hx
    · exact c x hx
    · rw [hfd] at hx; exact hx.elim
  have br : ∀ x, sptDomain beg x → liveTreeRegisters (fixDomination lt) x := by
    intro x hx
    rcases d x hx with hx | hx
    · exact absurd hx (sptDomainLn x)
    · exact hx
  have re : ∀ x, liveTreeRegisters (fixDomination lt) x → sptDomain end' x :=
    fun x hx => a x (Or.inr hx)
  rw [hend]
  constructor
  · funext x; exact propext ⟨br x, fun hx => eb x (re x hx)⟩
  · funext x; exact propext ⟨fun hx => br x (eb x hx), re x⟩

/-- Exact HOL `get_intervals_withlive_domain_eq_live_tree_registers`
(`linear_scanProofScript.sml:1499-1523`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_domain_eq_live_tree_registers"]
theorem getIntervalsWithliveDomainEqLiveTreeRegisters :
    ∀ (lt : LiveTree) (n : Int) (beg end_ : Spt Int),
      (n, beg, end_) = getIntervalsWithlive (fixDomination lt) 0 .ln .ln .ln →
      sptDomain beg = liveTreeRegisters (fixDomination lt) ∧
      sptDomain end_ = liveTreeRegisters (fixDomination lt) := by
  intro lt n beg end_ h
  have hfd := fixDominationFixesDomination lt
  rcases hg : getIntervals (fixDomination lt) 0 .ln .ln with ⟨n', beg', end'⟩
  have a := getIntervalsWithliveLiveTreeRegistersSubsetEndout _ _ _ _ _ _ _ _ h
  have b := getIntervalsWithliveRegistersSubsetBeg _ _ _ _ _ _ _ _
    ⟨fun x hx => absurd hx (sptDomainLn x), h⟩
  have c := getIntervalsWithliveBegSubsetGetIntervalsBeg _ _ _ _ _ _ _ _ _ _ _ _
    ⟨h, hg.symm, fun x hx => hx⟩
  have d := getIntervalsBegSubsetRegisters _ _ _ _ _ _ _ hg.symm
  have br : ∀ x, sptDomain beg x → liveTreeRegisters (fixDomination lt) x := by
    intro x hx
    rcases d x (c x hx) with hx | hx
    · exact absurd hx (sptDomainLn x)
    · exact hx
  have eb : ∀ x, sptDomain end_ x → sptDomain beg x := by
    intro x hx
    rcases b x hx with hx | hx
    · exact hx
    · rw [hfd] at hx; exact hx.elim
  have re : ∀ x, liveTreeRegisters (fixDomination lt) x → sptDomain end_ x :=
    fun x hx => a x (Or.inr hx)
  constructor
  · funext x; exact propext ⟨br x, fun hx => eb x (re x hx)⟩
  · funext x; exact propext ⟨fun hx => br x (eb x hx), re x⟩

/-- Exact HOL `get_intervals_withlive_beg_eq_get_intervals_beg`
(`linear_scanProofScript.sml:1525-1544`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_withlive_beg_eq_get_intervals_beg"]
theorem getIntervalsWithliveBegEqGetIntervalsBeg :
    ∀ (lt : LiveTree) (n : Int) (beg end_ : Spt Int) (n' : Int) (beg' end' : Spt Int),
      (n, beg, end_) = getIntervalsWithlive (fixDomination lt) 0 .ln .ln .ln ∧
      (n', beg', end') = getIntervals (fixDomination lt) 0 .ln .ln →
      ∀ (r : Nat), sptLookup r beg = sptLookup r beg' := by
  intro lt n beg end_ n' beg' end' ⟨h, h'⟩ r
  have d1 := (getIntervalsWithliveDomainEqLiveTreeRegisters lt _ _ _ h).1
  have d2 := (getIntervalsDomainEqLiveTreeRegisters lt _ _ _ h').1
  have hv := getIntervalsWithliveBegEqGetIntervalsBegWhenSome _ _ _ _ _ _ _ _ _ _ _ _
    ⟨h', h, by simp [sptLookup], by simp [sptLookup], by simp [sptLookup]⟩
  have hd := congrFun (d1.trans d2.symm) r
  unfold sptDomain at hd
  cases h1 : sptLookup r beg with
  | none =>
      cases h2 : sptLookup r beg' with
      | none => rfl
      | some _ => rw [h1, h2] at hd; simp at hd
  | some v1 =>
      cases h2 : sptLookup r beg' with
      | none => rw [h1, h2] at hd; simp at hd
      | some v2 => rw [hv r v2 v1 ⟨h2, h1⟩]

/-- Exact HOL `check_number_property_subset_endout`
(`linear_scanProofScript.sml:1565-1620`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "check_number_property_subset_endout"]
theorem checkNumberPropertySubsetEndout :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (live_in : NumSet)
      (n_out : Int) (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in ∧
      (∀ x, sptDomain live_in x → sptDomain end_in x) →
      checkNumberPropertyStrong (fun _n (live : NumSet) =>
        ∀ x, sptDomain live x → sptDomain end_out x) lt n_in live_in := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, hs⟩ x hx
      simp only [getIntervals, Prod.mk.injEq] at h
      rw [h.2.2, domainNumsetListAddIfGt]
      rw [RegAlloc.domainNumsetListDelete] at hx
      exact Or.inr (hs x hx.1)
  | reads l =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, hs⟩ x hx
      simp only [getIntervals, Prod.mk.injEq] at h
      rw [h.2.2, domainNumsetListAddIfGt]
      rw [domainNumsetListInsert] at hx
      exact hx.imp_right (hs x)
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in live_in n_out beg_out end_out ⟨h, hs⟩
      first
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsBranch lt1 lt2 _ _ _ _ _ _ h
        | obtain ⟨n2, b2, e2, h2, h1⟩ := getIntervalsSeq lt1 lt2 _ _ _ _ _ _ h
      have hn2 := getIntervalsNout lt2 _ _ _ _ _ _ h2
      have i2 := getIntervalsEndIncrease lt2 _ _ _ _ _ _ h2
      have i1 := getIntervalsEndIncrease lt1 _ _ _ _ _ _ h1
      have c2 := ih2 _ _ _ _ _ _ _ ⟨h2, hs⟩
      have c2' := checkNumberPropertyStrongMonotoneWeak _ (fun _n (live : NumSet) =>
        ∀ x, sptDomain live x → sptDomain end_out x) lt2 n_in live_in
        ⟨fun _ _ hp x hx => i1 x (hp x hx), c2⟩
      have e2 := checkNumberPropertyStrongEnd _ lt2 n_in live_in c2
      first
        | -- Branch
          have c1 := ih1 _ _ _ live_in _ _ _ ⟨h1, fun x hx => i2 x (hs x hx)⟩
          have e1 := checkNumberPropertyStrongEnd _ lt1 _ live_in c1
          refine ⟨by rw [← hn2]; exact c1, c2', ?_⟩
          intro x hx
          simp only [getLiveBackward] at hx
          rw [domainNumsetListInsert] at hx
          rcases (branchDomainIff _ _ x).mp hx with hx | hx
          · exact e1 x hx
          · exact i1 x (e2 x hx)
        | -- Seq
          have c1 := ih1 _ _ _ (getLiveBackward lt2 live_in) _ _ _ ⟨h1, e2⟩
          exact ⟨by rw [← hn2]; exact c1, c2'⟩

/-- Exact HOL `get_intervals_beg_less_live` (`linear_scanProofScript.sml:1622-1644`);
HOL's unused binder `live_in` is retained. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_beg_less_live"]
theorem getIntervalsBegLessLive :
    ∀ (lt : LiveTree) (_live_in : NumSet) (n_out : Int) (beg_out end_out : Spt Int),
      (n_out, beg_out, end_out) = getIntervals (fixDomination lt) 0 .ln .ln →
      checkNumberPropertyStrong (fun n (live : NumSet) => ∀ r, sptDomain live r →
        (sptLookup r beg_out).elim n_out (fun x => x) ≤ n) (fixDomination lt) 0 .ln := by
  intro lt _ n_out beg_out end_out h
  rcases hw : getIntervalsWithlive (fixDomination lt) 0 .ln .ln .ln with ⟨n', beg', end'⟩
  have c := getIntervalsWithliveBegLessLive _ _ _ _ _ _ _ _
    ⟨hw.symm, by simp [sptLookup], fun r _ => sptDomainLn r⟩
  have hb := getIntervalsWithliveBegEqGetIntervalsBeg lt _ _ _ _ _ _ ⟨hw.symm, h⟩
  have hn := getIntervalsWithliveNEqGetIntervalsN _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨h, hw.symm⟩
  subst hn
  refine checkNumberPropertyStrongMonotoneWeak _ _ _ _ _ ⟨?_, c⟩
  intro n live hp r hr
  rw [← hb r]
  exact hp r hr

end Flapjack.LinearScan
