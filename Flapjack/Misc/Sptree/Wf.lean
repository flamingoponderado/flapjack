import Flapjack.Misc.Sptree

namespace Flapjack

/-- Literal source nonempty result for insertion, without a well-formedness premise. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "insert_notEmpty"]
theorem sptInsertNotEmpty {α : Type} (key : Nat) (value : α) (tree : Spt α) :
    sptIsEmpty (sptInsert key value tree) = false := by
  cases tree <;> rw [sptInsert] <;> by_cases hz : key = 0 <;>
    by_cases hp : key % 2 = 0 <;> simp only [hz, hp, if_true, if_false, sptIsEmpty]

/-- Literal source insertion preserves well-formedness for every payload type. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_insert"]
theorem sptWfInsert {α : Type} : ∀ (key : Nat) (value : α) (tree : Spt α),
    sptWf tree = true → sptWf (sptInsert key value tree) = true := by
  intro key
  induction key using Nat.strongRecOn with
  | ind key ih =>
    intro value tree hw
    by_cases hz : key = 0
    · subst key
      cases tree <;> rw [sptInsert] <;> simp_all [sptWf]
    · have hlt : (key - 1) / 2 < key := by
        have := Nat.div_le_self (key - 1) 2
        omega
      have hrec := ih ((key - 1) / 2) hlt value
      have hnil := hrec .ln rfl
      cases tree <;> rw [sptInsert] <;> by_cases hp : key % 2 = 0 <;>
        simp_all [sptWf, sptInsertNotEmpty]

/-- Flapjack proof factoring for the collapsing constructor; no separate HOL
theorem is claimed. The source wf_delete proof unfolds this constructor. -/
private theorem wfMkBN {α : Type} (left right : Spt α)
    (hl : sptWf left = true) (hr : sptWf right = true) :
    sptWf (sptMkBN left right) = true := by
  cases left <;> cases right <;> simp_all [sptMkBN, sptWf, sptIsEmpty]

/-- Flapjack proof factoring for the collapsing value constructor, as above. -/
private theorem wfMkBS {α : Type} (left : Spt α) (value : α) (right : Spt α)
    (hl : sptWf left = true) (hr : sptWf right = true) :
    sptWf (sptMkBS left value right) = true := by
  cases left <;> cases right <;> simp_all [sptMkBS, sptWf, sptIsEmpty]

/-- Literal generic HOL deletion preservation with its sole wf premise. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_delete"]
theorem sptWfDelete {α : Type} : ∀ (tree : Spt α) (key : Nat),
    sptWf tree = true → sptWf (sptDelete key tree) = true := by
  intro tree
  induction tree with
  | ln => intro key hw; rfl
  | ls value =>
      intro key hw
      rw [sptDelete]
      split <;> rfl
  | bn left right ihl ihr =>
      intro key hw
      have hl : sptWf left = true := by simp_all [sptWf]
      have hr : sptWf right = true := by simp_all [sptWf]
      rw [sptDelete]
      split
      · exact hw
      · split
        · exact wfMkBN _ _ (ihl _ hl) hr
        · exact wfMkBN _ _ hl (ihr _ hr)
  | bs left value right ihl ihr =>
      intro key hw
      have hl : sptWf left = true := by simp_all [sptWf]
      have hr : sptWf right = true := by simp_all [sptWf]
      rw [sptDelete]
      split
      · simpa [sptWf] using hw
      · split
        · exact wfMkBS _ _ _ (ihl _ hl) hr
        · exact wfMkBS _ _ _ hl (ihr _ hr)

/-- `isEmpty` of a union (HOL's `isEmpty_union` rewrite, used by `wf_union`;
Flapjack infrastructure). -/
theorem sptIsEmpty_sptUnion {α : Type} (a b : Spt α) :
    sptIsEmpty (sptUnion a b) = (sptIsEmpty a && sptIsEmpty b) := by
  cases a <;> cases b <;> simp [sptUnion, sptIsEmpty]

/-- Exact HOL `wf_inter` (`HOL/src/finite_maps/sptreeScript.sml:353-358`):
intersection is well formed for arbitrary inputs. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_inter"]
theorem sptWfInter {α β : Type} : ∀ (m1 : Spt α) (m2 : Spt β), sptWf (sptInter m1 m2) = true := by
  intro m1
  induction m1 with
  | ln => intro m2; simp [sptInter]
  | ls a => intro m2; cases m2 <;> simp [sptInter, sptWf]
  | bn l r ihl ihr =>
      intro m2
      cases m2 with
      | ln => simp [sptInter]
      | ls b => simp [sptInter]
      | bn l' r' => simp only [sptInter]; exact wfMkBN _ _ (ihl l') (ihr r')
      | bs l' b r' => simp only [sptInter]; exact wfMkBN _ _ (ihl l') (ihr r')
  | bs l a r ihl ihr =>
      intro m2
      cases m2 with
      | ln => simp [sptInter]
      | ls b => simp [sptInter, sptWf]
      | bn l' r' => simp only [sptInter]; exact wfMkBN _ _ (ihl l') (ihr r')
      | bs l' b r' => simp only [sptInter]; exact wfMkBS _ _ _ (ihl l') (ihr r')

/-- Exact HOL `wf_union` (`HOL/src/finite_maps/sptreeScript.sml:247-253`). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_union"]
theorem sptWfUnion {α : Type} :
    ∀ (m1 m2 : Spt α), sptWf m1 = true ∧ sptWf m2 = true → sptWf (sptUnion m1 m2) = true := by
  intro m1
  induction m1 with
  | ln => intro m2 h; simpa [sptUnion] using h.2
  | ls a => intro m2 h; cases m2 <;> simp_all [sptUnion, sptWf]
  | bn l r ihl ihr =>
      intro m2 h
      cases m2 with
      | ln => simpa [sptUnion] using h.1
      | ls b => simp_all [sptUnion, sptWf]
      | bn l' r' =>
          simp only [sptUnion, sptWf, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
          refine ⟨⟨ihl l' ⟨h.1.1.1, h.2.1.1⟩, ihr r' ⟨h.1.1.2, h.2.1.2⟩⟩, ?_⟩
          rw [sptIsEmpty_sptUnion, sptIsEmpty_sptUnion]
          cases hl : sptIsEmpty l <;> cases hr : sptIsEmpty r <;> simp_all
      | bs l' b r' =>
          simp only [sptUnion, sptWf, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
          refine ⟨⟨ihl l' ⟨h.1.1.1, h.2.1.1⟩, ihr r' ⟨h.1.1.2, h.2.1.2⟩⟩, ?_⟩
          rw [sptIsEmpty_sptUnion, sptIsEmpty_sptUnion]
          cases hl : sptIsEmpty l <;> cases hr : sptIsEmpty r <;> simp_all
  | bs l a r ihl ihr =>
      intro m2 h
      cases m2 with
      | ln => simpa [sptUnion] using h.1
      | ls b => simp_all [sptUnion, sptWf]
      | bn l' r' =>
          simp only [sptUnion, sptWf, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
          refine ⟨⟨ihl l' ⟨h.1.1.1, h.2.1.1⟩, ihr r' ⟨h.1.1.2, h.2.1.2⟩⟩, ?_⟩
          rw [sptIsEmpty_sptUnion, sptIsEmpty_sptUnion]
          cases hl : sptIsEmpty l <;> cases hr : sptIsEmpty r <;> simp_all
      | bs l' b r' =>
          simp only [sptUnion, sptWf, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
          refine ⟨⟨ihl l' ⟨h.1.1.1, h.2.1.1⟩, ihr r' ⟨h.1.1.2, h.2.1.2⟩⟩, ?_⟩
          rw [sptIsEmpty_sptUnion, sptIsEmpty_sptUnion]
          cases hl : sptIsEmpty l <;> cases hr : sptIsEmpty r <;> simp_all

section KeyDecomposition

variable {α : Type}

/-- Key `2j+2` selects the left subtree (Flapjack infrastructure). -/
theorem sptLookup_left_bn (j : Nat) (l r : Spt α) :
    sptLookup (2 * j + 2) (.bn l r) = sptLookup j l := by
  rw [sptLookup, if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem sptLookup_right_bn (j : Nat) (l r : Spt α) :
    sptLookup (2 * j + 1) (.bn l r) = sptLookup j r := by
  rw [sptLookup, if_neg (by omega), if_neg (by omega)]
  congr 1; omega

theorem sptLookup_left_bs (j : Nat) (l : Spt α) (a : α) (r : Spt α) :
    sptLookup (2 * j + 2) (.bs l a r) = sptLookup j l := by
  rw [sptLookup, if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem sptLookup_right_bs (j : Nat) (l : Spt α) (a : α) (r : Spt α) :
    sptLookup (2 * j + 1) (.bs l a r) = sptLookup j r := by
  rw [sptLookup, if_neg (by omega), if_neg (by omega)]
  congr 1; omega

/-- A well-formed nonempty tree has a key (Flapjack infrastructure). -/
theorem sptWf_exists_key : ∀ (t : Spt α), sptWf t = true → sptIsEmpty t = false →
    ∃ k v, sptLookup k t = some v
  | .ln, _, h => by simp at h
  | .ls a, _, _ => ⟨0, a, by simp [sptLookup]⟩
  | .bs _ a _, _, _ => ⟨0, a, by simp [sptLookup]⟩
  | .bn l r, hw, _ => by
      simp only [sptWf, Bool.and_eq_true, Bool.not_eq_true'] at hw
      cases hl : sptIsEmpty l
      · obtain ⟨k, v, hk⟩ := sptWf_exists_key l hw.1.1 hl
        exact ⟨2 * k + 2, v, by rw [sptLookup_left_bn]; exact hk⟩
      · cases hr : sptIsEmpty r
        · obtain ⟨k, v, hk⟩ := sptWf_exists_key r hw.1.2 hr
          exact ⟨2 * k + 1, v, by rw [sptLookup_right_bn]; exact hk⟩
        · rw [hl, hr] at hw; simp at hw

/-- A well-formed tree without keys is `LN` (Flapjack infrastructure). -/
theorem sptWf_empty_of_lookup (t : Spt α) (hw : sptWf t = true)
    (h : ∀ n, sptLookup n t = none) : t = .ln := by
  cases he : sptIsEmpty t
  · obtain ⟨k, v, hk⟩ := sptWf_exists_key t hw he
    rw [h k] at hk; cases hk
  · cases t <;> simp_all [sptIsEmpty]

end KeyDecomposition

/-- Exact HOL `spt_eq_thm` (`HOL/src/finite_maps/sptreeScript.sml:1212-1288`):
well-formed trees are equal exactly when all their lookups agree. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "spt_eq_thm"]
theorem sptEqThm {α : Type} :
    ∀ (t1 t2 : Spt α), sptWf t1 = true ∧ sptWf t2 = true →
      (t1 = t2 ↔ ∀ n, sptLookup n t1 = sptLookup n t2) := by
  intro t1
  induction t1 with
  | ln =>
      rintro t2 ⟨-, h2⟩
      refine ⟨fun h => by subst h; intro; rfl, fun h => ?_⟩
      exact (sptWf_empty_of_lookup t2 h2 (fun n => (h n).symm.trans rfl)).symm
  | ls a =>
      rintro t2 ⟨-, h2⟩
      refine ⟨fun h => by subst h; intro; rfl, fun h => ?_⟩
      have h0 := h 0
      cases t2 with
      | ln => simp [sptLookup] at h0
      | ls b => simp [sptLookup] at h0; rw [h0]
      | bn l r => simp [sptLookup] at h0
      | bs l b r =>
          exfalso
          simp only [sptWf, Bool.and_eq_true, Bool.not_eq_true'] at h2
          cases hl : sptIsEmpty l
          · obtain ⟨k, v, hk⟩ := sptWf_exists_key l h2.1.1 hl
            have := h (2 * k + 2)
            rw [sptLookup_left_bs, hk, sptLookup, if_neg (by omega)] at this
            cases this
          · cases hr : sptIsEmpty r
            · obtain ⟨k, v, hk⟩ := sptWf_exists_key r h2.1.2 hr
              have := h (2 * k + 1)
              rw [sptLookup_right_bs, hk, sptLookup, if_neg (by omega)] at this
              cases this
            · rw [hl, hr] at h2; simp at h2
  | bn l r ihl ihr =>
      rintro t2 ⟨h1, h2⟩
      refine ⟨fun h => by subst h; intro; rfl, fun h => ?_⟩
      have hw1 := h1
      simp only [sptWf, Bool.and_eq_true, Bool.not_eq_true'] at hw1
      have hex : ∃ k v, sptLookup k (.bn l r : Spt α) = some v :=
        sptWf_exists_key _ h1 rfl
      cases t2 with
      | ln =>
          obtain ⟨k, v, hk⟩ := hex
          rw [h k] at hk; simp [sptLookup] at hk
      | ls b =>
          obtain ⟨k, v, hk⟩ := hex
          have := h k
          rw [hk] at this
          cases k with
          | zero => simp [sptLookup] at hk
          | succ k => simp [sptLookup] at this
      | bn l' r' =>
          have hw2 := h2
          simp only [sptWf, Bool.and_eq_true, Bool.not_eq_true'] at hw2
          have hl : l = l' := (ihl l' ⟨hw1.1.1, hw2.1.1⟩).mpr (fun j => by
            have := h (2 * j + 2); rwa [sptLookup_left_bn, sptLookup_left_bn] at this)
          have hr : r = r' := (ihr r' ⟨hw1.1.2, hw2.1.2⟩).mpr (fun j => by
            have := h (2 * j + 1); rwa [sptLookup_right_bn, sptLookup_right_bn] at this)
          rw [hl, hr]
      | bs l' b r' =>
          have := h 0
          simp [sptLookup] at this
  | bs l a r ihl ihr =>
      rintro t2 ⟨h1, h2⟩
      refine ⟨fun h => by subst h; intro; rfl, fun h => ?_⟩
      have hw1 := h1
      simp only [sptWf, Bool.and_eq_true, Bool.not_eq_true'] at hw1
      have h0 := h 0
      cases t2 with
      | ln => simp [sptLookup] at h0
      | bn l' r' => simp [sptLookup] at h0
      | ls b =>
          exfalso
          cases hl : sptIsEmpty l
          · obtain ⟨k, v, hk⟩ := sptWf_exists_key l hw1.1.1 hl
            have := h (2 * k + 2)
            rw [sptLookup_left_bs, hk] at this
            simp [sptLookup] at this
          · cases hr : sptIsEmpty r
            · obtain ⟨k, v, hk⟩ := sptWf_exists_key r hw1.1.2 hr
              have := h (2 * k + 1)
              rw [sptLookup_right_bs, hk] at this
              simp [sptLookup] at this
            · rw [hl, hr] at hw1; simp at hw1
      | bs l' b r' =>
          have hw2 := h2
          simp only [sptWf, Bool.and_eq_true, Bool.not_eq_true'] at hw2
          simp [sptLookup] at h0
          have hl : l = l' := (ihl l' ⟨hw1.1.1, hw2.1.1⟩).mpr (fun j => by
            have := h (2 * j + 2); rwa [sptLookup_left_bs, sptLookup_left_bs] at this)
          have hr : r = r' := (ihr r' ⟨hw1.1.2, hw2.1.2⟩).mpr (fun j => by
            have := h (2 * j + 1); rwa [sptLookup_right_bs, sptLookup_right_bs] at this)
          rw [hl, hr, h0]

/-- Lookup through `mk_BN` (HOL `lookup_mk_BN`; Flapjack infrastructure). -/
theorem sptLookupMkBN {α : Type} (k : Nat) (l r : Spt α) :
    sptLookup k (sptMkBN l r) = sptLookup k (.bn l r) := by
  cases l <;> cases r <;> simp [sptMkBN, sptLookup] <;> split <;> rfl

/-- Lookup through `mk_BS` (HOL `lookup_mk_BS`; Flapjack infrastructure). -/
theorem sptLookupMkBS {α : Type} (k : Nat) (l : Spt α) (a : α) (r : Spt α) :
    sptLookup k (sptMkBS l a r) = sptLookup k (.bs l a r) := by
  cases l <;> cases r <;> simp [sptMkBS, sptLookup] <;> split <;> rfl

/-- Exact HOL `lookup_difference` (`HOL/src/finite_maps/sptreeScript.sml:411-419`). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "lookup_difference"]
theorem sptLookupDifference {α β : Type} :
    ∀ (m1 : Spt α) (m2 : Spt β) (k : Nat),
      sptLookup k (sptDifference m1 m2) =
        if sptLookup k m2 = none then sptLookup k m1 else none := by
  intro m1
  induction m1 with
  | ln => intro m2 k; simp [sptDifference, sptLookup]
  | ls a =>
      intro m2 k
      cases m2 <;> simp only [sptDifference] <;> by_cases hk : k = 0 <;>
        simp [sptLookup, hk]
  | bn l r ihl ihr =>
      intro m2 k
      cases m2 with
      | ln => simp [sptDifference, sptLookup]
      | ls b =>
          simp only [sptDifference]
          by_cases hk : k = 0 <;> simp [sptLookup, hk]
      | bn l' r' =>
          simp only [sptDifference]
          rw [sptLookupMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk]
          · simp only [sptLookup, hk, if_false]
            split <;> first | exact ihl _ _ | exact ihr _ _
      | bs l' b r' =>
          simp only [sptDifference]
          rw [sptLookupMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk]
          · simp only [sptLookup, hk, if_false]
            split <;> first | exact ihl _ _ | exact ihr _ _
  | bs l a r ihl ihr =>
      intro m2 k
      cases m2 with
      | ln => simp [sptDifference, sptLookup]
      | ls b =>
          simp only [sptDifference]
          by_cases hk : k = 0 <;> simp [sptLookup, hk]
      | bn l' r' =>
          simp only [sptDifference]
          rw [sptLookupMkBS]
          by_cases hk : k = 0
          · simp [sptLookup, hk]
          · simp only [sptLookup, hk, if_false]
            split <;> first | exact ihl _ _ | exact ihr _ _
      | bs l' b r' =>
          simp only [sptDifference]
          rw [sptLookupMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk]
          · simp only [sptLookup, hk, if_false]
            split <;> first | exact ihl _ _ | exact ihr _ _

/-- Exact HOL `wf_difference` (`HOL/src/finite_maps/sptreeScript.sml:1925-1930`). -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "wf_difference"]
theorem sptWfDifference {α β : Type} :
    ∀ (t1 : Spt α) (t2 : Spt β), sptWf t1 = true ∧ sptWf t2 = true →
      sptWf (sptDifference t1 t2) = true := by
  intro t1
  induction t1 with
  | ln => intro t2 _; simp [sptDifference]
  | ls a => intro t2 _; cases t2 <;> simp [sptDifference, sptWf]
  | bn l r ihl ihr =>
      intro t2 h
      have hl : sptWf l = true := by have := h.1; simp_all [sptWf]
      have hr : sptWf r = true := by have := h.1; simp_all [sptWf]
      cases t2 with
      | ln => simpa [sptDifference] using h.1
      | ls b => simpa [sptDifference] using h.1
      | bn l' r' =>
          have hl' : sptWf l' = true := by have := h.2; simp_all [sptWf]
          have hr' : sptWf r' = true := by have := h.2; simp_all [sptWf]
          simp only [sptDifference]
          exact wfMkBN _ _ (ihl l' ⟨hl, hl'⟩) (ihr r' ⟨hr, hr'⟩)
      | bs l' b r' =>
          have hl' : sptWf l' = true := by have := h.2; simp_all [sptWf]
          have hr' : sptWf r' = true := by have := h.2; simp_all [sptWf]
          simp only [sptDifference]
          exact wfMkBN _ _ (ihl l' ⟨hl, hl'⟩) (ihr r' ⟨hr, hr'⟩)
  | bs l a r ihl ihr =>
      intro t2 h
      have hl : sptWf l = true := by have := h.1; simp_all [sptWf]
      have hr : sptWf r = true := by have := h.1; simp_all [sptWf]
      cases t2 with
      | ln => simpa [sptDifference] using h.1
      | ls b =>
          simp only [sptDifference]
          simpa [sptWf] using h.1
      | bn l' r' =>
          have hl' : sptWf l' = true := by have := h.2; simp_all [sptWf]
          have hr' : sptWf r' = true := by have := h.2; simp_all [sptWf]
          simp only [sptDifference]
          exact wfMkBS _ _ _ (ihl l' ⟨hl, hl'⟩) (ihr r' ⟨hr, hr'⟩)
      | bs l' b r' =>
          have hl' : sptWf l' = true := by have := h.2; simp_all [sptWf]
          have hr' : sptWf r' = true := by have := h.2; simp_all [sptWf]
          simp only [sptDifference]
          exact wfMkBN _ _ (ihl l' ⟨hl, hl'⟩) (ihr r' ⟨hr, hr'⟩)

end Flapjack
