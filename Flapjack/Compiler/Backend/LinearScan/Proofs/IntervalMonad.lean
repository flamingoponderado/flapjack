import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.Intervals
import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Compiler.Backend.LinearScan.Proofs.RegExchange
import Flapjack.Compiler.Backend.LinearScan.Proofs.CheckIntervals

/-!
# linear_scanProof: live-tree registers and interval bounds

Ports of `linear_scanProofScript.sml:5206-5469`. The `sptree_eq_list`
correspondence between the interval maps and the hidden-state arrays and the
interval-monad correctness theorems use HOL `EL`, rendered by the exact tagged
`holEl`. The `EL`-free theorems (`linear_scanProofScript.sml:5386-5469`) are
exact:
the clash tree's names are the registers of its live-tree view,
`fix_domination` adds no registers, and `get_intervals` keeps every
beginning no later than its end. Renderings as in `Intervals`; `the 0` is the
tagged `miscThe`.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc

/-- Exact HOL `in_clash_tree_eq_live_tree_registers` (`linear_scanProofScript.sml:5386-5398`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "in_clash_tree_eq_live_tree_registers"]
theorem inClashTreeEqLiveTreeRegisters :
    ∀ (ct : ClashTree) (r : Nat), inClashTree ct r ↔ liveTreeRegisters (getLiveTree ct) r := by
  intro ct
  induction ct with
  | delta w rd =>
      intro r
      simp only [inClashTree, getLiveTree, liveTreeRegisters]
      exact Or.comm
  | set s =>
      intro r
      simp only [inClashTree, getLiveTree, liveTreeRegisters]
      exact (sptMemMapFstToAList s r).symm
  | branch o ct1 ct2 ih1 ih2 =>
      intro r
      cases o with
      | none =>
          simp only [inClashTree, getLiveTree, liveTreeRegisters, ih1, ih2]
          simp
      | some cut =>
          simp only [inClashTree, getLiveTree, liveTreeRegisters, ih1, ih2]
          rw [sptMemMapFstToAList]
          constructor
          · rintro (h | h | h)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact Or.inl h
          · rintro (h | h | h)
            · exact Or.inr (Or.inr h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
  | seq ct1 ct2 ih1 ih2 =>
      intro r
      simp only [inClashTree, getLiveTree, liveTreeRegisters, ih1, ih2]

/-- Exact HOL `get_live_backward_in_live_tree_registers`
(`linear_scanProofScript.sml:5400-5407`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_live_backward_in_live_tree_registers"]
theorem getLiveBackwardInLiveTreeRegisters :
    ∀ (lt : LiveTree) (live : NumSet),
      ∀ x, sptDomain (getLiveBackward lt live) x → sptDomain live x ∨ liveTreeRegisters lt x := by
  intro lt
  induction lt with
  | writes l =>
      intro live x hx
      simp only [getLiveBackward] at hx
      rw [RegAlloc.domainNumsetListDelete] at hx
      exact Or.inl hx.1
  | reads l =>
      intro live x hx
      simp only [getLiveBackward] at hx
      rw [domainNumsetListInsert] at hx
      simp only [liveTreeRegisters]
      exact hx.symm
  | branch lt1 lt2 ih1 ih2 =>
      intro live x hx
      simp only [getLiveBackward] at hx
      rw [domainNumsetListInsert] at hx
      simp only [liveTreeRegisters]
      rcases (branchDomainIff _ _ x).mp hx with h | h
      · exact (ih1 live x h).imp_right Or.inl
      · exact (ih2 live x h).imp_right Or.inr
  | seq lt1 lt2 ih1 ih2 =>
      intro live x hx
      simp only [getLiveBackward] at hx
      simp only [liveTreeRegisters]
      rcases ih1 _ x hx with h | h
      · rcases ih2 live x h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)

/-- Exact HOL `fix_domination_live_tree_registers` (`linear_scanProofScript.sml:5409-5417`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "fix_domination_live_tree_registers"]
theorem fixDominationLiveTreeRegisters :
    ∀ (lt : LiveTree), liveTreeRegisters (fixDomination lt) = liveTreeRegisters lt := by
  intro lt
  simp only [fixDomination]
  split
  · rfl
  · funext x
    simp only [liveTreeRegisters]
    apply propext
    constructor
    · rintro (h | h)
      · rw [sptMemMapFstToAList] at h
        rcases getLiveBackwardInLiveTreeRegisters lt .ln x h with h | h
        · simp [sptDomain, sptLookup] at h
        · exact h
      · exact h
    · exact Or.inr

/-- Exact HOL `get_intervals_beg_less_end` (`linear_scanProofScript.sml:5419-5469`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "get_intervals_beg_less_end"]
theorem getIntervalsBegLessEnd :
    ∀ (lt : LiveTree) (n_in : Int) (beg_in end_in : Spt Int) (n_out : Int)
      (beg_out end_out : Spt Int),
      (∀ r, sptDomain beg_in r →
        miscThe 0 (sptLookup r beg_in) ≤ miscThe 0 (sptLookup r end_in)) ∧
      (∀ x, sptDomain beg_in x → sptDomain end_in x) ∧
      (n_out, beg_out, end_out) = getIntervals lt n_in beg_in end_in →
      (∀ r, sptDomain beg_out r →
        miscThe 0 (sptLookup r beg_out) ≤ miscThe 0 (sptLookup r end_out)) ∧
      (∀ x, sptDomain beg_out x → sptDomain end_out x) := by
  intro lt
  induction lt with
  | writes l =>
      intro n_in beg_in end_in n_out beg_out end_out ⟨hle, hsub, h⟩
      simp only [getIntervals, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      constructor
      · intro r hr
        rw [lookupNumsetListAddIfLt, lookupNumsetListAddIfGt]
        by_cases hm : r ∈ l
        · rw [if_pos hm, if_pos hm]
          cases hb : sptLookup r beg_in with
          | none =>
              cases he : sptLookup r end_in with
              | none => simp [miscThe]
              | some ve => by_cases hc : ve ≤ n_in <;> simp [miscThe, hc] <;> omega
          | some vb =>
              cases he : sptLookup r end_in with
              | none =>
                  by_cases hc : n_in ≤ vb <;> simp [miscThe, hc] <;> omega
              | some ve =>
                  by_cases hc : n_in ≤ vb <;> by_cases hc' : ve ≤ n_in <;>
                    simp [miscThe, hc, hc'] <;> omega
        · rw [if_neg hm, if_neg hm]
          rw [domainNumsetListAddIfLt] at hr
          exact hle r (hr.resolve_left hm)
      · intro x hx
        rw [domainNumsetListAddIfLt] at hx
        rw [domainNumsetListAddIfGt]
        exact hx.imp_right (hsub x)
  | reads l =>
      intro n_in beg_in end_in n_out beg_out end_out ⟨hle, hsub, h⟩
      simp only [getIntervals, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      constructor
      · intro r hr
        have h1 := hle r hr
        rw [lookupNumsetListAddIfGt]
        by_cases hm : r ∈ l
        · rw [if_pos hm]
          have hd := hsub r hr
          unfold sptDomain at hd
          cases he : sptLookup r end_in with
          | none => rw [he] at hd; simp at hd
          | some ve =>
              rw [he] at h1
              by_cases hc : ve ≤ n_in <;> simp [miscThe, hc] at h1 ⊢ <;> omega
        · rw [if_neg hm]; exact h1
      · intro x hx
        rw [domainNumsetListAddIfGt]
        exact Or.inr (hsub x hx)
  | branch lt1 lt2 ih1 ih2 | seq lt1 lt2 ih1 ih2 =>
      intro n_in beg_in end_in n_out beg_out end_out ⟨hle, hsub, h⟩
      simp only [getIntervals] at h
      rcases h2 : getIntervals lt2 n_in beg_in end_in with ⟨n2, b2, e2⟩
      rw [h2] at h
      obtain ⟨hle2, hsub2⟩ := ih2 _ _ _ _ _ _ ⟨hle, hsub, h2.symm⟩
      exact ih1 _ _ _ _ _ _ ⟨hle2, hsub2, h⟩

/-- HOL proof-script definition `sptree_eq_list` (`linear_scanProofScript.sml:5206-5211`).

HOL `EL` is the exact `holEl`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "sptree_eq_list_def"]
def sptreeEqList (s : Spt Int) (l : List Int) : Prop :=
  ∀ i, i < l.length →
    (0 < holEl i l ↔ sptLookup i s = none) ∧ (holEl i l ≤ 0 ↔ sptLookup i s = some (holEl i l))

private theorem sptreeEqListStep (s : Spt Int) (l : List Int) (r : Nat) (v : Int) (hv : v ≤ 0)
    (hr : r < l.length) (h : sptreeEqList s l) : sptreeEqList (sptInsert r v s) (l.set r v) := by
  intro i hi
  rw [List.length_set] at hi
  rw [holEl_set l r i v hr]
  by_cases hri : r = i
  · subst hri
    rw [if_pos rfl, sptLookup_sptInsert_same]
    constructor
    · constructor
      · intro h0; omega
      · intro h0; cases h0
    · exact ⟨fun _ => rfl, fun _ => hv⟩
  · rw [if_neg hri, sptLookup_sptInsert_ne r i v s (Ne.symm hri)]
    exact h i hi

private theorem sptreeEqListLookup (s : Spt Int) (l : List Int) (r : Nat) (hr : r < l.length)
    (h : sptreeEqList s l) :
    (0 < holEl r l → sptLookup r s = none) ∧ (holEl r l ≤ 0 → sptLookup r s = some (holEl r l)) :=
  ⟨(h r hr).1.mp, (h r hr).2.mp⟩

/-- HOL `numset_list_add_if_lt_monad_correct` (`linear_scanProofScript.sml:5213-5232`).

HOL `EL` (through `sptree_eq_list`) is the exact `holEl`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "numset_list_add_if_lt_monad_correct"]
theorem numsetListAddIfLtMonadCorrect :
    ∀ (int_beg : Spt Int) (sth : LinearScanHiddenState) (l : List Nat) (v : Int),
      v ≤ 0 ∧ sptreeEqList int_beg sth.int_beg ∧ (∀ r, r ∈ l → r < sth.int_beg.length) →
      ∃ sthout, numsetListAddIfLtMonad l v sth = (.success (), sthout) ∧
        sptreeEqList (numsetListAddIfLt l v int_beg) sthout.int_beg ∧
        sthout = { sth with int_beg := sthout.int_beg } ∧
        sthout.int_beg.length = sth.int_beg.length := by
  intro int_beg sth l
  induction l generalizing int_beg sth with
  | nil => intro v ⟨_, h, _⟩; exact ⟨sth, rfl, h, rfl, rfl⟩
  | cons r rs ih =>
      intro v ⟨hv, h, hl⟩
      have hr : r < sth.int_beg.length := hl r List.mem_cons_self
      have hrs : ∀ x, x ∈ rs → x < sth.int_beg.length := fun x hx => hl x (List.mem_cons_of_mem r hx)
      obtain ⟨hpos, hnpos⟩ := sptreeEqListLookup int_beg sth.int_beg r hr h
      let sth' : LinearScanHiddenState := { sth with int_beg := sth.int_beg.set r v }
      have hupd : ∀ (k : LsM Unit),
          Translator.Monadic.MonadBase.ignoreBind (updateIntBeg r v) k sth = k sth' := by
        intro k
        unfold Translator.Monadic.MonadBase.ignoreBind
        rw [updateIntBegEqn, if_pos hr]
      have hsub : ∀ (k : Int → LsM Unit),
          Translator.Monadic.MonadBase.bind (intBegSub r) k sth = k (holEl r sth.int_beg) sth := by
        intro k
        unfold Translator.Monadic.MonadBase.bind
        rw [intBegSubEqn, if_pos hr]
      have hstep' : sptreeEqList (sptInsert r v int_beg) sth'.int_beg :=
        sptreeEqListStep int_beg sth.int_beg r v hv hr h
      have hlen' : sth'.int_beg.length = sth.int_beg.length := by simp [sth']
      by_cases h0 : 0 < holEl r sth.int_beg
      · obtain ⟨so, hrun, heq, hso, hlen⟩ := ih (sptInsert r v int_beg) sth' v
          ⟨hv, hstep', fun x hx => by rw [hlen']; exact hrs x hx⟩
        refine ⟨so, ?_, ?_, ?_, ?_⟩
        · show numsetListAddIfLtMonad (r :: rs) v sth = _
          simp only [numsetListAddIfLtMonad]
          rw [hsub]; simp only [if_pos h0]; rw [hupd]; exact hrun
        · simp only [numsetListAddIfLt, numsetListAddIf, hpos h0] at heq ⊢; exact heq
        · rw [hso]
        · rw [hlen, hlen']
      · have hle : holEl r sth.int_beg ≤ 0 := by omega
        have hlk := hnpos hle
        by_cases hvb : v ≤ holEl r sth.int_beg
        · obtain ⟨so, hrun, heq, hso, hlen⟩ := ih (sptInsert r v int_beg) sth' v
            ⟨hv, hstep', fun x hx => by rw [hlen']; exact hrs x hx⟩
          refine ⟨so, ?_, ?_, ?_, ?_⟩
          · simp only [numsetListAddIfLtMonad]
            rw [hsub]; simp only [if_neg h0, if_pos hvb]; rw [hupd]; exact hrun
          · simp only [numsetListAddIfLt, numsetListAddIf, hlk, decide_eq_true hvb, if_true] at heq ⊢
            exact heq
          · rw [hso]
          · rw [hlen, hlen']
        · obtain ⟨so, hrun, heq, hso, hlen⟩ := ih int_beg sth v ⟨hv, h, hrs⟩
          refine ⟨so, ?_, ?_, hso, hlen⟩
          · simp only [numsetListAddIfLtMonad]
            rw [hsub]; simp only [if_neg h0, if_neg hvb]; exact hrun
          · simp only [numsetListAddIfLt, numsetListAddIf, hlk, decide_eq_false hvb,
              Bool.false_eq_true, if_false] at heq ⊢
            exact heq

/-- HOL `numset_list_add_if_gt_monad_correct` (`linear_scanProofScript.sml:5234-5253`).

HOL `EL` (through `sptree_eq_list`) is the exact `holEl`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "numset_list_add_if_gt_monad_correct"]
theorem numsetListAddIfGtMonadCorrect :
    ∀ (int_end : Spt Int) (sth : LinearScanHiddenState) (l : List Nat) (v : Int),
      v ≤ 0 ∧ sptreeEqList int_end sth.int_end ∧ (∀ r, r ∈ l → r < sth.int_end.length) →
      ∃ sthout, numsetListAddIfGtMonad l v sth = (.success (), sthout) ∧
        sptreeEqList (numsetListAddIfGt l v int_end) sthout.int_end ∧
        sthout = { sth with int_end := sthout.int_end } ∧
        sthout.int_end.length = sth.int_end.length := by
  intro int_end sth l
  induction l generalizing int_end sth with
  | nil => intro v ⟨_, h, _⟩; exact ⟨sth, rfl, h, rfl, rfl⟩
  | cons r rs ih =>
      intro v ⟨hv, h, hl⟩
      have hr : r < sth.int_end.length := hl r List.mem_cons_self
      have hrs : ∀ x, x ∈ rs → x < sth.int_end.length := fun x hx => hl x (List.mem_cons_of_mem r hx)
      obtain ⟨hpos, hnpos⟩ := sptreeEqListLookup int_end sth.int_end r hr h
      let sth' : LinearScanHiddenState := { sth with int_end := sth.int_end.set r v }
      have hupd : ∀ (k : LsM Unit),
          Translator.Monadic.MonadBase.ignoreBind (updateIntEnd r v) k sth = k sth' := by
        intro k
        unfold Translator.Monadic.MonadBase.ignoreBind
        rw [updateIntEndEqn, if_pos hr]
      have hsub : ∀ (k : Int → LsM Unit),
          Translator.Monadic.MonadBase.bind (intEndSub r) k sth = k (holEl r sth.int_end) sth := by
        intro k
        unfold Translator.Monadic.MonadBase.bind
        rw [intEndSubEqn, if_pos hr]
      have hstep' : sptreeEqList (sptInsert r v int_end) sth'.int_end :=
        sptreeEqListStep int_end sth.int_end r v hv hr h
      have hlen' : sth'.int_end.length = sth.int_end.length := by simp [sth']
      by_cases h0 : 0 < holEl r sth.int_end
      · obtain ⟨so, hrun, heq, hso, hlen⟩ := ih (sptInsert r v int_end) sth' v
          ⟨hv, hstep', fun x hx => by rw [hlen']; exact hrs x hx⟩
        refine ⟨so, ?_, ?_, ?_, ?_⟩
        · simp only [numsetListAddIfGtMonad]
          rw [hsub]; simp only [if_pos h0]; rw [hupd]; exact hrun
        · simp only [numsetListAddIfGt, numsetListAddIf, hpos h0] at heq ⊢; exact heq
        · rw [hso]
        · rw [hlen, hlen']
      · have hle : holEl r sth.int_end ≤ 0 := by omega
        have hlk := hnpos hle
        by_cases hvb : holEl r sth.int_end ≤ v
        · obtain ⟨so, hrun, heq, hso, hlen⟩ := ih (sptInsert r v int_end) sth' v
            ⟨hv, hstep', fun x hx => by rw [hlen']; exact hrs x hx⟩
          refine ⟨so, ?_, ?_, ?_, ?_⟩
          · simp only [numsetListAddIfGtMonad]
            rw [hsub]; simp only [if_neg h0, if_pos hvb]; rw [hupd]; exact hrun
          · simp only [numsetListAddIfGt, numsetListAddIf, hlk, decide_eq_true hvb, if_true] at heq ⊢
            exact heq
          · rw [hso]
          · rw [hlen, hlen']
        · obtain ⟨so, hrun, heq, hso, hlen⟩ := ih int_end sth v ⟨hv, h, hrs⟩
          refine ⟨so, ?_, ?_, hso, hlen⟩
          · simp only [numsetListAddIfGtMonad]
            rw [hsub]; simp only [if_neg h0, if_neg hvb]; exact hrun
          · simp only [numsetListAddIfGt, numsetListAddIf, hlk, decide_eq_false hvb,
              Bool.false_eq_true, if_false] at heq ⊢
            exact heq

private theorem bindOk {α β : Type} {m : LsM α} {k : α → LsM β} {s s1 : LinearScanHiddenState}
    {a : α} (h : m s = (.success a, s1)) : Translator.Monadic.MonadBase.bind m k s = k a s1 := by
  unfold Translator.Monadic.MonadBase.bind; rw [h]

private theorem ignoreBindOk {α β : Type} {m : LsM α} {k : LsM β} {s s1 : LinearScanHiddenState}
    {a : α} (h : m s = (.success a, s1)) : Translator.Monadic.MonadBase.ignoreBind m k s = k s1 := by
  unfold Translator.Monadic.MonadBase.ignoreBind; rw [h]

/-- Field bookkeeping for `sthout = sth with <| int_beg := _; int_end := _ |>`. -/
private def sameOthers (s t : LinearScanHiddenState) : Prop :=
  t.colors = s.colors ∧ t.sorted_regs = s.sorted_regs ∧ t.sorted_moves = s.sorted_moves

private theorem sameOthers_beg {s t : LinearScanHiddenState} (h : t = { s with int_beg := t.int_beg }) :
    sameOthers s t ∧ t.int_end = s.int_end := by
  rw [h]; exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

private theorem sameOthers_end {s t : LinearScanHiddenState} (h : t = { s with int_end := t.int_end }) :
    sameOthers s t ∧ t.int_beg = s.int_beg := by
  rw [h]; exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

private theorem sameOthers_both {s t : LinearScanHiddenState}
    (h : t = { s with int_beg := t.int_beg, int_end := t.int_end }) : sameOthers s t := by
  rw [h]; exact ⟨rfl, rfl, rfl⟩

private theorem sameOthers_trans {a b c : LinearScanHiddenState} (h1 : sameOthers a b)
    (h2 : sameOthers b c) : sameOthers a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

private theorem eq_of_sameOthers {s t : LinearScanHiddenState} (h : sameOthers s t) :
    t = { s with int_beg := t.int_beg, int_end := t.int_end } := by
  obtain ⟨h1, h2, h3⟩ := h
  cases t; cases s; simp_all

private theorem getIntervalsCtAuxBranch' (o : Option NumSet) (ct1 ct2 : ClashTree) (n : Int)
    (b e : Spt Int) (live : NumSet) (n_out : Int) (b_out e_out : Spt Int) (l_out : NumSet)
    (h : getIntervalsCtAux (.branch o ct1 ct2) n b e live = (n_out, b_out, e_out, l_out)) :
    ∃ n2 b2 e2 l2 n1 b1 e1 l1,
      getIntervalsCtAux ct2 n b e live = (n2, b2, e2, l2) ∧
      getIntervalsCtAux ct1 n2 b2 e2 live = (n1, b1, e1, l1) ∧
      (o = none → (n_out, b_out, e_out, l_out) = (n1, b1, e1, sptUnion l1 l2)) ∧
      (∀ cutset, o = some cutset → (n_out, b_out, e_out, l_out) =
        (n1 - 1, b1, numsetListAddIfGt ((sptToAList cutset).map Prod.fst) n1 e1,
          sptUnion cutset (sptUnion l1 l2))) := by
  rcases h2 : getIntervalsCtAux ct2 n b e live with ⟨n2, b2, e2, l2⟩
  rcases h1 : getIntervalsCtAux ct1 n2 b2 e2 live with ⟨n1, b1, e1, l1⟩
  refine ⟨n2, b2, e2, l2, n1, b1, e1, l1, rfl, h1, ?_, ?_⟩
  · intro ho; subst ho; simp only [getIntervalsCtAux, h2, h1] at h; exact h.symm
  · intro c hc; subst hc; simp only [getIntervalsCtAux, h2, h1] at h; exact h.symm

/-- HOL `get_intervals_ct_monad_aux_correct` (`linear_scanProofScript.sml:5255-5347`).

HOL `EL` (through `sptree_eq_list`) is the exact `holEl`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_ct_monad_aux_correct"]
theorem getIntervalsCtMonadAuxCorrect :
    ∀ (ct : ClashTree) (sth : LinearScanHiddenState) (live : NumSet) (n : Int)
      (int_beg int_end : Spt Int) (nout : Int) (int_begout int_endout : Spt Int)
      (liveout : NumSet),
      n ≤ 0 ∧ sptreeEqList int_beg sth.int_beg ∧ sptreeEqList int_end sth.int_end ∧
      getIntervalsCtAux ct n int_beg int_end live = (nout, int_begout, int_endout, liveout) ∧
      sth.int_end.length = sth.int_beg.length ∧
      (∀ r, inClashTree ct r → r < sth.int_beg.length) ∧
      (∀ r, sptDomain live r → r < sth.int_beg.length) →
      ∃ sthout, getIntervalsCtMonadAux ct n live sth = (.success (nout, liveout), sthout) ∧
        sptreeEqList int_begout sthout.int_beg ∧ sptreeEqList int_endout sthout.int_end ∧
        sthout.int_beg.length = sth.int_beg.length ∧ sthout.int_end.length = sth.int_end.length ∧
        (∀ r, sptDomain liveout r → r < sth.int_beg.length) ∧
        sthout = { sth with int_beg := sthout.int_beg, int_end := sthout.int_end } ∧
        nout ≤ 0 := by
  intro ct
  induction ct with
  | delta wr rd =>
      intro sth live n int_beg int_end nout int_begout int_endout liveout
        ⟨hn, hb, he, hp, hlen, hct, hlive⟩
      simp only [getIntervalsCtAux, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
      obtain ⟨s1, r1, q1, so1, l1⟩ := numsetListAddIfLtMonadCorrect int_beg sth wr n
        ⟨hn, hb, fun r hr => hct r (Or.inl hr)⟩
      obtain ⟨o1, e1⟩ := sameOthers_beg so1
      obtain ⟨s2, r2, q2, so2, l2⟩ := numsetListAddIfGtMonadCorrect int_end s1 wr n
        ⟨hn, by rw [e1]; exact he, fun r hr => by rw [e1, hlen]; exact hct r (Or.inl hr)⟩
      obtain ⟨o2, e2⟩ := sameOthers_end so2
      obtain ⟨s3, r3, q3, so3, l3⟩ := numsetListAddIfGtMonadCorrect _ s2 rd (n - 1)
        ⟨by omega, q2, fun r hr => by rw [l2, e1, hlen]; exact hct r (Or.inr hr)⟩
      obtain ⟨o3, e3⟩ := sameOthers_end so3
      refine ⟨s3, ?_, by rw [e3, e2]; exact q1, q3, by rw [e3, e2, l1], by rw [l3, l2, e1], ?_,
        eq_of_sameOthers (sameOthers_trans (sameOthers_trans o1 o2) o3), by omega⟩
      · simp only [getIntervalsCtMonadAux]
        rw [ignoreBindOk r1, ignoreBindOk r2, ignoreBindOk r3]
        rfl
      · intro r hr
        rw [domainNumsetListInsert, RegAlloc.domainNumsetListDelete] at hr
        rcases hr with hr | ⟨hr, _⟩
        · exact hct r (Or.inr hr)
        · exact hlive r hr
  | set cut =>
      intro sth live n int_beg int_end nout int_begout int_endout liveout
        ⟨hn, hb, he, hp, hlen, hct, hlive⟩
      simp only [getIntervalsCtAux, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
      obtain ⟨s1, r1, q1, so1, l1⟩ := numsetListAddIfGtMonadCorrect int_end sth
        ((sptToAList cut).map Prod.fst) n
        ⟨hn, he, fun r hr => by rw [hlen]; exact hct r ((sptMemMapFstToAList cut r).mp hr)⟩
      obtain ⟨o1, e1⟩ := sameOthers_end so1
      refine ⟨s1, ?_, by rw [e1]; exact hb, q1, by rw [e1], l1, ?_, eq_of_sameOthers o1, by omega⟩
      · simp only [getIntervalsCtMonadAux]
        rw [ignoreBindOk r1]
        rfl
      · intro r hr
        rw [sptDomain_sptUnion] at hr
        rcases hr with hr | hr
        · exact hct r hr
        · exact hlive r hr
  | branch o ct1 ct2 ih1 ih2 =>
      intro sth live n int_beg int_end nout int_begout int_endout liveout
        ⟨hn, hb, he, hp, hlen, hct, hlive⟩
      obtain ⟨n2, b2, e2, lv2, n1, b1, e1, lv1, h2, h1, hnone, hsome⟩ :=
        getIntervalsCtAuxBranch' o ct1 ct2 _ _ _ _ _ _ _ _ hp
      obtain ⟨s2, r2, qb2, qe2, lb2, le2, hl2, so2, hn2⟩ := ih2 sth live n int_beg int_end n2 b2 e2 lv2
        ⟨hn, hb, he, h2, hlen, fun r hr => hct r (Or.inr (Or.inl hr)), hlive⟩
      obtain ⟨s1, r1, qb1, qe1, lb1, le1, hl1, so1, hn1⟩ := ih1 s2 live n2 b2 e2 n1 b1 e1 lv1
        ⟨hn2, qb2, qe2, h1, by rw [le2, lb2, hlen], fun r hr => by rw [lb2]; exact hct r (Or.inl hr),
          fun r hr => by rw [lb2]; exact hlive r hr⟩
      have o21 := sameOthers_trans (sameOthers_both so2) (sameOthers_both so1)
      have hmon : ∀ k : Int × NumSet → LsM (Int × NumSet),
          Translator.Monadic.MonadBase.bind (getIntervalsCtMonadAux ct2 n live)
            (fun p => Translator.Monadic.MonadBase.bind (getIntervalsCtMonadAux ct1 p.1 live)
              (fun q => k (q.1, sptUnion q.2 p.2))) sth = k (n1, sptUnion lv1 lv2) s1 := by
        intro k
        rw [bindOk r2]
        simp only
        rw [bindOk r1]
      cases o with
      | none =>
          have hr := hnone rfl
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
          refine ⟨s1, ?_, qb1, qe1, by rw [lb1, lb2], by rw [le1, le2], ?_, eq_of_sameOthers o21, hn1⟩
          · simp only [getIntervalsCtMonadAux]
            exact hmon (fun q => Translator.Monadic.MonadBase.ret q)
          · intro r hr
            rw [sptDomain_sptUnion] at hr
            rcases hr with hr | hr
            · rw [← lb2]; exact hl1 r hr
            · exact hl2 r hr
      | some cut =>
          have hr := hsome cut rfl
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
          obtain ⟨s3, r3, q3, so3, l3⟩ := numsetListAddIfGtMonadCorrect e1 s1
            ((sptToAList cut).map Prod.fst) n1
            ⟨hn1, qe1, fun r hr => by
              rw [le1, le2, hlen]; exact hct r (Or.inr (Or.inr ((sptMemMapFstToAList cut r).mp hr)))⟩
          obtain ⟨o3, e3⟩ := sameOthers_end so3
          refine ⟨s3, ?_, by rw [e3]; exact qb1, q3, by rw [e3, lb1, lb2], by rw [l3, le1, le2], ?_,
            eq_of_sameOthers (sameOthers_trans o21 o3), by omega⟩
          · simp only [getIntervalsCtMonadAux]
            refine (hmon (fun q => Translator.Monadic.MonadBase.ignoreBind
              (numsetListAddIfGtMonad ((sptToAList cut).map Prod.fst) q.1)
              (Translator.Monadic.MonadBase.ret (q.1 - 1, sptUnion cut q.2)))).trans ?_
            rw [ignoreBindOk r3]
            rfl
          · intro r hr
            rw [sptDomain_sptUnion, sptDomain_sptUnion] at hr
            rcases hr with hr | hr | hr
            · exact hct r (Or.inr (Or.inr hr))
            · rw [← lb2]; exact hl1 r hr
            · exact hl2 r hr
  | seq ct1 ct2 ih1 ih2 =>
      intro sth live n int_beg int_end nout int_begout int_endout liveout
        ⟨hn, hb, he, hp, hlen, hct, hlive⟩
      simp only [getIntervalsCtAux] at hp
      rcases h2 : getIntervalsCtAux ct2 n int_beg int_end live with ⟨n2, b2, e2, lv2⟩
      rw [h2] at hp
      obtain ⟨s2, r2, qb2, qe2, lb2, le2, hl2, so2, hn2⟩ := ih2 sth live n int_beg int_end n2 b2 e2 lv2
        ⟨hn, hb, he, h2, hlen, fun r hr => hct r (Or.inr hr), hlive⟩
      obtain ⟨s1, r1, qb1, qe1, lb1, le1, hl1, so1, hn1⟩ := ih1 s2 lv2 n2 b2 e2 _ _ _ _
        ⟨hn2, qb2, qe2, hp, by rw [le2, lb2, hlen], fun r hr => by rw [lb2]; exact hct r (Or.inl hr),
          fun r hr => by rw [lb2]; exact hl2 r hr⟩
      refine ⟨s1, ?_, qb1, qe1, by rw [lb1, lb2], by rw [le1, le2], fun r hr => by rw [← lb2]; exact hl1 r hr,
        eq_of_sameOthers (sameOthers_trans (sameOthers_both so2) (sameOthers_both so1)), hn1⟩
      simp only [getIntervalsCtMonadAux]
      rw [bindOk r2]
      exact r1

/-- HOL `get_intervals_ct_monad_correct` (`linear_scanProofScript.sml:5349-5384`).

HOL `EL` is the exact `holEl`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "get_intervals_ct_monad_correct"]
theorem getIntervalsCtMonadCorrect :
    ∀ (ct : ClashTree) (sth : LinearScanHiddenState) (n : Int) (int_beg int_end : Spt Int),
      (∀ i, i < sth.int_beg.length → 0 < holEl i sth.int_beg) ∧
      (∀ i, i < sth.int_end.length → 0 < holEl i sth.int_end) ∧
      getIntervalsCt ct = (n, int_beg, int_end) ∧
      sth.int_end.length = sth.int_beg.length ∧
      (∀ r, inClashTree ct r → r < sth.int_beg.length) →
      ∃ sthout, getIntervalsCtMonad ct sth = (.success n, sthout) ∧
        sptreeEqList int_beg sthout.int_beg ∧ sptreeEqList int_end sthout.int_end ∧
        sthout.int_beg.length = sth.int_beg.length ∧ sthout.int_end.length = sth.int_end.length ∧
        sthout = { sth with int_beg := sthout.int_beg, int_end := sthout.int_end } := by
  intro ct sth n int_beg int_end ⟨hpb, hpe, hct0, hlen, hct⟩
  have initEq : ∀ l : List Int, (∀ i, i < l.length → 0 < holEl i l) → sptreeEqList .ln l := by
    intro l hl i hi
    have := hl i hi
    exact ⟨⟨fun _ => rfl, fun _ => this⟩, ⟨fun h => by omega, fun h => by cases h⟩⟩
  rcases ha : getIntervalsCtAux ct 0 .ln .ln .ln with ⟨n1, b1, e1, live⟩
  obtain ⟨s1, r1, qb1, qe1, lb1, le1, hl1, so1, hn1⟩ := getIntervalsCtMonadAuxCorrect ct sth .ln 0 .ln .ln
    n1 b1 e1 live ⟨Int.le_refl _, initEq _ hpb, initEq _ hpe, ha, hlen, hct,
      fun r hr => by simp [sptDomain, sptLookup] at hr⟩
  simp only [getIntervalsCt, ha, Prod.mk.injEq] at hct0
  obtain ⟨rfl, rfl, rfl⟩ := hct0
  obtain ⟨s2, r2, q2, so2, l2⟩ := numsetListAddIfLtMonadCorrect b1 s1 ((sptToAList live).map Prod.fst) n1
    ⟨hn1, qb1, fun r hr => by rw [lb1]; exact hl1 r ((sptMemMapFstToAList live r).mp hr)⟩
  obtain ⟨o2, e2⟩ := sameOthers_beg so2
  obtain ⟨s3, r3, q3, so3, l3⟩ := numsetListAddIfGtMonadCorrect e1 s2 ((sptToAList live).map Prod.fst) n1
    ⟨hn1, by rw [e2]; exact qe1, fun r hr => by
      rw [e2, le1, hlen]; exact hl1 r ((sptMemMapFstToAList live r).mp hr)⟩
  obtain ⟨o3, e3⟩ := sameOthers_end so3
  refine ⟨s3, ?_, by rw [e3]; exact q2, q3, by rw [e3, l2, lb1], by rw [l3, e2, le1],
    eq_of_sameOthers (sameOthers_trans (sameOthers_trans (sameOthers_both so1) o2) o3)⟩
  simp only [getIntervalsCtMonad]
  rw [bindOk r1]
  simp only
  rw [ignoreBindOk r2, ignoreBindOk r3]
  rfl

end Flapjack.LinearScan
