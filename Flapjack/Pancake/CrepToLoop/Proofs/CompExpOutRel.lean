import Flapjack.Pancake.CrepToLoop.Proofs.CompExpSurvives
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkLemmas

/-!
# crep_to_loop `compile_exp_out_rel`

Counterpart of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`compile_exp_out_rel_cases` (420) and its projections (589/590) over the exact
`compileExpHOLExact`/`compileExpsHOLExact`, `compSyntaxOkHOL`, `cutSetsHOL` and
`holLoopNestedSeq` (bead `flapjack-pxn.18.5.6.32.3`).
-/

namespace Flapjack

/-- `sptInsert` of the same key and value is idempotent (structurally). -/
theorem sptInsert_idem {α : Type} :
    ∀ (k : Nat) (v : α) (t : Spt α), sptInsert k v (sptInsert k v t) = sptInsert k v t := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro v t
    by_cases h0 : k = 0
    · subst h0; cases t <;> simp only [sptInsert_root_zero]
    · have hdec : (k - 1) / 2 < k := by omega
      by_cases he : k % 2 = 0 <;> cases t <;>
        simp only [sptInsert_root_even h0, sptInsert_root_odd h0, he, not_false_eq_true] <;>
        (congr 1; exact ih _ hdec _ _)

variable {width : Nat} [NeZero width]

theorem cutSets_zipWith_assign (m : Nat) (cs : NumSet) :
    ∀ (is : List Nat) (vs : List (HolLoopExp width)), is.length = vs.length →
      cutSetsHOL cs (holLoopNestedSeq
        (List.zipWith (fun i v => HolLoopProg.assign (m + i) v) is vs)) =
      sptListInsert (is.map (m + ·)) cs
  | [], [], _ => by simp [holLoopNestedSeq, cutSetsHOL, sptListInsert]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | i :: is, v :: vs, h => by
      simp only [List.zipWith_cons_cons, holLoopNestedSeq, cutSetsHOL, List.map_cons,
        sptListInsert]
      exact cutSets_zipWith_assign m (sptInsert (m + i) () cs) is vs (by simpa using h)

theorem compSyntaxOk_zipWith_assign (m : Nat) :
    ∀ (cs : NumSet) (is : List Nat) (vs : List (HolLoopExp width)),
      compSyntaxOkHOL cs (holLoopNestedSeq
        (List.zipWith (fun i v => HolLoopProg.assign (m + i) v) is vs)) = true
  | cs, [], _ => by simp [holLoopNestedSeq, compSyntaxOkHOL]
  | cs, _ :: _, [] => by simp [holLoopNestedSeq, compSyntaxOkHOL]
  | cs, i :: is, v :: vs => by
      simp only [List.zipWith_cons_cons, holLoopNestedSeq]
      rw [compSyntaxOkHOL, Bool.and_eq_true]
      exact ⟨by simp [compSyntaxOkHOL], compSyntaxOk_zipWith_assign m _ is vs⟩

theorem sptListInsert_append_seq (xs ys : List Nat) (t : NumSet) :
    sptListInsert (xs ++ ys) t = sptListInsert ys (sptListInsert xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, sptListInsert]; exact ih _

theorem compSyntaxOk_append (l : NumSet) (p q : List (HolLoopProg width))
    (hp : compSyntaxOkHOL l (holLoopNestedSeq p) = true)
    (hq : compSyntaxOkHOL (cutSetsHOL l (holLoopNestedSeq p)) (holLoopNestedSeq q) = true) :
    compSyntaxOkHOL l (holLoopNestedSeq (p ++ q)) = true :=
  comp_syn_ok_nested_seq p q l ⟨hp, hq⟩

mutual
theorem compileExpHOLExact_out_rel (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ e : CrepExpHOL width,
      compSyntaxOkHOL l (holLoopNestedSeq (compileExpHOLExact ct tmp l e).1) = true ∧
      tmp ≤ (compileExpHOLExact ct tmp l e).2.2.1 ∧
      (compileExpHOLExact ct tmp l e).2.2.2 =
        cutSetsHOL l (holLoopNestedSeq (compileExpHOLExact ct tmp l e).1)
  | .baseAddr | .topAddr | .const _ | .var _ | .loadGlob _ => by
      simp [compileExpHOLExact, holLoopNestedSeq, compSyntaxOkHOL, cutSetsHOL]
  | .load a => by
      have ih := compileExpHOLExact_out_rel ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp only at ih; simp only [compileExpHOLExact, hA]; exact ih
  | .load32 a | .loadByte a => by
      have ih := compileExpHOLExact_out_rel ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp only at ih
      obtain ⟨h1, h2, h3⟩ := ih
      simp only [compileExpHOLExact, hA]
      refine ⟨compSyntaxOk_append l _ _ h1 (by simp [holLoopNestedSeq, compSyntaxOkHOL]),
        by omega, ?_⟩
      rw [cut_sets_nested_seq, ← h3]
      simp only [holLoopNestedSeq, cutSetsHOL, sptInsert_idem]
  | .op o es => by
      have ih := compileExpsHOLExact_out_rel ct tmp l es
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp only at ih
      simp only [compileExpHOLExact, hA]; exact ⟨ih.1, ih.2.1, ih.2.2.1⟩
  | .crepOp o es => by
      have ih := compileExpsHOLExact_out_rel ct tmp l es
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp only at ih
      obtain ⟨h1, h2, h3, hlen⟩ := ih
      simp only [compileExpHOLExact, hA]
      cases o
      simp only [compileCrepopHOLExact]
      have hz := cutSets_zipWith_assign (width := width) m ol (List.range vs.length) vs (by simp)
      have hzc := compSyntaxOk_zipWith_assign (width := width) m ol (List.range vs.length) vs
      split
      · -- ARMv7: two-result long multiplication
        simp only
        refine ⟨compSyntaxOk_append l _ _ (compSyntaxOk_append l _ _ h1 (h3 ▸ hzc)) ?_, by omega, ?_⟩
        · simp [holLoopNestedSeq, compSyntaxOkHOL]
        · rw [cut_sets_nested_seq, cut_sets_nested_seq, ← h3, hz]
          simp only [holLoopNestedSeq, cutSetsHOL]
          rw [show m + vs.length + 1 - m = vs.length + 1 by omega, List.range_succ, List.map_append,
            sptListInsert_append_seq]
          simp only [List.map_cons, List.map_nil, sptListInsert]
          exact (sptInsert_comm _ _ _ _ _ (by omega)).symm
      · simp only
        refine ⟨compSyntaxOk_append l _ _ (compSyntaxOk_append l _ _ h1 (h3 ▸ hzc)) ?_, by omega, ?_⟩
        · simp [holLoopNestedSeq, compSyntaxOkHOL]
        · rw [cut_sets_nested_seq, cut_sets_nested_seq, ← h3, hz]
          simp only [holLoopNestedSeq, cutSetsHOL, sptInsert_idem]
          rw [show m + vs.length - m = vs.length by omega]
  | .cmp o a b => by
      have iha := compileExpHOLExact_out_rel ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha; simp only at iha
      obtain ⟨ha1, ha2, ha3⟩ := iha
      have ihb := compileExpHOLExact_out_rel ct m ol b
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb; simp only at ihb
      obtain ⟨hb1, hb2, hb3⟩ := ihb
      simp only [compileExpHOLExact, hA, hB, progIfHOLExact]
      refine ⟨compSyntaxOk_append l _ _ (compSyntaxOk_append l _ _ ha1 (ha3 ▸ hb1)) ?_, by omega, ?_⟩
      · rw [cut_sets_nested_seq, ← ha3, ← hb3]
        simp only [holLoopNestedSeq, compSyntaxOkHOL, cutSetsHOL, Bool.and_true, Bool.true_and,
          holPropBool_eq_true]
        exact ⟨[], rfl⟩
      · rw [cut_sets_nested_seq, cut_sets_nested_seq, ← ha3, ← hb3]
        simp [holLoopNestedSeq, cutSetsHOL]
  | .shift o a b => by
      have iha := compileExpHOLExact_out_rel ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha; simp only at iha
      obtain ⟨ha1, ha2, ha3⟩ := iha
      have ihb := compileExpHOLExact_out_rel ct m ol b
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb; simp only at ihb
      obtain ⟨hb1, hb2, hb3⟩ := ihb
      simp only [compileExpHOLExact, hA, hB]
      refine ⟨compSyntaxOk_append l _ _ ha1 (ha3 ▸ hb1), by omega, ?_⟩
      rw [cut_sets_nested_seq, ← ha3, ← hb3]
termination_by e => sizeOf e

theorem compileExpsHOLExact_out_rel (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ es : List (CrepExpHOL width),
      compSyntaxOkHOL l (holLoopNestedSeq (compileExpsHOLExact ct tmp l es).1) = true ∧
      tmp ≤ (compileExpsHOLExact ct tmp l es).2.2.1 ∧
      (compileExpsHOLExact ct tmp l es).2.2.2 =
        cutSetsHOL l (holLoopNestedSeq (compileExpsHOLExact ct tmp l es).1) ∧
      (compileExpsHOLExact ct tmp l es).2.1.length = es.length
  | [] => by simp [compileExpsHOLExact, holLoopNestedSeq, compSyntaxOkHOL, cutSetsHOL]
  | e :: es => by
      have iha := compileExpHOLExact_out_rel ct tmp l e
      rcases hA : compileExpHOLExact ct tmp l e with ⟨c, v, m, ol⟩
      rw [hA] at iha; simp only at iha
      obtain ⟨ha1, ha2, ha3⟩ := iha
      have ihb := compileExpsHOLExact_out_rel ct m ol es
      rcases hB : compileExpsHOLExact ct m ol es with ⟨c', vs', m', ol'⟩
      rw [hB] at ihb; simp only at ihb
      obtain ⟨hb1, hb2, hb3, hb4⟩ := ihb
      simp only [compileExpsHOLExact, hA, hB, List.length_cons]
      refine ⟨compSyntaxOk_append l _ _ ha1 (ha3 ▸ hb1), by omega, ?_, by omega⟩
      rw [cut_sets_nested_seq, ← ha3, ← hb3]
termination_by es => sizeOf es
end

namespace CrepToLoopCompExpOutRelWitnesses

/-- Same-module re-export of the canonical finite-support witness for the
    `crep_to_loop$context` carrier, required by the `fmap_as_finite_support`
    qualifier on the ports below. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopCompExpOutRelWitnesses

/-- Exact HOL `compile_exp_out_rel_cases` (`crep_to_loopProofScript.sml:420-427`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exp_out_rel_cases"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem compile_exp_out_rel_cases :
    (∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      compileExpHOLExact ct tmp l e = (p, le, ntmp, nl) →
      compSyntaxOkHOL l (holLoopNestedSeq p) = true ∧ tmp ≤ ntmp ∧
        nl = cutSetsHOL l (holLoopNestedSeq p)) ∧
    (∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (le : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet),
      compileExpsHOLExact ct tmp l e = (p, le, ntmp, nl) →
      compSyntaxOkHOL l (holLoopNestedSeq p) = true ∧ tmp ≤ ntmp ∧
        nl = cutSetsHOL l (holLoopNestedSeq p) ∧ le.length = e.length) :=
  ⟨fun ct tmp l e p le ntmp nl h => by
      have := compileExpHOLExact_out_rel ct tmp l e; rw [h] at this; exact this,
   fun ct tmp l e p le ntmp nl h => by
      have := compileExpsHOLExact_out_rel ct tmp l e; rw [h] at this; exact this⟩

/-- Exact HOL `compile_exp_out_rel` (`crep_to_loopProofScript.sml:589`, `CONJUNCT1`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exp_out_rel"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem compile_exp_out_rel :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
      compileExpHOLExact ct tmp l e = (p, le, ntmp, nl) →
      compSyntaxOkHOL l (holLoopNestedSeq p) = true ∧ tmp ≤ ntmp ∧
        nl = cutSetsHOL l (holLoopNestedSeq p) :=
  compile_exp_out_rel_cases.1

/-- Exact HOL `compile_exps_out_rel` (`crep_to_loopProofScript.sml:590`, `CONJUNCT2`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exps_out_rel"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem compile_exps_out_rel :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (le : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet),
      compileExpsHOLExact ct tmp l e = (p, le, ntmp, nl) →
      compSyntaxOkHOL l (holLoopNestedSeq p) = true ∧ tmp ≤ ntmp ∧
        nl = cutSetsHOL l (holLoopNestedSeq p) ∧ le.length = e.length :=
  compile_exp_out_rel_cases.2

end Flapjack
