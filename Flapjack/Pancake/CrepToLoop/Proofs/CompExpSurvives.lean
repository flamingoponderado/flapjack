import Flapjack.Pancake.CrepToLoop.Proofs.CompExpLeTmpDomain
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

/-!
# crep_to_loopProof `member_cutset_survives_comp_exp`

Counterpart of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`member_cutset_survives_comp_exp_cases` (1321), its projections (1426/1428) and
`[local]` flips (1432/1434) over the exact `compileExpHOLExact`/
`compileExpsHOLExact`, `survivesHOLExact` and `holLoopNestedSeq`
(bead `flapjack-pxn.18.5.6.33.6`).
-/

namespace Flapjack

variable {width : Nat} [NeZero width]

theorem survives_nested_seq_append (n : Nat) (p q : List (HolLoopProg width))
    (hp : survivesHOLExact n (holLoopNestedSeq p) = true)
    (hq : survivesHOLExact n (holLoopNestedSeq q) = true) :
    survivesHOLExact n (holLoopNestedSeq (p ++ q)) = true :=
  survives_nested_seq_intro p q n ⟨hp, hq⟩

mutual
theorem compileExpHOLExact_survives (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ (e : CrepExpHOL width) (n : Nat), (sptLookup n l).isSome = true →
      survivesHOLExact n (holLoopNestedSeq (compileExpHOLExact ct tmp l e).1) = true
  | .baseAddr, n, _ | .topAddr, n, _ | .const _, n, _ | .var _, n, _ | .loadGlob _, n, _ => by
      simp [compileExpHOLExact, holLoopNestedSeq, survivesHOLExact]
  | .load a, n, h => by
      have ih := compileExpHOLExact_survives ct tmp l a n h
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp only at ih; simp only [compileExpHOLExact, hA]; exact ih
  | .load32 a, n, h | .loadByte a, n, h => by
      have ih := compileExpHOLExact_survives ct tmp l a n h
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp only at ih; simp only [compileExpHOLExact, hA]
      exact survives_nested_seq_append n _ _ ih (by simp [holLoopNestedSeq, survivesHOLExact])
  | .op o es, n, h => by
      have ih := compileExpsHOLExact_survives ct tmp l es n h
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp only at ih; simp only [compileExpHOLExact, hA]; exact ih
  | .crepOp o es, n, h => by
      have ih := compileExpsHOLExact_survives ct tmp l es n h
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp only at ih
      simp only [compileExpHOLExact, hA]
      rcases hB : compileCrepopHOLExact (width := width) o ct.target m (m + 1) (m + vs.length)
        (sptListInsert ((List.range vs.length).map (fun offset => m + offset)) ol) with ⟨oc, d⟩
      simp only
      have hassign : ∀ (is : List Nat) (xs : List (HolLoopExp width)),
          survivesHOLExact n (holLoopNestedSeq
            (List.zipWith (fun i v => HolLoopProg.assign (m + i) v) is xs)) = true := by
        intro is xs
        induction is generalizing xs with
        | nil => simp [holLoopNestedSeq, survivesHOLExact]
        | cons i is ihi => cases xs <;> simp [holLoopNestedSeq, survivesHOLExact, ihi]
      have hoc : survivesHOLExact n (holLoopNestedSeq oc) = true := by
        cases o
        simp only [compileCrepopHOLExact] at hB
        split at hB <;> (simp only [Prod.mk.injEq] at hB; obtain ⟨rfl, rfl⟩ := hB) <;>
          simp [holLoopNestedSeq, survivesHOLExact]
      exact survives_nested_seq_append n _ _ (survives_nested_seq_append n _ _ ih (hassign _ _)) hoc
  | .cmp o a b, n, h => by
      have iha := compileExpHOLExact_survives ct tmp l a n h
      have hdom := compileExpHOLExact_domain_mono ct tmp l a n h
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha hdom; simp only at iha hdom
      have ihb := compileExpHOLExact_survives ct m ol b n hdom
      have hdom2 := compileExpHOLExact_domain_mono ct m ol b n hdom
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb hdom2; simp only at ihb hdom2
      simp only [compileExpHOLExact, hA, hB, progIfHOLExact]
      refine survives_nested_seq_append n _ _ (survives_nested_seq_append n _ _ iha ihb) ?_
      simp only [holLoopNestedSeq, survivesHOLExact, Bool.true_and, Bool.and_true]
      exact sptListInsert_mono n _ _ hdom2
  | .shift o a b, n, h => by
      have iha := compileExpHOLExact_survives ct tmp l a n h
      have hdom := compileExpHOLExact_domain_mono ct tmp l a n h
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha hdom; simp only at iha hdom
      have ihb := compileExpHOLExact_survives ct m ol b n hdom
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb; simp only at ihb
      simp only [compileExpHOLExact, hA, hB]
      exact survives_nested_seq_append n _ _ iha ihb
termination_by e => sizeOf e

theorem compileExpsHOLExact_survives (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ (es : List (CrepExpHOL width)) (n : Nat), (sptLookup n l).isSome = true →
      survivesHOLExact n (holLoopNestedSeq (compileExpsHOLExact ct tmp l es).1) = true
  | [], n, _ => by simp [compileExpsHOLExact, holLoopNestedSeq, survivesHOLExact]
  | e :: es, n, h => by
      have iha := compileExpHOLExact_survives ct tmp l e n h
      have hdom := compileExpHOLExact_domain_mono ct tmp l e n h
      rcases hA : compileExpHOLExact ct tmp l e with ⟨c, v, m, ol⟩
      rw [hA] at iha hdom; simp only at iha hdom
      have ihb := compileExpsHOLExact_survives ct m ol es n hdom
      rcases hB : compileExpsHOLExact ct m ol es with ⟨c', vs', m', ol'⟩
      rw [hB] at ihb; simp only at ihb
      simp only [compileExpsHOLExact, hA, hB]
      exact survives_nested_seq_append n _ _ iha ihb
termination_by es => sizeOf es
end

namespace CrepToLoopCompExpSurvivesWitnesses

/-- Same-module re-export of the canonical finite-support witness for the
    `crep_to_loop$context` carrier, required by the `fmap_as_finite_support`
    qualifier on the ports below. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopCompExpSurvivesWitnesses

/-- Exact HOL `member_cutset_survives_comp_exp_cases` (`crep_to_loopProofScript.sml:1321-1329`);
    `n ∈ domain l` is `(sptLookup n l).isSome`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_exp_cases"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem member_cutset_survives_comp_exp_cases :
    (∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet) (n : Nat),
      (sptLookup n l).isSome = true ∧ compileExpHOLExact ct tmp l e = (p, le, ntmp, nl) → survivesHOLExact n (holLoopNestedSeq p) = true) ∧
    (∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (le : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet)
      (n : Nat),
      (sptLookup n l).isSome = true ∧ compileExpsHOLExact ct tmp l e = (p, le, ntmp, nl) → survivesHOLExact n (holLoopNestedSeq p) = true) :=
  ⟨fun ct tmp l e p le ntmp nl n ⟨hn, h⟩ => by
      have := compileExpHOLExact_survives ct tmp l e n hn; rw [h] at this; exact this,
   fun ct tmp l e p le ntmp nl n ⟨hn, h⟩ => by
      have := compileExpsHOLExact_survives ct tmp l e n hn; rw [h] at this; exact this⟩

/-- Exact HOL `member_cutset_survives_comp_exp` (`crep_to_loopProofScript.sml:1426`, `CONJUNCT1`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_exp"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem member_cutset_survives_comp_exp :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet) (n : Nat),
      (sptLookup n l).isSome = true ∧ compileExpHOLExact ct tmp l e = (p, le, ntmp, nl) → survivesHOLExact n (holLoopNestedSeq p) = true :=
  member_cutset_survives_comp_exp_cases.1

/-- Exact HOL `member_cutset_survives_comp_exps` (`crep_to_loopProofScript.sml:1428`, `CONJUNCT2`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_exps"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem member_cutset_survives_comp_exps :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (le : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet)
      (n : Nat),
      (sptLookup n l).isSome = true ∧ compileExpsHOLExact ct tmp l e = (p, le, ntmp, nl) → survivesHOLExact n (holLoopNestedSeq p) = true :=
  member_cutset_survives_comp_exp_cases.2

/-- Exact HOL `member_cutset_survives_comp_exp_flip` (`crep_to_loopProofScript.sml:1432-1433`,
    `[local]`, `ONCE_REWRITE_RULE [CONJ_COMM]`: the two premise conjuncts swapped). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_exp_flip"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem member_cutset_survives_comp_exp_flip :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet) (n : Nat),
      compileExpHOLExact ct tmp l e = (p, le, ntmp, nl) ∧ (sptLookup n l).isSome = true → survivesHOLExact n (holLoopNestedSeq p) = true :=
  fun ct tmp l e p le ntmp nl n ⟨h, hn⟩ => member_cutset_survives_comp_exp ct tmp l e p le ntmp nl n ⟨hn, h⟩

/-- Exact HOL `member_cutset_survives_comp_exps_flip` (`crep_to_loopProofScript.sml:1434-1435`,
    `[local]`, premise conjuncts swapped). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_exps_flip"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem member_cutset_survives_comp_exps_flip :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (le : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet)
      (n : Nat),
      compileExpsHOLExact ct tmp l e = (p, le, ntmp, nl) ∧ (sptLookup n l).isSome = true → survivesHOLExact n (holLoopNestedSeq p) = true :=
  fun ct tmp l e p le ntmp nl n ⟨h, hn⟩ => member_cutset_survives_comp_exps ct tmp l e p le ntmp nl n ⟨hn, h⟩

theorem survives_zipWith_assign (n : Nat) :
    ∀ (names : List Nat) (values : List (HolLoopExp width)),
      survivesHOLExact n (holLoopNestedSeq (List.zipWith HolLoopProg.assign names values)) = true
  | [], _ => by simp [holLoopNestedSeq, survivesHOLExact]
  | _ :: _, [] => by simp [holLoopNestedSeq, survivesHOLExact]
  | x :: xs, v :: vs => by
      simp only [List.zipWith_cons_cons, holLoopNestedSeq, survivesHOLExact, Bool.true_and]
      exact survives_zipWith_assign n xs vs

theorem compileHOLExact_survives :
    ∀ (ctxt : CrepToLoopContextExact) (l : NumSet) (p : CrepProgHOL width) (n : Nat),
      (sptLookup n l).isSome = true → survivesHOLExact n (compileHOLExact ctxt l p) = true
  | ctxt, l, .skip, n, _ | ctxt, l, .break _, n, _ | ctxt, l, .continue _, n, _
  | ctxt, l, .tick, n, _ | ctxt, l, .raise _, n, _ => by
      simp [compileHOLExact, survivesHOLExact]
  | ctxt, l, .primitive ds o as, n, _ => by
      simp only [compileHOLExact]; split <;> simp [survivesHOLExact]
  | ctxt, l, .extCall f c cl a al, n, h => by
      simp only [compileHOLExact]; split <;> simp [survivesHOLExact, h]
  | ctxt, l, .return es, n, h => by
      have hc := compileExpsHOLExact_survives ctxt (ctxt.vmax + 1) l es n h
      rcases hA : compileExpsHOLExact ctxt (ctxt.vmax + 1) l es with ⟨c, vs, t, o⟩
      rw [hA] at hc; simp only at hc
      simp only [compileHOLExact, hA, loopNestedSeqHOL_eq_holLoopNestedSeq]
      exact survives_nested_seq_append n _ _ (survives_nested_seq_append n _ _ hc
        (survives_zipWith_assign n _ _)) (by simp [holLoopNestedSeq, survivesHOLExact])
  | ctxt, l, .shMem o nm a, n, h => by
      simp only [compileHOLExact]
      split
      · simp [survivesHOLExact]
      · have hc := compileExpHOLExact_survives ctxt (ctxt.vmax + 1) l a n h
        rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l a with ⟨c, v, t, o⟩
        rw [hA] at hc; simp only at hc
        simp only [loopNestedSeqHOL_eq_holLoopNestedSeq]
        exact survives_nested_seq_append n _ _ hc (by simp [holLoopNestedSeq, survivesHOLExact])
  | ctxt, l, .store d v, n, h | ctxt, l, .store32 d v, n, h | ctxt, l, .storeByte d v, n, h => by
      have hc := compileExpHOLExact_survives ctxt (ctxt.vmax + 1) l d n h
      have hdom := compileExpHOLExact_domain_mono ctxt (ctxt.vmax + 1) l d n h
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l d with ⟨c, a, t, o⟩
      rw [hA] at hc hdom; simp only at hc hdom
      have hc2 := compileExpHOLExact_survives ctxt t o v n hdom
      rcases hB : compileExpHOLExact ctxt t o v with ⟨c', v', t', o'⟩
      rw [hB] at hc2; simp only at hc2
      simp only [compileHOLExact, hA, hB, loopNestedSeqHOL_eq_holLoopNestedSeq]
      exact survives_nested_seq_append n _ _ (survives_nested_seq_append n _ _ hc hc2)
        (by simp [holLoopNestedSeq, survivesHOLExact])
  | ctxt, l, .storeGlob g v, n, h => by
      have hc := compileExpHOLExact_survives ctxt (ctxt.vmax + 1) l v n h
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l v with ⟨c, v', t, o⟩
      rw [hA] at hc; simp only at hc
      simp only [compileHOLExact, hA, loopNestedSeqHOL_eq_holLoopNestedSeq]
      exact survives_nested_seq_append n _ _ hc (by simp [holLoopNestedSeq, survivesHOLExact])
  | ctxt, l, .assign nm v, n, h => by
      simp only [compileHOLExact]
      split
      · simp [survivesHOLExact]
      · have hc := compileExpHOLExact_survives ctxt (ctxt.vmax + 1) l v n h
        rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l v with ⟨c, v', t, o⟩
        rw [hA] at hc; simp only at hc
        simp only [loopNestedSeqHOL_eq_holLoopNestedSeq]
        exact survives_nested_seq_append n _ _ hc (by simp [holLoopNestedSeq, survivesHOLExact])
  | ctxt, l, .seq p1 p2, n, h => by
      simp only [compileHOLExact, survivesHOLExact, Bool.and_eq_true]
      exact ⟨compileHOLExact_survives ctxt l p1 n h, compileHOLExact_survives ctxt l p2 n h⟩
  | ctxt, l, .dec nm v body, n, h => by
      have hc := compileExpHOLExact_survives ctxt (ctxt.vmax + 1) l v n h
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l v with ⟨c, v', t, o⟩
      rw [hA] at hc; simp only at hc
      simp only [compileHOLExact, hA, survivesHOLExact, Bool.and_eq_true, Bool.true_and,
        loopNestedSeqHOL_eq_holLoopNestedSeq]
      refine ⟨hc, compileHOLExact_survives _ _ body n ?_⟩
      rw [sptLookup_sptInsert]; split <;> simp_all
  | ctxt, l, .ite c p1 p2, n, h => by
      have hc := compileExpHOLExact_survives ctxt (ctxt.vmax + 1) l c n h
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l c with ⟨cc, v', t, o⟩
      rw [hA] at hc; simp only at hc
      simp only [compileHOLExact, hA, loopNestedSeqHOL_eq_holLoopNestedSeq]
      refine survives_nested_seq_append n _ _ hc ?_
      simp only [holLoopNestedSeq, survivesHOLExact, Bool.true_and, Bool.and_true,
        Bool.and_eq_true]
      exact ⟨⟨compileHOLExact_survives ctxt l p1 n h, compileHOLExact_survives ctxt l p2 n h⟩, h⟩
  | ctxt, l, .while c body, n, h => by
      have hc := compileExpHOLExact_survives ctxt (ctxt.vmax + 1) l c n h
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l c with ⟨cc, v', t, o⟩
      rw [hA] at hc; simp only at hc
      simp only [compileHOLExact, hA, loopNestedSeqHOL_eq_holLoopNestedSeq, survivesHOLExact,
        Bool.and_eq_true]
      have hb := compileHOLExact_survives ctxt l body n h
      refine ⟨⟨h, h⟩, survives_nested_seq_append n _ _ hc ?_⟩
      simp_all [holLoopNestedSeq, survivesHOLExact]
  | ctxt, l, .call ri nm args, n, h => by
      have hc := compileExpsHOLExact_survives ctxt (ctxt.vmax + 1) l args n h
      rcases hA : compileExpsHOLExact ctxt (ctxt.vmax + 1) l args with ⟨cc, vs, t, o⟩
      rw [hA] at hc; simp only at hc
      rw [compileHOLExact.eq_def]
      simp only [hA, loopNestedSeqHOL_eq_holLoopNestedSeq]
      refine survives_nested_seq_append n _ _
        (survives_nested_seq_append n _ _ hc (survives_zipWith_assign n _ _)) ?_
      cases ri with
      | none => simp [holLoopNestedSeq, survivesHOLExact]
      | some rh =>
        obtain ⟨rv, mh⟩ := rh
        cases mh with
        | none => simp [holLoopNestedSeq, survivesHOLExact, h]
        | some eh =>
          obtain ⟨ex, hp⟩ := eh
          have hh := compileHOLExact_survives ctxt l hp n h
          simp_all [holLoopNestedSeq, survivesHOLExact]
termination_by _ _ p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepProgHOL.dec.sizeOf_spec, CrepProgHOL.seq.sizeOf_spec,
        CrepProgHOL.ite.sizeOf_spec, CrepProgHOL.while.sizeOf_spec,
        CrepProgHOL.call.sizeOf_spec]; omega)

/-- Exact HOL `member_cutset_survives_comp_prog` (`crep_to_loopProofScript.sml:1439-1442`):
    `!ctxt l p n. n ∈ domain l ==> survives n (compile ctxt l p)`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "member_cutset_survives_comp_prog"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem member_cutset_survives_comp_prog :
    ∀ (ctxt : CrepToLoopContextExact) (l : NumSet) (p : CrepProgHOL width) (n : Nat),
      (sptLookup n l).isSome = true → survivesHOLExact n (compileHOLExact ctxt l p) = true :=
  compileHOLExact_survives

end Flapjack
