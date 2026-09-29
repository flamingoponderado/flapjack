import Flapjack.Pancake.CrepToLoop.Proofs.CompExpTmpBound
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.Semantics.LoopProps.CutSets

/-!
# crep_to_loopProof syntactic `compile_exp` helper lemmas

Counterparts of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`not_mem_assigned_mem_gt_comp_exp_cases` (1466) and its projections (1557/1559),
`assigned_vars_nested_seq_assign` (1562), `cut_sets_MAPi_Assign` (342) and
`compile_exps_alt` (394) over the exact carriers (bead `flapjack-pxn.18.5.6.33.5`).
-/

namespace Flapjack

variable {width : Nat} [NeZero width]

namespace CrepToLoopCompExpSyntaxWitnesses

/-- Same-module re-export of the canonical finite-support witness for the
    `crep_to_loop$context` carrier, required by the `fmap_as_finite_support`
    qualifier on the context-quantified ports below. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopCompExpSyntaxWitnesses

/-- Exact HOL `not_mem_assigned_mem_gt_comp_exp_cases`
    (`crep_to_loopProofScript.sml:1466-1476`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "not_mem_assigned_mem_gt_comp_exp_cases"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem not_mem_assigned_mem_gt_comp_exp_cases :
    (∀ (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet) (n : Nat),
      compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
      crepToLoopCtxtMaxExact ctxt.vmax ctxt.vars ∧
      (∀ v m, ctxt.vars.lookup v = some m → n ≠ m) ∧ n < tmp →
      n ∉ holLoopAssignedVars (loopNestedSeqHOL p)) ∧
    (∀ (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (le : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet)
      (n : Nat),
      compileExpsHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
      crepToLoopCtxtMaxExact ctxt.vmax ctxt.vars ∧
      (∀ v m, ctxt.vars.lookup v = some m → n ≠ m) ∧ n < tmp →
      n ∉ holLoopAssignedVars (loopNestedSeqHOL p)) :=
  ⟨fun ctxt tmp l e p le ntmp nl n ⟨h, _, _, hn⟩ hm => by
      have := (comp_exp_assigned_vars_tmp_bound ctxt tmp l e p le ntmp nl n ⟨h, hm⟩).1; omega,
   fun ctxt tmp l e p le ntmp nl n ⟨h, _, _, hn⟩ hm => by
      have := (comp_exps_assigned_vars_tmp_bound ctxt tmp l e p le ntmp nl n ⟨h, hm⟩).1; omega⟩

/-- Exact HOL `not_mem_assigned_mem_gt_comp_exp` (`crep_to_loopProofScript.sml:1557`,
    `CONJUNCT1`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "not_mem_assigned_mem_gt_comp_exp"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem not_mem_assigned_mem_gt_comp_exp :
    ∀ (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet) (n : Nat),
      compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
      crepToLoopCtxtMaxExact ctxt.vmax ctxt.vars ∧
      (∀ v m, ctxt.vars.lookup v = some m → n ≠ m) ∧ n < tmp →
      n ∉ holLoopAssignedVars (loopNestedSeqHOL p) :=
  not_mem_assigned_mem_gt_comp_exp_cases.1

/-- Exact HOL `not_mem_assigned_mem_gt_comp_exps` (`crep_to_loopProofScript.sml:1559`,
    `CONJUNCT2`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "not_mem_assigned_mem_gt_comp_exps"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem not_mem_assigned_mem_gt_comp_exps :
    ∀ (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (le : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet)
      (n : Nat),
      compileExpsHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
      crepToLoopCtxtMaxExact ctxt.vmax ctxt.vars ∧
      (∀ v m, ctxt.vars.lookup v = some m → n ≠ m) ∧ n < tmp →
      n ∉ holLoopAssignedVars (loopNestedSeqHOL p) :=
  not_mem_assigned_mem_gt_comp_exp_cases.2

/-- Exact HOL `assigned_vars_nested_seq_assign` (`crep_to_loopProofScript.sml:1562-1564`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "assigned_vars_nested_seq_assign"
  (words_as_type_indexed_bitvec)]
theorem assigned_vars_nested_seq_assign :
    ∀ (vs : List Nat) (es : List (HolLoopExp width)), vs.length = es.length →
      holLoopAssignedVars (loopNestedSeqHOL (List.zipWith HolLoopProg.assign vs es)) = vs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | v :: vs, e :: es, h => by
      simp only [List.zipWith_cons_cons, loopNestedSeqHOL, holLoopAssignedVars, List.singleton_append]
      rw [assigned_vars_nested_seq_assign vs es (by simpa using h)]

/-- Exact HOL `cut_sets_MAPi_Assign` (`crep_to_loopProofScript.sml:342-345`):
    `cut_sets cs (nested_seq (MAPi (λn. Assign (n + offset)) les)) =
      list_insert (GENLIST ($+ offset) (LENGTH les)) cs`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "cut_sets_MAPi_Assign"
  (words_as_type_indexed_bitvec)]
theorem cut_sets_MAPi_Assign :
    ∀ (les : List (HolLoopExp width)) (cs : NumSet) (offset : Nat),
      cutSetsHOL cs (loopNestedSeqHOL
        (les.mapIdx (fun n e => HolLoopProg.assign (n + offset) e))) =
      sptListInsert ((List.range les.length).map (offset + ·)) cs
  | [], cs, offset => by simp [loopNestedSeqHOL, cutSetsHOL, sptListInsert]
  | e :: es, cs, offset => by
      simp only [List.mapIdx_cons, loopNestedSeqHOL, cutSetsHOL, List.length_cons,
        List.range_succ_eq_map, List.map_cons, List.map_map, sptListInsert]
      have ih := cut_sets_MAPi_Assign es (sptInsert (0 + offset) () cs) (offset + 1)
      have hf : (fun n e => HolLoopProg.assign (n + 1 + offset) e) =
          (fun n e => HolLoopProg.assign (n + (offset + 1)) (width := width) e) := by
        funext n e; congr 1; omega
      have hg : ((offset + ·) ∘ Nat.succ) = ((offset + 1) + ·) := by
        funext n; simp only [Function.comp]; omega
      rw [hf, ih, hg]; simp

/-- Exact HOL `compile_exps_alt` (`crep_to_loopProofScript.sml:394-402`): the two
    defining equations of the list half of `compile_exp_def`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exps_alt"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem compile_exps_alt (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (e : CrepExpHOL width) (es : List (CrepExpHOL width)) :
    compileExpsHOLExact ctxt tmp l [] =
      (([] : List (HolLoopProg width)), ([] : List (HolLoopExp width)), tmp, l) ∧
    compileExpsHOLExact ctxt tmp l (e :: es) =
      (let (p, le, tmp', l') := compileExpHOLExact ctxt tmp l e
       let (p1, les, tmp'', l'') := compileExpsHOLExact ctxt tmp' l' es
       (p ++ p1, le :: les, tmp'', l'')) := by
  constructor
  · simp [compileExpsHOLExact]
  · rw [compileExpsHOLExact]

end Flapjack
