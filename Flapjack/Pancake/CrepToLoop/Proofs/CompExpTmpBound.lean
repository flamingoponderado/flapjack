import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.Semantics.LoopProps.AssignedVars

/-!
# crep_to_loop `comp_exp_assigned_vars_tmp_bound`

Counterpart of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`comp_exp_assigned_vars_tmp_bound_cases` (line 593) and its two projections
(679-680) over the exact `compileExpHOLExact`/`compileExpsHOLExact`,
`holLoopAssignedVars` and `loopNestedSeqHOL` (bead `flapjack-pxn.18.5.6.32.1`).
-/

namespace Flapjack

variable {width : Nat} [NeZero width]

theorem compileCrepopHOLExact_tmp (operator : CrepOp) (target : Compiler.Encoders.Asm.AsmArchitecture)
    (left right tmp : Nat) (live : NumSet) :
    tmp ≤ (compileCrepopHOLExact (width := width) operator target left right tmp live).2 ∧
      (compileCrepopHOLExact (width := width) operator target left right tmp live).2 ≤ tmp + 1 := by
  cases operator; simp only [compileCrepopHOLExact]; split <;> simp

mutual
/-- The temporary counter of the exact `compile_exp` never decreases (the
    `tmp <= ntmp` conjunct of HOL `compile_exp_out_rel_cases`, which also
    asserts `comp_syntax_ok`; this is the part needed here, proved directly).
    Flapjack-only helper, no tag. -/
theorem compileExpHOLExact_tmp_le (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ e : CrepExpHOL width, tmp ≤ (compileExpHOLExact ct tmp l e).2.2.1
  | .baseAddr | .topAddr | .const _ | .var _ | .loadGlob _ => by simp [compileExpHOLExact]
  | .load a => by
      have h1 := compileExpHOLExact_tmp_le ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, n, o⟩
      rw [hA] at h1; simp only at h1; simp only [compileExpHOLExact, hA]; exact h1
  | .load32 a => by
      have h1 := compileExpHOLExact_tmp_le ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, n, o⟩
      rw [hA] at h1; simp only at h1; simp only [compileExpHOLExact, hA]; omega
  | .loadByte a => by
      have h1 := compileExpHOLExact_tmp_le ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, n, o⟩
      rw [hA] at h1; simp only at h1; simp only [compileExpHOLExact, hA]; omega
  | .op o es => by
      have h1 := compileExpsHOLExact_tmp_le ct tmp l es
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, v, n, ol⟩
      rw [hA] at h1; simp only at h1; simp only [compileExpHOLExact, hA]; exact h1
  | .crepOp o es => by
      have h1 := compileExpsHOLExact_tmp_le ct tmp l es
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, n, ol⟩
      rw [hA] at h1; simp only at h1
      simp only [compileExpHOLExact, hA]
      rcases hB : compileCrepopHOLExact (width := width) o ct.target n (n + 1) (n + vs.length)
        (sptListInsert ((List.range vs.length).map (fun offset => n + offset)) ol) with ⟨oc, d⟩
      have h2 := compileCrepopHOLExact_tmp (width := width) o ct.target n (n + 1) (n + vs.length)
        (sptListInsert ((List.range vs.length).map (fun offset => n + offset)) ol)
      rw [hB] at h2; simp only at h2
      simp only
      omega
  | .cmp o a b => by
      have h1 := compileExpHOLExact_tmp_le ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, n, ol⟩
      rw [hA] at h1; simp only at h1
      have h2 := compileExpHOLExact_tmp_le ct n ol b
      rcases hB : compileExpHOLExact ct n ol b with ⟨c', v', n', ol'⟩
      rw [hB] at h2; simp only at h2
      simp only [compileExpHOLExact, hA, hB]; omega
  | .shift o a b => by
      have h1 := compileExpHOLExact_tmp_le ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, n, ol⟩
      rw [hA] at h1; simp only at h1
      have h2 := compileExpHOLExact_tmp_le ct n ol b
      rcases hB : compileExpHOLExact ct n ol b with ⟨c', v', n', ol'⟩
      rw [hB] at h2; simp only at h2
      simp only [compileExpHOLExact, hA, hB]; omega
termination_by e => sizeOf e

theorem compileExpsHOLExact_tmp_le (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ es : List (CrepExpHOL width), tmp ≤ (compileExpsHOLExact ct tmp l es).2.2.1
  | [] => by simp [compileExpsHOLExact]
  | e :: es => by
      have h1 := compileExpHOLExact_tmp_le ct tmp l e
      rcases hA : compileExpHOLExact ct tmp l e with ⟨c, v, n, ol⟩
      rw [hA] at h1; simp only at h1
      have h2 := compileExpsHOLExact_tmp_le ct n ol es
      rcases hB : compileExpsHOLExact ct n ol es with ⟨c', v', n', ol'⟩
      rw [hB] at h2; simp only at h2
      simp only [compileExpsHOLExact, hA, hB]; omega
termination_by es => sizeOf es
end

theorem zipAssign_assigned (k : Nat) :
    ∀ (is : List Nat) (vs : List (HolLoopExp width)) (x : Nat),
      x ∈ holLoopAssignedVars (loopNestedSeqHOL
        (List.zipWith (fun i v => HolLoopProg.assign (k + i) v) is vs)) → ∃ i ∈ is, x = k + i
  | [], _, x, h => by simp [loopNestedSeqHOL, holLoopAssignedVars] at h
  | _ :: _, [], x, h => by simp [loopNestedSeqHOL, holLoopAssignedVars] at h
  | i :: is, v :: vs, x, h => by
      simp only [List.zipWith_cons_cons, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact ⟨i, List.mem_cons_self, h⟩
      · obtain ⟨j, hj, rfl⟩ := zipAssign_assigned k is vs x h
        exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩

mutual
theorem compileExpHOLExact_assigned_bound (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ (e : CrepExpHOL width) (n : Nat),
      n ∈ holLoopAssignedVars (loopNestedSeqHOL (compileExpHOLExact ct tmp l e).1) →
      tmp ≤ n ∧ n < (compileExpHOLExact ct tmp l e).2.2.1
  | .baseAddr, n, h | .topAddr, n, h | .const _, n, h | .var _, n, h | .loadGlob _, n, h => by
      simp [compileExpHOLExact, loopNestedSeqHOL, holLoopAssignedVars] at h
  | .load a, n, h => by
      have ih := compileExpHOLExact_assigned_bound ct tmp l a n
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp only at ih
      simp only [compileExpHOLExact, hA] at h ⊢; exact ih h
  | .load32 a, n, h | .loadByte a, n, h => by
      have ih := compileExpHOLExact_assigned_bound ct tmp l a n
      have hle := compileExpHOLExact_tmp_le ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih hle; simp only at ih hle
      simp only [compileExpHOLExact, hA, holAssignedVarsNestedSeqSplit, loopNestedSeqHOL,
        holLoopAssignedVars, List.mem_append, List.mem_singleton, List.append_nil] at h ⊢
      rcases h with h | h | h
      · have := ih h; omega
      · omega
      · omega
  | .op o es, n, h => by
      have ih := compileExpsHOLExact_assigned_bound ct tmp l es n
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp only at ih
      simp only [compileExpHOLExact, hA] at h ⊢; exact ih h
  | .crepOp o es, n, h => by
      have ih := compileExpsHOLExact_assigned_bound ct tmp l es n
      have hle := compileExpsHOLExact_tmp_le ct tmp l es
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih hle; simp only at ih hle
      simp only [compileExpHOLExact, hA] at h ⊢
      rcases hB : compileCrepopHOLExact (width := width) o ct.target m (m + 1) (m + vs.length)
        (sptListInsert ((List.range vs.length).map (fun offset => m + offset)) ol) with ⟨oc, d⟩
      have hd := compileCrepopHOLExact_tmp (width := width) o ct.target m (m + 1) (m + vs.length)
        (sptListInsert ((List.range vs.length).map (fun offset => m + offset)) ol)
      rw [hB] at hd; simp only at hd
      rw [hB] at h; simp only at h ⊢
      simp only [holAssignedVarsNestedSeqSplit, List.mem_append] at h
      rcases h with (h | h) | h
      · have := ih h; omega
      · obtain ⟨i, hi, rfl⟩ := zipAssign_assigned m _ _ n h
        simp only [List.mem_range] at hi; omega
      · have hoc : ∀ x ∈ holLoopAssignedVars (loopNestedSeqHOL oc), m + vs.length ≤ x ∧ x ≤ d := by
          cases o
          simp only [compileCrepopHOLExact] at hB
          split at hB <;> (simp only [Prod.mk.injEq] at hB; obtain ⟨rfl, rfl⟩ := hB) <;>
            simp [loopNestedSeqHOL, holLoopAssignedVars] <;> omega
        have := hoc n h; omega
  | .cmp o a b, n, h => by
      have iha := compileExpHOLExact_assigned_bound ct tmp l a n
      have hla := compileExpHOLExact_tmp_le ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha hla; simp only at iha hla
      have ihb := compileExpHOLExact_assigned_bound ct m ol b n
      have hlb := compileExpHOLExact_tmp_le ct m ol b
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb hlb; simp only at ihb hlb
      simp only [compileExpHOLExact, hA, hB, progIfHOLExact, holAssignedVarsNestedSeqSplit,
        loopNestedSeqHOL, holLoopAssignedVars, List.mem_append, List.mem_singleton,
        List.append_nil] at h ⊢
      rcases h with ((h | h) | h | h | h | h)
      · have := iha h; omega
      · have := ihb h; omega
      all_goals omega
  | .shift o a b, n, h => by
      have iha := compileExpHOLExact_assigned_bound ct tmp l a n
      have hla := compileExpHOLExact_tmp_le ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha hla; simp only at iha hla
      have ihb := compileExpHOLExact_assigned_bound ct m ol b n
      have hlb := compileExpHOLExact_tmp_le ct m ol b
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb hlb; simp only at ihb hlb
      simp only [compileExpHOLExact, hA, hB, holAssignedVarsNestedSeqSplit, List.mem_append] at h ⊢
      rcases h with h | h
      · have := iha h; omega
      · have := ihb h; omega
termination_by e => sizeOf e

theorem compileExpsHOLExact_assigned_bound (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ (es : List (CrepExpHOL width)) (n : Nat),
      n ∈ holLoopAssignedVars (loopNestedSeqHOL (compileExpsHOLExact ct tmp l es).1) →
      tmp ≤ n ∧ n < (compileExpsHOLExact ct tmp l es).2.2.1
  | [], n, h => by simp [compileExpsHOLExact, loopNestedSeqHOL, holLoopAssignedVars] at h
  | e :: es, n, h => by
      have iha := compileExpHOLExact_assigned_bound ct tmp l e n
      have hla := compileExpHOLExact_tmp_le ct tmp l e
      rcases hA : compileExpHOLExact ct tmp l e with ⟨c, v, m, ol⟩
      rw [hA] at iha hla; simp only at iha hla
      have ihb := compileExpsHOLExact_assigned_bound ct m ol es n
      have hlb := compileExpsHOLExact_tmp_le ct m ol es
      rcases hB : compileExpsHOLExact ct m ol es with ⟨c', v', m', ol'⟩
      rw [hB] at ihb hlb; simp only at ihb hlb
      simp only [compileExpsHOLExact, hA, hB, holAssignedVarsNestedSeqSplit, List.mem_append] at h ⊢
      rcases h with h | h
      · have := iha h; omega
      · have := ihb h; omega
termination_by es => sizeOf es
end

namespace CrepToLoopCompExpTmpBoundWitnesses

/-- Same-module re-export of the canonical finite-support witness for the
    `crep_to_loop$context` carrier, required by the `fmap_as_finite_support`
    qualifier on the `comp_exp_assigned_vars_tmp_bound` ports below. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopCompExpTmpBoundWitnesses

/-- Exact HOL `comp_exp_assigned_vars_tmp_bound_cases`
    (`crep_to_loopProofScript.sml:593-599`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_assigned_vars_tmp_bound_cases"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem comp_exp_assigned_vars_tmp_bound_cases :
    (∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet) (n : Nat),
      compileExpHOLExact ct tmp l e = (p, le, ntmp, nl) ∧
        n ∈ holLoopAssignedVars (loopNestedSeqHOL p) → tmp ≤ n ∧ n < ntmp) ∧
    (∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (le : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet)
      (n : Nat),
      compileExpsHOLExact ct tmp l e = (p, le, ntmp, nl) ∧
        n ∈ holLoopAssignedVars (loopNestedSeqHOL p) → tmp ≤ n ∧ n < ntmp) :=
  ⟨fun ct tmp l e p le ntmp nl n ⟨h, hn⟩ => by
      have := compileExpHOLExact_assigned_bound ct tmp l e n; rw [h] at this; exact this hn,
   fun ct tmp l e p le ntmp nl n ⟨h, hn⟩ => by
      have := compileExpsHOLExact_assigned_bound ct tmp l e n; rw [h] at this; exact this hn⟩

/-- Exact HOL `comp_exp_assigned_vars_tmp_bound`
    (`crep_to_loopProofScript.sml:679`, `CONJUNCT1` of the cases theorem). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_assigned_vars_tmp_bound"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem comp_exp_assigned_vars_tmp_bound :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet) (n : Nat),
      compileExpHOLExact ct tmp l e = (p, le, ntmp, nl) ∧
        n ∈ holLoopAssignedVars (loopNestedSeqHOL p) → tmp ≤ n ∧ n < ntmp :=
  comp_exp_assigned_vars_tmp_bound_cases.1

/-- Exact HOL `comp_exps_assigned_vars_tmp_bound`
    (`crep_to_loopProofScript.sml:680`, `CONJUNCT2` of the cases theorem). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exps_assigned_vars_tmp_bound"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem comp_exps_assigned_vars_tmp_bound :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (le : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet)
      (n : Nat),
      compileExpsHOLExact ct tmp l e = (p, le, ntmp, nl) ∧
        n ∈ holLoopAssignedVars (loopNestedSeqHOL p) → tmp ≤ n ∧ n < ntmp :=
  comp_exp_assigned_vars_tmp_bound_cases.2

end Flapjack
