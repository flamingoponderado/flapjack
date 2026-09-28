import Flapjack.Pancake.CrepToLoop.Proofs.CompExpSyntaxHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpOutRel
import Flapjack.Pancake.Semantics.LoopProps.AssignedVars

/-!
# crep_to_loop `not_mem_context_assigned_mem_gt` over the exact carriers

Exact port of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`not_mem_context_assigned_mem_gt` (1570) over `CrepToLoopContextExact`, the
tagged `compileHOLExact` (`compile_def`) and `holLoopAssignedVars`
(`assigned_vars_def`) (bead `flapjack-pxn.18.5.6.33.19`).  HOL proves it by
`compile_ind`; the Lean proof is the matching well-founded recursion on the
source program.
-/

namespace Flapjack

namespace CrepToLoopNotMemContextAssignedWitnesses

/-- Same-module re-export of the canonical `crep_to_loop$context` witness. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopNotMemContextAssignedWitnesses

variable {width : Nat} [NeZero width]

private theorem mapM_some_mem_image {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ y ∈ ys, ∃ x, f x = some y
  | [], ys, h, y, hy => by simp at h; subst h; simp at hy
  | a :: as, ys, h, y, hy => by
      simp only [List.mapM_cons] at h
      cases ha : f a with
      | none => simp [ha] at h
      | some b =>
        cases has : as.mapM f with
        | none => simp [ha, has] at h
        | some bs =>
          simp [ha, has] at h
          subst h
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨a, ha⟩
          · exact mapM_some_mem_image f as bs has y hy

private theorem mem_genTemps {n k m : Nat} (h : m ∈ genTemps n k) : n ≤ m := by
  simp only [genTemps, List.mem_map, List.mem_range] at h
  obtain ⟨x, _, rfl⟩ := h
  omega

private theorem not_mem_context_assigned_aux :
    ∀ (ctxt : CrepToLoopContextExact) (l : NumSet) (p : CrepProgHOL width) (n : Nat),
      crepToLoopCtxtMax ctxt.vmax ctxt.vars.lookup →
      (∀ v m, ctxt.vars.lookup v = some m → n ≠ m) → n ≤ ctxt.vmax →
      n ∉ holLoopAssignedVars (compileHOLExact ctxt l p)
  | ctxt, l, .skip, n, _, _, _ => by simp [compileHOLExact, holLoopAssignedVars]
  | ctxt, l, .break _, n, _, _, _ => by simp [compileHOLExact, holLoopAssignedVars]
  | ctxt, l, .continue _, n, _, _, _ => by simp [compileHOLExact, holLoopAssignedVars]
  | ctxt, l, .tick, n, _, _, _ => by simp [compileHOLExact, holLoopAssignedVars]
  | ctxt, l, .raise _, n, _, _, hn => by
      simp [compileHOLExact, holLoopAssignedVars]; omega
  | ctxt, l, .extCall _ _ _ _ _, n, _, _, _ => by
      rw [compileHOLExact]; split <;> simp [holLoopAssignedVars]
  | ctxt, l, .primitive dests _ args, n, _, hne, _ => by
      rw [compileHOLExact]
      split
      · rename_i md ma hd _
        simp only [holLoopAssignedVars]
        intro hm
        obtain ⟨v, hv⟩ := mapM_some_mem_image _ dests md hd n hm
        exact hne v n hv rfl
      · simp [holLoopAssignedVars]
  | ctxt, l, .assign name value, n, hmax, hne, hn => by
      rw [compileHOLExact]
      split
      · simp [holLoopAssignedVars]
      · rename_i m hm
        rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l value with ⟨c, v, t, o⟩
        simp only [holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨not_mem_assigned_mem_gt_comp_exp ctxt _ l value c v t o n
          ⟨hA, hmax, hne, by omega⟩, hne name m hm⟩
  | ctxt, l, .shMem _ name address, n, hmax, hne, hn => by
      rw [compileHOLExact]
      split
      · simp [holLoopAssignedVars]
      · rename_i m hm
        rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l address with ⟨c, v, t, o⟩
        simp only [holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨not_mem_assigned_mem_gt_comp_exp ctxt _ l address c v t o n
          ⟨hA, hmax, hne, by omega⟩, hne name m hm⟩
  | ctxt, l, .storeGlob _ value, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l value with ⟨c, v, t, o⟩
      simp only [holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.not_mem_nil, or_false]
      exact not_mem_assigned_mem_gt_comp_exp ctxt _ l value c v t o n ⟨hA, hmax, hne, by omega⟩
  | ctxt, l, .store dst src, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l dst with ⟨c1, a, t1, o1⟩
      rcases hB : compileExpHOLExact ctxt t1 o1 src with ⟨c2, v, t2, o2⟩
      have hA1 := (compile_exp_out_rel ctxt _ l dst c1 a t1 o1 hA).2.1
      have hB1 := (compile_exp_out_rel ctxt t1 o1 src c2 v t2 o2 hB).2.1
      simp only [hB, holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨not_mem_assigned_mem_gt_comp_exp ctxt _ l dst c1 a t1 o1 n ⟨hA, hmax, hne, by omega⟩,
        not_mem_assigned_mem_gt_comp_exp ctxt t1 o1 src c2 v t2 o2 n ⟨hB, hmax, hne, by omega⟩⟩,
        by omega⟩
  | ctxt, l, .store32 dst src, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l dst with ⟨c1, a, t1, o1⟩
      rcases hB : compileExpHOLExact ctxt t1 o1 src with ⟨c2, v, t2, o2⟩
      have hA1 := (compile_exp_out_rel ctxt _ l dst c1 a t1 o1 hA).2.1
      have hB1 := (compile_exp_out_rel ctxt t1 o1 src c2 v t2 o2 hB).2.1
      simp only [hB, holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨not_mem_assigned_mem_gt_comp_exp ctxt _ l dst c1 a t1 o1 n ⟨hA, hmax, hne, by omega⟩,
        not_mem_assigned_mem_gt_comp_exp ctxt t1 o1 src c2 v t2 o2 n ⟨hB, hmax, hne, by omega⟩⟩,
        by omega, by omega⟩
  | ctxt, l, .storeByte dst src, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l dst with ⟨c1, a, t1, o1⟩
      rcases hB : compileExpHOLExact ctxt t1 o1 src with ⟨c2, v, t2, o2⟩
      have hA1 := (compile_exp_out_rel ctxt _ l dst c1 a t1 o1 hA).2.1
      have hB1 := (compile_exp_out_rel ctxt t1 o1 src c2 v t2 o2 hB).2.1
      simp only [hB, holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨not_mem_assigned_mem_gt_comp_exp ctxt _ l dst c1 a t1 o1 n ⟨hA, hmax, hne, by omega⟩,
        not_mem_assigned_mem_gt_comp_exp ctxt t1 o1 src c2 v t2 o2 n ⟨hB, hmax, hne, by omega⟩⟩,
        by omega, by omega⟩
  | ctxt, l, .seq p1 p2, n, hmax, hne, hn => by
      rw [compileHOLExact]
      simp only [holLoopAssignedVars, List.mem_append, not_or]
      exact ⟨not_mem_context_assigned_aux ctxt l p1 n hmax hne hn,
        not_mem_context_assigned_aux ctxt l p2 n hmax hne hn⟩
  | ctxt, l, .ite cond p1 p2, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l cond with ⟨c, v, t, o⟩
      have hA1 := (compile_exp_out_rel ctxt _ l cond c v t o hA).2.1
      simp only [holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, List.append_nil]
      exact ⟨not_mem_assigned_mem_gt_comp_exp ctxt _ l cond c v t o n ⟨hA, hmax, hne, by omega⟩,
        by omega, not_mem_context_assigned_aux ctxt l p1 n hmax hne hn,
        not_mem_context_assigned_aux ctxt l p2 n hmax hne hn⟩
  | ctxt, l, .while cond body, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l cond with ⟨c, v, t, o⟩
      have hA1 := (compile_exp_out_rel ctxt _ l cond c v t o hA).2.1
      simp only [holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, List.append_nil]
      exact ⟨not_mem_assigned_mem_gt_comp_exp ctxt _ l cond c v t o n ⟨hA, hmax, hne, by omega⟩,
        by omega, not_mem_context_assigned_aux ctxt l body n hmax hne hn⟩
  | ctxt, l, .dec name value body, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpHOLExact ctxt (ctxt.vmax + 1) l value with ⟨c, v, t, o⟩
      have hA1 := (compile_exp_out_rel ctxt _ l value c v t o hA).2.1
      simp only [holLoopAssignedVars, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, not_or]
      refine ⟨not_mem_assigned_mem_gt_comp_exp ctxt _ l value c v t o n ⟨hA, hmax, hne, by omega⟩,
        by omega, not_mem_context_assigned_aux _ _ body n ?_ ?_ (by simp only; omega)⟩
      · intro x m hx
        simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL, FLOOKUP] at hx
        split at hx
        · cases hx; exact Nat.le_refl _
        · exact Nat.le_trans (hmax x m hx) (show ctxt.vmax ≤ t by omega)
      · intro x m hx
        simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL] at hx
        split at hx
        · cases hx; omega
        · exact hne x m hx
  | ctxt, l, .return values, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpsHOLExact ctxt (ctxt.vmax + 1) l values with ⟨c, vs, t, o⟩
      have hA1 := (compile_exp_out_rel_cases.2 ctxt _ l values c vs t o hA).2.1
      simp only [holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.not_mem_nil, or_false, not_or]
      refine ⟨not_mem_assigned_mem_gt_comp_exps ctxt _ l values c vs t o n
        ⟨hA, hmax, hne, by omega⟩, fun hm => ?_⟩
      rw [assigned_vars_nested_seq_assign _ _ (by simp [genTemps])] at hm
      have := mem_genTemps hm
      omega
  | ctxt, l, .call none fname args, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpsHOLExact ctxt (ctxt.vmax + 1) l args with ⟨c, vs, t, o⟩
      have hA1 := (compile_exp_out_rel_cases.2 ctxt _ l args c vs t o hA).2.1
      simp only [holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.not_mem_nil, or_false, not_or]
      refine ⟨not_mem_assigned_mem_gt_comp_exps ctxt _ l args c vs t o n
        ⟨hA, hmax, hne, by omega⟩, fun hm => ?_⟩
      rw [assigned_vars_nested_seq_assign _ _ (by simp [genTemps])] at hm
      have := mem_genTemps hm
      omega
  | ctxt, l, .call (some (rets, none)) fname args, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpsHOLExact ctxt (ctxt.vmax + 1) l args with ⟨c, vs, t, o⟩
      have hA1 := (compile_exp_out_rel_cases.2 ctxt _ l args c vs t o hA).2.1
      simp only [holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, List.append_nil]
      refine ⟨⟨not_mem_assigned_mem_gt_comp_exps ctxt _ l args c vs t o n
        ⟨hA, hmax, hne, by omega⟩, fun hm => ?_⟩, ?_, by omega⟩
      · rw [assigned_vars_nested_seq_assign _ _ (by simp [genTemps])] at hm
        have := mem_genTemps hm
        omega
      · split
        · simp; omega
        · rename_i names hnames
          intro hm
          obtain ⟨x, hx⟩ := mapM_some_mem_image _ rets names hnames n hm
          exact hne x n hx rfl
  | ctxt, l, .call (some (rets, some (exn, handler))) fname args, n, hmax, hne, hn => by
      rw [compileHOLExact]
      rcases hA : compileExpsHOLExact ctxt (ctxt.vmax + 1) l args with ⟨c, vs, t, o⟩
      have hA1 := (compile_exp_out_rel_cases.2 ctxt _ l args c vs t o hA).2.1
      simp only [holAssignedVarsNestedSeqSplit, loopNestedSeqHOL, holLoopAssignedVars,
        List.mem_append, List.mem_cons, not_or, List.append_nil, List.nil_append]
      refine ⟨⟨not_mem_assigned_mem_gt_comp_exps ctxt _ l args c vs t o n
        ⟨hA, hmax, hne, by omega⟩, fun hm => ?_⟩, ?_, by omega,
        not_mem_context_assigned_aux ctxt l handler n hmax hne hn⟩
      · rw [assigned_vars_nested_seq_assign _ _ (by simp [genTemps])] at hm
        have := mem_genTemps hm
        omega
      · split
        · simp; omega
        · rename_i names hnames
          intro hm
          obtain ⟨x, hx⟩ := mapM_some_mem_image _ rets names hnames n hm
          exact hne x n hx rfl
termination_by _ _ p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Exact HOL `not_mem_context_assigned_mem_gt` (`crep_to_loopProofScript.sml:1570-1575`):
    `!ctxt l p n. ctxt_max ctxt.vmax ctxt.vars /\
      (!v m. FLOOKUP ctxt.vars v = SOME m ==> n <> m) ∧ n <= ctxt.vmax ==>
      ~MEM n (assigned_vars (compile ctxt l p))`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "not_mem_context_assigned_mem_gt"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem not_mem_context_assigned_mem_gt {width : Nat} [NeZero width] :
    ∀ (ctxt : CrepToLoopContextExact) (l : NumSet) (p : CrepProgHOL width) (n : Nat),
      crepToLoopCtxtMax ctxt.vmax ctxt.vars.lookup ∧
        (∀ v m, ctxt.vars.lookup v = some m → n ≠ m) ∧ n ≤ ctxt.vmax →
      n ∉ holLoopAssignedVars (compileHOLExact ctxt l p) :=
  fun ctxt l p n ⟨h1, h2, h3⟩ => not_mem_context_assigned_aux ctxt l p n h1 h2 h3

end Flapjack
