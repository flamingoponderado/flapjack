import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.CrepInline.Canonical
import Flapjack.Pancake.CrepInline.Pass

namespace Flapjack

/-- Original `exps_of_nested_seq_assign` (`crep_inlineProofScript.sml:3042-3049`):
`∀ns es e. MEM e (exps_of (nested_seq (MAP2 Assign ns es))) ⇒ MEM e es`;
`MAP2 Assign` is `List.zipWith .assign`, as in the reviewed `transform_eoc`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_nested_seq_assign"
  (words_as_type_indexed_bitvec)]
theorem crepInline_expsOfNestedSeqAssign {width : Nat} [NeZero width] :
    ∀ (ns : List Nat) (es : List (CrepExpHOL width)) (e : CrepExpHOL width),
      e ∈ crepExpsOfHOL (crepNestedSeqHOL (ns.zipWith (fun n v => CrepProgHOL.assign n v) es)) →
        e ∈ es := by
  intro ns
  induction ns with
  | nil => intro es e h; simp [crepNestedSeqHOL, crepExpsOfHOL] at h
  | cons n ns ih =>
      intro es e h
      cases es with
      | nil => simp [crepNestedSeqHOL, crepExpsOfHOL] at h
      | cons v es =>
          simp only [List.zipWith_cons_cons, crepNestedSeqHOL, crepExpsOfHOL, List.mem_append,
            List.mem_singleton] at h
          rcases h with rfl | h
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih es e h)

/-- Original nested-declaration expression provenance, including mismatched
name/value lengths. No matching-length guard is added. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_nested_decs"
  (words_as_type_indexed_bitvec)]
theorem crepInline_expsOfNestedDecs {width : Nat} [NeZero width]
    (e : CrepExpHOL width) (vs : List Nat) (es : List (CrepExpHOL width))
    (p : CrepProgHOL width)
    (member : e ∈ crepExpsOfHOL (nestedDecsHOL vs es p)) :
    e ∈ es ∨ e ∈ crepExpsOfHOL p := by
  induction vs generalizing es with
  | nil =>
      cases es <;> simp_all [nestedDecsHOL, crepExpsOfHOL]
  | cons v vs ih =>
      cases es with
      | nil => simp [nestedDecsHOL, crepExpsOfHOL] at member
      | cons a es =>
          simp only [nestedDecsHOL, crepExpsOfHOL, List.mem_cons] at member
          rcases member with same | tail
          · exact Or.inl (List.mem_cons.mpr (Or.inl same))
          · rcases ih es tail with h | h
            · exact Or.inl (List.mem_cons.mpr (Or.inr h))
            · exact Or.inr h

/-- Original `exps_of_arg_load` (`crep_inlineProofScript.sml:3060-3068`):
`∀e tmp_vars args args_vname p. MEM e (exps_of (arg_load tmp_vars args args_vname p)) ⇒
MEM e args ∨ (∃c. MEM c tmp_vars ∧ e = Var c) ∨ MEM e (exps_of p)`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_arg_load"
  (words_as_type_indexed_bitvec)]
theorem crepInline_expsOfArgLoad {width : Nat} [NeZero width] :
    ∀ (e : CrepExpHOL width) (tmp_vars : List Nat) (args : List (CrepExpHOL width))
      (args_vname : List Nat) (p : CrepProgHOL width),
      e ∈ crepExpsOfHOL (argLoadHOLExact tmp_vars args args_vname p) →
        e ∈ args ∨ (∃ c, c ∈ tmp_vars ∧ e = .var c) ∨ e ∈ crepExpsOfHOL p := by
  intro e tmp_vars args args_vname p h
  unfold argLoadHOLExact at h
  rcases crepInline_expsOfNestedDecs _ _ _ _ h with h1 | h1
  · exact Or.inl h1
  · rcases crepInline_expsOfNestedDecs _ _ _ _ h1 with h2 | h2
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h2
      exact Or.inr (Or.inl ⟨c, hc, rfl⟩)
    · exact Or.inr (Or.inr h2)

/-- Original `exps_of_transform_eoc` (`crep_inlineProofScript.sml:3093-3108`):
`∀rts p e. MEM e (exps_of (transform_eoc rts p)) ⇒ MEM e (exps_of p)`, by HOL's
`transform_eoc_ind` recursion. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_transform_eoc"
  (words_as_type_indexed_bitvec)]
theorem crepInline_expsOfTransformEoc {width : Nat} [NeZero width] :
    ∀ (rts : List Nat) (p : CrepProgHOL width) (e : CrepExpHOL width),
      e ∈ crepExpsOfHOL (transformEocHOLExact rts p) → e ∈ crepExpsOfHOL p := by
  intro rts p
  induction p using transformEocHOLExact.induct with
  | case1 values =>
      intro e h
      simp only [transformEocHOLExact] at h
      simp only [crepExpsOfHOL]
      exact crepInline_expsOfNestedSeqAssign _ _ _ h
  | case2 => intro e h; simpa [transformEocHOLExact, crepExpsOfHOL] using h
  | case3 => intro e h; simpa [transformEocHOLExact, crepExpsOfHOL] using h
  | case4 names handler body name arguments ih =>
      intro e h
      simp only [transformEocHOLExact, crepExpsOfHOL, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih e h)
  | case5 name value body ih =>
      intro e h
      simp only [transformEocHOLExact, crepExpsOfHOL, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih e h)
  | case6 condition body ih =>
      intro e h
      simp only [transformEocHOLExact, crepExpsOfHOL, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih e h)
  | case7 first second ih1 ih2 =>
      intro e h
      simp only [transformEocHOLExact, crepExpsOfHOL, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (ih1 e h)
      · exact Or.inr (ih2 e h)
  | case8 condition thenBranch elseBranch ih1 ih2 =>
      intro e h
      simp only [transformEocHOLExact, crepExpsOfHOL, List.mem_cons, List.mem_append] at h ⊢
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (ih1 e h))
      · exact Or.inr (Or.inr (ih2 e h))
  | case9 program h1 h2 h3 h4 h5 h6 h7 h8 =>
      intro e h
      rw [transformEocHOLExact.eq_def] at h
      cases program <;> simp_all

/-- Original `exps_of_transform_branch` (`crep_inlineProofScript.sml:3110-3125`):
`∀ld rts p e. MEM e (exps_of (transform_branch ld rts p)) ⇒ MEM e (exps_of p)`, by
HOL's `transform_branch_ind` recursion. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_transform_branch"
  (words_as_type_indexed_bitvec)]
theorem crepInline_expsOfTransformBranch {width : Nat} [NeZero width] :
    ∀ (ld : Nat) (rts : List Nat) (p : CrepProgHOL width) (e : CrepExpHOL width),
      e ∈ crepExpsOfHOL (transformBranchHOLExact ld rts p) → e ∈ crepExpsOfHOL p := by
  intro ld rts p
  induction ld, p using transformBranchHOLExact.induct with
  | case1 depth values =>
      intro e h
      simp only [transformBranchHOLExact, crepExpsOfHOL, List.append_nil] at h
      simp only [crepExpsOfHOL]
      exact crepInline_expsOfNestedSeqAssign _ _ _ h
  | case2 => intro e h; simpa [transformBranchHOLExact, crepExpsOfHOL] using h
  | case3 => intro e h; simpa [transformBranchHOLExact, crepExpsOfHOL] using h
  | case4 depth names handler body name arguments ih =>
      intro e h
      simp only [transformBranchHOLExact, crepExpsOfHOL, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih e h)
  | case5 depth name value body ih =>
      intro e h
      simp only [transformBranchHOLExact, crepExpsOfHOL, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih e h)
  | case6 depth condition body ih =>
      intro e h
      simp only [transformBranchHOLExact, crepExpsOfHOL, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih e h)
  | case7 depth first second ih1 ih2 =>
      intro e h
      simp only [transformBranchHOLExact, crepExpsOfHOL, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (ih1 e h)
      · exact Or.inr (ih2 e h)
  | case8 depth condition thenBranch elseBranch ih1 ih2 =>
      intro e h
      simp only [transformBranchHOLExact, crepExpsOfHOL, List.mem_cons, List.mem_append] at h ⊢
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (ih1 e h))
      · exact Or.inr (Or.inr (ih2 e h))
  | case9 depth program h1 h2 h3 h4 h5 h6 h7 h8 =>
      intro e h
      rw [transformBranchHOLExact.eq_def] at h
      cases program <;> simp_all

/-- `unreach_elim` only removes code: every expression of its output program
occurs in its input (Flapjack infrastructure for the tagged theorem below). -/
theorem crepInline_unreachElim_exps {width : Nat} [NeZero width] :
    ∀ (p : CrepProgHOL width) (e : CrepExpHOL width),
      e ∈ crepExpsOfHOL (unreachElimHOLExact p).1 → e ∈ crepExpsOfHOL p := by
  intro p
  induction p using unreachElimHOLExact.induct with
  | case1 => intro e h; simpa [unreachElimHOLExact, crepExpsOfHOL] using h
  | case2 => intro e h; simp [unreachElimHOLExact, crepExpsOfHOL] at h
  | case3 => intro e h; simp [unreachElimHOLExact, crepExpsOfHOL] at h
  | case4 => intro e h; simp [unreachElimHOLExact, crepExpsOfHOL] at h
  | case5 first second second' secondExit hu hsome ih =>
      intro e h
      simp only [unreachElimHOLExact, hu, hsome, if_true] at h
      simp only [crepExpsOfHOL, List.mem_append]
      exact Or.inl (ih e (by rw [hu]; exact h))
  | case6 first second first' firstExit hu hnone second' secondExit hu2 ih1 ih2 =>
      intro e h
      simp only [unreachElimHOLExact, hu, hnone, hu2, if_false, Bool.false_eq_true] at h
      simp only [crepExpsOfHOL, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (ih1 e (by rw [hu]; exact h))
      · exact Or.inr (ih2 e (by rw [hu2]; exact h))
  | case7 name value body body' bodyExit hu ih =>
      intro e h
      simp only [unreachElimHOLExact, hu, crepExpsOfHOL, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih e (by rw [hu]; exact h))
  | case8 condition thenBranch elseBranch then' thenExit hu1 else' elseExit hu2 ih1 ih2 =>
      intro e h
      simp only [unreachElimHOLExact, hu1, hu2, crepExpsOfHOL, List.mem_cons, List.mem_append]
        at h ⊢
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (ih1 e (by rw [hu1]; exact h)))
      · exact Or.inr (Or.inr (ih2 e (by rw [hu2]; exact h)))
  | case9 condition body body' bodyExit hu ih =>
      intro e h
      simp only [unreachElimHOLExact, hu, crepExpsOfHOL, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih e (by rw [hu]; exact h))
  | case10 => intro e h; simpa [unreachElimHOLExact, crepExpsOfHOL] using h
  | case11 => intro e h; simpa [unreachElimHOLExact, crepExpsOfHOL] using h
  | case12 names handler body name arguments body' bodyExit hu ih =>
      intro e h
      simp only [unreachElimHOLExact, hu, crepExpsOfHOL, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih e (by rw [hu]; exact h))
  | case13 program =>
      intro e h
      rw [unreachElimHOLExact.eq_def] at h
      cases program <;> simp_all

/-- Original `exps_of_unreach_elim` (`crep_inlineProofScript.sml:3082-3091`):
`∀p q r e rt. unreach_elim p = (q, r) ∧ MEM e (exps_of q) ⇒ MEM e (exps_of p)`.
HOL's binder `rt` does not occur in the body; it is retained at its free type. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_unreach_elim"
  (words_as_type_indexed_bitvec)]
theorem crepInline_expsOfUnreachElim {width : Nat} [NeZero width] {β : Type} :
    ∀ (p q : CrepProgHOL width) (r : Option CrepEarlyExitHOL) (e : CrepExpHOL width) (_rt : β),
      unreachElimHOLExact p = (q, r) ∧ e ∈ crepExpsOfHOL q → e ∈ crepExpsOfHOL p := by
  intro p q r e _ ⟨h, he⟩
  exact crepInline_unreachElim_exps p e (by rw [h]; exact he)

end Flapjack
