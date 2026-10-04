import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.CrepInline.Canonical
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.Proofs.CrepInline
import Flapjack.Pancake.CrepToLoop.Proofs.CodeRel2
import Flapjack.Pancake.Semantics.CrepProps.EveryExpHOL

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

section InstInline

open CrepInlineCanonical
/-! ### `exps_of_inst_inline` -/

/-- Conclusion of HOL `exps_of_inst_inline`: `e` occurs in the caller program,
is a constant or a variable, or occurs in the body of some `crep_code` entry.
Flapjack abbreviation for the induction below; no HOL original. -/
def crepInlineInstProv {width : Nat} [NeZero width]
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (prog : CrepProgHOL width) (e : CrepExpHOL width) : Prop :=
  e ∈ crepExpsOfHOL prog ∨ (∃ c, e = .const c) ∨ (∃ v, e = .var v) ∨
    ∃ name params body, (name, params, body) ∈ crep_code ∧ e ∈ crepExpsOfHOL body

theorem crepInlineInstProv_of_callee {width : Nat} [NeZero width]
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (inl : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (hsub : HolFiniteMapExact.submap inl (alistToFmapCodeExact crep_code))
    (name : CrepInlineMapHOLName) (params : List Nat) (body : CrepProgHOL width)
    (hlookup : inl.lookup name = some (params, body))
    (prog : CrepProgHOL width) (e : CrepExpHOL width)
    (h : crepInlineInstProv crep_code body e) :
    crepInlineInstProv crep_code prog e := by
  have hmem : (name, params, body) ∈ crep_code :=
    flookup_fupdateList_reverse_mem' crep_code name (params, body) (hsub _ _ hlookup)
  rcases h with h | h | h | ⟨n, ps, b, hb, h⟩
  · exact Or.inr (Or.inr (Or.inr ⟨name, params, body, hmem, h⟩))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨n, ps, b, hb, h⟩))

theorem crepInlineInstProv_mono {width : Nat} [NeZero width]
    {crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)}
    {p q : CrepProgHOL width} {e : CrepExpHOL width}
    (hpq : ∀ x, x ∈ crepExpsOfHOL p → x ∈ crepExpsOfHOL q) :
    crepInlineInstProv crep_code p e → crepInlineInstProv crep_code q e
  | .inl h => .inl (hpq e h)
  | .inr h => .inr h

/-- The return-copy sequence of `inline_nontail` only mentions variables. -/
theorem expsOf_nestedSeq_assignVar {width : Nat} [NeZero width]
    (ns ts : List Nat) (e : CrepExpHOL width)
    (h : e ∈ crepExpsOfHOL (crepNestedSeqHOL
      (ns.zipWith (fun n t => CrepProgHOL.assign n (CrepExpHOL.var t)) ts))) :
    ∃ v, e = .var v := by
  rw [← List.zipWith_map_right] at h
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp (crepInline_expsOfNestedSeqAssign _ _ e h)
  exact ⟨v, rfl⟩

/-- `inl \\ name SUBMAP m` whenever `inl SUBMAP m`. -/
theorem submap_erase_left {α β : Type} [BEq α] [LawfulBEq α]
    (inl m : HolFiniteMapExact α β) (name : α) (hsub : HolFiniteMapExact.submap inl m) :
    HolFiniteMapExact.submap (inl.erase name) m := by
  intro k v hk
  apply hsub k v
  simp only [HolFiniteMapExact.lookup_erase, FDOMSUB] at hk
  split at hk
  · cases hk
  · exact hk

/-- Generalisation of HOL `exps_of_inst_inline` to the support-certified core
`inlineProgHOLCoreExact`, proved by its functional induction (Flapjack
infrastructure; the tagged statement follows). -/
theorem crepInline_instInlineCore_exps {width : Nat} [NeZero width]
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    ∀ (inl : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
      (keys : List CrepInlineMapHOLName)
      (spec : ∀ key, inl.lookup key ≠ none → key ∈ keys) (prog : CrepProgHOL width),
      HolFiniteMapExact.submap inl (alistToFmapCodeExact crep_code) →
      ∀ e, e ∈ crepExpsOfHOL (inlineProgHOLCoreExact inl keys spec prog) →
        crepInlineInstProv crep_code prog e := by
  intro inl keys spec prog
  induction inl, keys, spec, prog using inlineProgHOLCoreExact.induct with
  | case1 inl keys spec name args hl =>
      intro _ e h
      rw [inlineProgHOLCoreExact_call_none] at h
      split at h
      · exact Or.inl h
      · rename_i heq; rw [hl] at heq; cases heq
  | case2 inl keys spec name args argNames body hl ih =>
      intro hsub e h
      rw [inlineProgHOLCoreExact_call_none] at h
      split at h
      · rename_i heq; rw [hl] at heq; cases heq
      · rename_i an b heq
        rw [hl] at heq; cases heq
        simp only [inlineTailHOLExact, crepExpsOfHOL, List.nil_append] at h
        rcases crepInline_expsOfArgLoad e _ _ _ _ h with h | ⟨c, _, rfl⟩ | h
        · exact Or.inl (by simpa [crepExpsOfHOL] using h)
        · exact Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
        · have h := crepInline_unreachElim_exps _ e h
          exact crepInlineInstProv_of_callee crep_code inl hsub name argNames body hl _ e
            (ih (submap_erase_left inl _ name hsub) e h)
  | case3 inl keys spec rets name args hd =>
      intro _ e h
      rw [inlineProgHOLCoreExact_call_returns, if_pos hd] at h
      exact Or.inl h
  | case4 inl keys spec rets name args hd hl =>
      intro _ e h
      rw [inlineProgHOLCoreExact_call_returns, if_neg hd] at h
      split at h
      · exact Or.inl h
      · rename_i heq; rw [hl] at heq; cases heq
  | case5 inl keys spec rets name args hd argNames body hl ih =>
      intro hsub e h
      rw [inlineProgHOLCoreExact_call_returns, if_neg hd] at h
      split at h
      · rename_i heq; rw [hl] at heq; cases heq
      · rename_i an b heq
        rw [hl] at heq; cases heq
        have callee : ∀ q, e ∈ crepExpsOfHOL (unreachElimHOLExact q).1 →
            (∀ e, e ∈ crepExpsOfHOL q → crepInlineInstProv crep_code body e) →
            crepInlineInstProv crep_code (.call (some (rets, none)) name args) e :=
          fun q hq hb => crepInlineInstProv_of_callee crep_code inl hsub name argNames body hl _ e
            (hb e (crepInline_unreachElim_exps q e hq))
        have ihb := ih (submap_erase_left inl _ name hsub)
        simp only [inlineNontailHOLExact] at h
        rcases crepInline_expsOfNestedDecs e _ _ _ h with h | h
        · obtain ⟨-, rfl⟩ := List.mem_replicate.mp h
          exact Or.inr (Or.inl ⟨_, rfl⟩)
        simp only [crepExpsOfHOL, List.mem_append] at h
        rcases h with h | h
        · rcases crepInline_expsOfArgLoad e _ _ _ _ h with h | ⟨c, _, rfl⟩ | h
          · exact Or.inl (by simpa [crepExpsOfHOL] using h)
          · exact Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
          · split at h
            · simp only [crepExpsOfHOL, List.nil_append] at h
              exact callee _ (crepInline_expsOfTransformEoc _ _ e h) ihb
            · simp only [crepExpsOfHOL, List.mem_cons] at h
              rcases h with rfl | h
              · exact Or.inr (Or.inl ⟨_, rfl⟩)
              · exact callee _ (crepInline_expsOfTransformBranch _ _ _ e h) ihb
        · exact Or.inr (Or.inr (Or.inl (expsOf_nestedSeq_assignVar _ _ e h)))
  | case6 inl keys spec rets handler body name args ih =>
      intro hsub e h
      rw [inlineProgHOLCoreExact_call_handler] at h
      simp only [crepExpsOfHOL, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl (by simp [crepExpsOfHOL, h])
      · exact (crepInlineInstProv_mono (fun x hx => by simp [crepExpsOfHOL, hx])) (ih hsub e h)
  | case7 inl keys spec name value body ih =>
      intro hsub e h
      rw [inlineProgHOLCoreExact_dec] at h
      simp only [crepExpsOfHOL, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl (by simp [crepExpsOfHOL])
      · exact (crepInlineInstProv_mono (fun x hx => by simp [crepExpsOfHOL, hx])) (ih hsub e h)
  | case8 inl keys spec first second ih1 ih2 =>
      intro hsub e h
      rw [inlineProgHOLCoreExact_seq] at h
      simp only [crepExpsOfHOL, List.mem_append] at h
      rcases h with h | h
      · exact (crepInlineInstProv_mono (fun x hx => by simp [crepExpsOfHOL, hx])) (ih1 hsub e h)
      · exact (crepInlineInstProv_mono (fun x hx => by simp [crepExpsOfHOL, hx])) (ih2 hsub e h)
  | case9 inl keys spec cond first second ih1 ih2 =>
      intro hsub e h
      rw [inlineProgHOLCoreExact_ite] at h
      simp only [crepExpsOfHOL, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact Or.inl (by simp [crepExpsOfHOL])
      · exact (crepInlineInstProv_mono (fun x hx => by simp [crepExpsOfHOL, hx])) (ih1 hsub e h)
      · exact (crepInlineInstProv_mono (fun x hx => by simp [crepExpsOfHOL, hx])) (ih2 hsub e h)
  | case10 inl keys spec cond body ih =>
      intro hsub e h
      rw [inlineProgHOLCoreExact_while] at h
      simp only [crepExpsOfHOL, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl (by simp [crepExpsOfHOL])
      · exact (crepInlineInstProv_mono (fun x hx => by simp [crepExpsOfHOL, hx])) (ih hsub e h)
  | case11 inl keys spec program h1 h2 h3 h4 h5 h6 h7 =>
      intro _ e h
      have heq : inlineProgHOLCoreExact inl keys spec program = program := by
        rw [inlineProgHOLCoreExact.eq_def]
        cases program <;> simp_all
      rw [heq] at h
      exact Or.inl h

/-- Original `exps_of_inst_inline` (`crep_inlineProofScript.sml:3128-3233`):
`∀inl_fs prog crep_code e. inl_fs SUBMAP alist_to_fmap crep_code ∧
MEM e (exps_of (inline_prog inl_fs prog)) ⇒ MEM e (exps_of prog) ∨ (∃c. e = Const c) ∨
(∃v. e = Var v) ∨ ∃name params body. MEM (name,params,body) crep_code ∧ MEM e (exps_of body)`.
`SUBMAP` is `HolFiniteMapExact.submap`, `alist_to_fmap` the reviewed
`alistToFmapCodeExact`, and `inline_prog` the tagged `inlineProgHOLExact`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "exps_of_inst_inline"
  (fmap_as_finite_support_relation := [inl_fs]) (words_as_type_indexed_bitvec)]
theorem crepInline_expsOfInstInline {width : Nat} [NeZero width]
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (prog : CrepProgHOL width)
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (e : CrepExpHOL width) :
    HolFiniteMapExact.submap inl_fs (alistToFmapCodeExact crep_code) ∧
      e ∈ crepExpsOfHOL (inlineProgHOLExact inl_fs prog) →
    e ∈ crepExpsOfHOL prog ∨ (∃ c, e = .const c) ∨ (∃ v, e = .var v) ∨
      ∃ name params body, (name, params, body) ∈ crep_code ∧ e ∈ crepExpsOfHOL body := by
  rintro ⟨hsub, h⟩
  unfold inlineProgHOLExact at h
  exact crepInline_instInlineCore_exps crep_code inl_fs _ _ prog hsub e h

/-- Original `every_inst_crep_inline` (`crep_inlineProofScript.sml:3235-3260`):
if every body expression of `crep_code` satisfies
`every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)` and
`inl_fs SUBMAP alist_to_fmap crep_code`, the same holds for every function of
`compile_inl_prog inl_fs crep_code`. HOL's paired abstraction
`λ(name,params,body). …` is the Lean pattern-matching lambda. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "every_inst_crep_inline"
  (fmap_as_finite_support_relation := [inl_fs]) (words_as_type_indexed_bitvec)]
theorem crepInline_everyInstCrepInline {width : Nat} [NeZero width]
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width)) :
    (∀ e, e ∈ crep_code →
        (fun ((_name, _params, body) : CrepInlineMapHOLName × List Nat × CrepProgHOL width) =>
          ∀ e, e ∈ crepExpsOfHOL body →
            crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e) e) ∧
      HolFiniteMapExact.submap inl_fs (alistToFmapCodeExact crep_code) →
    ∀ e, e ∈ compileInlProgHOLExact inl_fs crep_code →
      (fun ((_name, _params, body) : CrepInlineMapHOLName × List Nat × CrepProgHOL width) =>
        ∀ e, e ∈ crepExpsOfHOL body →
          crepEveryExpHOL (fun x => ∀ op es, x = .crepOp op es → es.length = 2) e) e := by
  rintro ⟨hall, hsub⟩ e he
  simp only [compileInlProgHOLExact, List.mem_map] at he
  obtain ⟨⟨name, params, body⟩, hmem, rfl⟩ := he
  intro x hx
  rcases crepInline_expsOfInstInline (inl_fs.erase name) body crep_code x
      ⟨submap_erase_left inl_fs _ name hsub, hx⟩ with
    h | ⟨c, rfl⟩ | ⟨v, rfl⟩ | ⟨n, ps, b, hb, h⟩
  · exact hall _ hmem x h
  · simp [crepEveryExpHOL]
  · simp [crepEveryExpHOL]
  · exact hall _ hb x h

end InstInline

end Flapjack
