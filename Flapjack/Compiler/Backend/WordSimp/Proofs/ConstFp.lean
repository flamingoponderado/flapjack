import Flapjack.Compiler.Backend.WordSimp.Proofs.GcConsts
import Flapjack.Misc.Sptree.InsertUnchanged

/-!
# `word_simpProof`: verification of `const_fp`

Counterpart of `cakeml/compiler/backend/proofs/word_simpProofScript.sml:895-1169`
(bead `flapjack-pxn.18.5.15.2.41`): `evaluate_drop_consts_1`,
`evaluate_drop_consts`, `lookup_FOLDR_delete`, `get_var_set_vars_ignore`,
`evaluate_const_fp_loop` and `evaluate_const_fp`, over the native exact
evaluator and the tagged `word_simp` definitions.  HOL's `FOLDR delete m l` is
the untagged `deleteAll l m` rendering of `word_simp`'s local overload.

Inherited assumption: theorems mentioning `evaluate` reach the
`reals_as_rational_cuts`-qualified `inst`; the theorem map records the
`docs/SOUNDNESS.md` item 8 assumption.
-/

namespace Flapjack

namespace WordSimpConstFpSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSimpConstFpSupport

namespace WordSemStateFiniteExact

open Compiler.Backend.WordSimp

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- HOL's recurring constant-set hypothesis
    `!v w. lookup v cs = SOME w ==> get_var v s = SOME (Word w)`. -/
def CsOk (cs : Spt (BitVec width)) (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ v w, sptLookup v cs = some w → getVar v s = some (.word w)

theorem evaluate_assign_eq (v : Nat) (e : WordLangExpHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.assign v e) s =
      match wordExp s e with
      | none => (some .error, s)
      | some w => (none, setVar v w s) := by
  rw [evaluate]
  rfl

end Helpers

/-- Exact HOL `evaluate_drop_consts_1` (`word_simpProofScript.sml:895-904`); HOL's
    unused binder `rest` is kept and its free `cs` is an explicit binder. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_drop_consts_1"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_drop_consts_1 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (cs : Spt (BitVec width)) :
    ∀ (vs : List Nat) (_rest : Nat) (s : WordSemStateFiniteExact width C F),
      (∀ v w, sptLookup v cs = some w → getVar v s = some (.word w)) →
        evaluate (dropConsts cs vs) s = (none, s) := by
  intro vs
  induction vs with
  | nil => intro _ s _; exact evaluate_skip_eq s
  | cons n ns ih =>
    intro r s h
    simp only [dropConsts]
    rcases hl : sptLookup n cs with _ | w
    · exact ih r s h
    · simp only
      rw [evaluate_SmartSeq, evaluate_seq_eq, ih r s h]
      simp only
      rw [evaluate_assign_eq, wordExp]
      simp only
      have hv := h n w hl
      have : setVar n (.word w) s = s := by
        simp only [setVar]
        rw [sptInsertUnchanged _ _ _ hv]
      rw [this]

/-- Exact HOL `evaluate_drop_consts` (`word_simpProofScript.sml:906-911`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_drop_consts"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_drop_consts {width : Nat} [NeZero width] {C : Type} {F : Type}
    (cs : Spt (BitVec width)) (s : WordSemStateFiniteExact width C F) (vs : List Nat)
    (p : WordLangProgHOL (BitVec width)) :
    (∀ v w, sptLookup v cs = some w → getVar v s = some (.word w)) →
      evaluate (Compiler.Backend.WordSimp.smartSeqHOL (dropConsts cs vs) p) s = evaluate p s := by
  intro h
  rw [evaluate_SmartSeq, evaluate_seq_eq, evaluate_drop_consts_1 cs vs 0 s h]

/-- Exact HOL local `lookup_FOLDR_delete` (`word_simpProofScript.sml:913-919`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_FOLDR_delete"]
theorem lookup_FOLDR_delete {β : Type} :
    ∀ (l : List Nat) (m : Spt β) (v : Nat) (w : β),
      sptLookup v (deleteAll l m) = some w → sptLookup v m = some w ∧ v ∉ l := by
  intro l
  induction l with
  | nil => intro m v w h; exact ⟨h, by simp⟩
  | cons x xs ih =>
    intro m v w h
    simp only [deleteAll, List.foldr_cons] at h
    rw [sptLookup_sptDelete] at h
    split at h
    · cases h
    · rename_i hne
      obtain ⟨h1, h2⟩ := ih m v w h
      exact ⟨h1, by simp [hne, h2]⟩

/-- Exact HOL `get_var_set_vars_ignore` (`word_simpProofScript.sml:921-927`); HOL's
    free variable `v` is the outer binder. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_set_vars_ignore"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_var_set_vars_ignore {width : Nat} [NeZero width] {C : Type} {F : Type} (v : Nat) :
    ∀ (xs : List Nat) (l : List (WordLocW width)) (m : WordSemStateFiniteExact width C F),
      v ∉ xs → getVar v (setVars xs l m) = getVar v m := by
  intro xs
  induction xs with
  | nil => intro l m _; rfl
  | cons x xs ih =>
    intro l m h
    simp only [List.mem_cons, not_or] at h
    rcases l with _ | ⟨y, ys⟩
    · rfl
    · simp only [getVar_setVars_eq, LoopSemStateFiniteExact.sptAlistInsert]
      rw [sptLookup_sptInsert_eq, if_neg h.1]
      exact ih ys m h.2

section InstCs

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem csOk_setVar_delete {cs : Spt (BitVec width)} {s : WordSemStateFiniteExact width C F}
    (h : CsOk cs s) (r : Nat) (x : WordLocW width) : CsOk (sptDelete r cs) (setVar r x s) :=
  fun v w hv => cs_delete_if_set x r v s cs w ⟨h, hv⟩

theorem csOk_setVar2_delete {cs : Spt (BitVec width)} {s : WordSemStateFiniteExact width C F}
    (h : CsOk cs s) (r1 r2 : Nat) (x1 x2 : WordLocW width) :
    CsOk (sptDelete r2 (sptDelete r1 cs)) (setVar r2 x2 (setVar r1 x1 s)) :=
  fun v w hv => cs_delete_if_set_x2 x1 x2 r1 r2 v s cs w ⟨h, hv⟩

theorem csOk_setVar2_delete' {cs : Spt (BitVec width)} {s : WordSemStateFiniteExact width C F}
    (h : CsOk cs s) (r1 r2 : Nat) (x1 x2 : WordLocW width) :
    CsOk (sptDelete r1 (sptDelete r2 cs)) (setVar r2 x2 (setVar r1 x1 s)) := by
  intro v w hv
  rw [sptLookup_sptDelete, sptLookup_sptDelete] at hv
  rw [get_var_set_var_thm, get_var_set_var_thm]
  split at hv
  · cases hv
  split at hv
  · cases hv
  rename_i h1 h2
  rw [if_neg h2, if_neg h1]
  exact h v w hv

theorem csOk_fpUpdate {cs : Spt (BitVec width)} {s : WordSemStateFiniteExact width C F}
    (h : CsOk cs s) (d : Nat) (f : BitVec 64) : CsOk cs (setFpVar d f s) := h

theorem csOk_memStore {cs : Spt (BitVec width)} {s s1 : WordSemStateFiniteExact width C F}
    (h : CsOk cs s) {a : BitVec width} {x : WordLocW width} (hm : memStore a x s = some s1) :
    CsOk cs s1 := fun v w hv => (get_var_mem_store_thm s1 v a x s hm).trans (h v w hv)

/-- Closes `inst`-result goals: every successful branch is a `setVar`/`setFpVar`/
    memory update matched against the constant set's deletions. -/
macro "inst_cs_tac" : tactic => `(tactic| first
  | (simp only [reduceCtorEq] at *; done)
  | (simp only [Option.some.injEq] at *; subst_vars
     first
       | exact csOk_setVar_delete ‹_› _ _
       | exact csOk_setVar2_delete ‹_› _ _ _ _
       | exact csOk_setVar2_delete' ‹_› _ _ _ _
       | exact ‹CsOk _ _›
       | exact fun v w hv => ‹CsOk _ _› v w hv)
  | (simp only [Option.some.injEq] at *; subst_vars; exact csOk_memStore ‹_› ‹_›)
  | contradiction
  | (exfalso; simp_all))

theorem csOk_inst (i : WordLangInst (BitVec width)) (cs : Spt (BitVec width))
    (s s1 : WordSemStateFiniteExact width C F) (h : inst i s = some s1) (hcs : CsOk cs s) :
    CsOk (constFpInstCs i cs) s1 := by
  rcases i with _ | ⟨r, c⟩ | ⟨a⟩ | ⟨op, r, ⟨b, o⟩⟩ | ⟨f⟩
  · simp only [inst, Option.some.injEq] at h; subst h; exact hcs
  · simp only [inst, assign] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; exact csOk_setVar_delete hcs _ _
  · rcases a with ⟨bop, r1, r2, ri⟩ | ⟨sh, r1, r2, ri⟩ | ⟨r1, r2, r3⟩ | ⟨r1, r2, r3, r4⟩ |
      ⟨r1, r2, r3, r4, r5⟩ | ⟨r1, r2, r3, r4⟩ | ⟨r1, r2, r3, r4⟩ | ⟨r1, r2, r3, r4⟩ <;>
      simp only [inst, assign, constFpInstCs] at h ⊢ <;>
      (repeat' split at h) <;>
      inst_cs_tac
  · cases op <;> simp only [inst, constFpInstCs] at h ⊢ <;>
      (repeat' split at h) <;>
      inst_cs_tac
  · cases f <;> simp only [inst, constFpInstCs] at h ⊢ <;>
      (repeat' split at h) <;>
      (try dsimp only at h) <;>
      (try split) <;>
      inst_cs_tac

end InstCs

section ConstFpLoop

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem csOk_same_locals {cs : Spt (BitVec width)} {s t : WordSemStateFiniteExact width C F}
    (h : CsOk cs s) (hl : t.locals = s.locals) : CsOk cs t :=
  fun v w hv => by have := h v w hv; simp only [getVar, hl] at this ⊢; exact this

theorem csOk_ln (s : WordSemStateFiniteExact width C F) : CsOk (.ln : Spt (BitVec width)) s :=
  fun v w hv => by simp [sptLookup] at hv

/-- The recursion's motive: the transformed program evaluates the same, and on
    normal termination the returned constant set is sound. -/
def CfGoal (p p' : WordLangProgHOL (BitVec width)) (cs' : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) : Prop :=
  evaluate p' s = evaluate p s ∧ ((evaluate p s).1 = none → CsOk cs' (evaluate p s).2)

theorem cfGoal_refl_of (p : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (h : (evaluate p s).1 = none → (evaluate p s).2.locals = s.locals) (hcs : CsOk cs s) :
    CfGoal p p cs s :=
  ⟨rfl, fun hn => csOk_same_locals hcs (h hn)⟩

end ConstFpLoop

section ConstFpCases

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem cf_move (pri : Nat) (moves : List (Nat × Nat)) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.move pri moves) (constFpLoop (.move pri moves) cs).1
      (constFpLoop (.move pri moves) cs).2 s := by
  simp only [constFpLoop]
  refine ⟨rfl, ?_⟩
  rw [evaluate]
  split
  · rename_i hnd
    rcases hg : getVars (moves.map Prod.snd) s with _ | vs
    · simp
    · intro _ v w hv
      simp only
      rw [lookup_const_fp_move_cs v moves cs hnd] at hv
      rw [get_var_move_thm s _ moves vs v ⟨hg, rfl⟩]
      rcases hl : sptAListLookup v moves with _ | u <;> rw [hl] at hv <;> exact hcs _ w hv
  · simp

theorem cf_inst (i : WordLangInst (BitVec width)) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.inst i) (constFpLoop (.inst i) cs).1 (constFpLoop (.inst i) cs).2 s := by
  simp only [constFpLoop]
  refine ⟨rfl, ?_⟩
  rw [evaluate]
  rcases hi : inst i s with _ | s1
  · simp
  · intro _; exact csOk_inst i cs s s1 hi hcs

theorem cf_assign (v : Nat) (e : WordLangExpHOL (BitVec width)) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.assign v e) (constFpLoop (.assign v e) cs).1 (constFpLoop (.assign v e) cs).2 s := by
  have hwe := const_fp_exp_word_exp e cs s hcs
  have first : ∀ e', constFpExp e cs = e' → evaluate (.assign v e') s = evaluate (.assign v e) s := by
    intro e' he; rw [evaluate_assign_eq, evaluate_assign_eq, ← he, hwe]
  simp only [constFpLoop]
  rcases hc : constFpExp e cs with c | _ | _ | _ | _ | _ <;> simp only
  · refine ⟨first _ hc, ?_⟩
    rw [evaluate_assign_eq]
    rcases hw : wordExp s e with _ | x
    · simp
    · intro _
      have hx := const_fp_exp_word_exp_const e cs s c ⟨hcs, hc⟩
      rw [hw] at hx; cases hx
      intro u w hu
      simp only
      rw [get_var_set_var_thm]
      rw [sptLookup_sptInsert_eq] at hu
      split at hu
      · simp only [Option.some.injEq] at hu; subst hu; rw [if_pos ‹_›]
      · rw [if_neg ‹_›]; exact hcs u w hu
  all_goals
    refine ⟨first _ hc, ?_⟩
    rw [evaluate_assign_eq]
    rcases hw : wordExp s e with _ | x
    · simp
    · intro _
      exact fun u w hu => cs_delete_if_set x v u s cs w ⟨hcs, hu⟩

theorem cutEnv_lookup {β : Type} (names : WordLangCutsetsHOL) (l env : Spt β)
    (h : wordSemCutEnv names l = some env) (v : Nat) (hv : sptLookup v (allNames names) ≠ none) :
    sptLookup v env = sptLookup v l := by
  by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive names.1 l <;>
    by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive names.2 l <;>
    simp [wordSemCutEnv, wordSemCutEnvs, wordSemCutNames, h1, h2] at h
  subst h
  rw [sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases]
  simp only [Compiler.Backend.WordSimp.allNames] at hv
  rw [sptLookup_sptUnion] at hv
  rcases hl : sptLookup v l with _ | x <;> rcases h2v : sptLookup v names.2 with _ | u2 <;>
    rcases h1v : sptLookup v names.1 with _ | u1 <;> simp_all

theorem csOk_inter_cut {cs : Spt (BitVec width)} {s t : WordSemStateFiniteExact width C F}
    (hcs : CsOk cs s) (names : WordLangCutsetsHOL) (env : Spt (WordLocW width))
    (h : wordSemCutEnv names s.locals = some env) (ht : t.locals = env) :
    CsOk (sptInter cs (allNames names)) t := by
  intro v w hv
  rw [sptLookup_sptInterCases] at hv
  rcases h1 : sptLookup v cs with _ | x <;> rcases h2 : sptLookup v (allNames names) with _ | u <;>
    simp only [h1, h2, reduceCtorEq] at hv
  simp only [Option.some.injEq] at hv; subst hv
  have := cutEnv_lookup names s.locals env h v (by rw [h2]; simp)
  show sptLookup v t.locals = _
  rw [ht, this]; exact hcs v x h1

theorem cf_simple_delete (p : WordLangProgHOL (BitVec width)) (r : Nat) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s)
    (hp : (evaluate p s).1 = none → ∃ x, (evaluate p s).2 = setVar r x s) :
    CfGoal p p (sptDelete r cs) s := by
  refine ⟨rfl, fun hn => ?_⟩
  obtain ⟨x, hx⟩ := hp hn
  rw [hx]; exact csOk_setVar_delete hcs r x

theorem cf_get (v : Nat) (name : WordStoreHOL) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.get v name) (constFpLoop (.get v name) cs).1 (constFpLoop (.get v name) cs).2 s := by
  simp only [constFpLoop]
  refine cf_simple_delete _ v cs s hcs ?_
  rw [evaluate]
  split
  · simp
  · rename_i x _; intro _; exact ⟨x, rfl⟩

theorem cf_opCurrHeap (b : BinOp) (v w : Nat) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.opCurrHeap b v w) (constFpLoop (.opCurrHeap b v w) cs).1
      (constFpLoop (.opCurrHeap b v w) cs).2 s := by
  simp only [constFpLoop]
  refine cf_simple_delete _ v cs s hcs ?_
  rw [evaluate]
  split
  · simp
  · rename_i x _; intro _; exact ⟨x, rfl⟩

theorem cf_locValue (v l : Nat) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.locValue v l) (constFpLoop (.locValue v l) cs).1
      (constFpLoop (.locValue v l) cs).2 s := by
  simp only [constFpLoop]
  refine cf_simple_delete _ v cs s hcs ?_
  rw [evaluate]
  split
  · intro _; exact ⟨_, rfl⟩
  · simp

theorem cf_storeConsts (a b c d : Nat) (ws : List (Bool × BitVec width)) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.storeConsts a b c d ws) (constFpLoop (.storeConsts a b c d ws) cs).1
      (constFpLoop (.storeConsts a b c d ws) cs).2 s := by
  simp only [constFpLoop]
  refine ⟨rfl, ?_⟩
  rw [evaluate]
  split
  · split
    · simp
    · intro _ u w hu
      simp only [sptLookup_sptDelete] at hu
      split at hu; · cases hu
      split at hu; · cases hu
      split at hu; · cases hu
      split at hu; · cases hu
      rename_i h1 h2 h3 h4
      simp only [getVar, setVar, unsetVar, sptLookup_sptInsert_eq, sptLookup_sptDelete,
        if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      exact hcs u w hu
  · simp

theorem cf_store (e : WordLangExpHOL (BitVec width)) (v : Nat) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.store e v) (constFpLoop (.store e v) cs).1 (constFpLoop (.store e v) cs).2 s := by
  simp only [constFpLoop]
  have hwe := const_fp_exp_word_exp e cs s hcs
  refine ⟨by rw [evaluate, evaluate, hwe], ?_⟩
  rw [evaluate]
  split
  · split
    · rename_i hm; intro _; exact csOk_memStore hcs hm
    · simp
  · simp

theorem cf_shareInst (op : WordMemOp) (v : Nat) (e : WordLangExpHOL (BitVec width))
    (cs : Spt (BitVec width)) (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.shareInst op v e) (constFpLoop (.shareInst op v e) cs).1
      (constFpLoop (.shareInst op v e) cs).2 s := by
  have hwe := const_fp_exp_word_exp e cs s hcs
  cases op <;> simp only [constFpLoop] <;>
    refine ⟨by rw [evaluate, evaluate, hwe], ?_⟩ <;>
    rw [evaluate] <;>
    (split <;> [skip; simp]) <;>
    simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32] <;>
    (repeat' split) <;>
    first
      | (simp; done)
      | (intro _; exact csOk_setVar_delete hcs _ _)
      | (intro _; exact hcs)

theorem cf_ffi (x0 : Basis.Pure.MlString.MlString) (x1 x2 x3 x4 : Nat) (names : WordLangCutsetsHOL)
    (cs : Spt (BitVec width)) (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.ffi x0 x1 x2 x3 x4 names) (constFpLoop (.ffi x0 x1 x2 x3 x4 names) cs).1
      (constFpLoop (.ffi x0 x1 x2 x3 x4 names) cs).2 s := by
  simp only [constFpLoop]
  refine ⟨evaluate_drop_consts cs s _ _ hcs, ?_⟩
  rw [evaluate]
  split
  · split
    · simp
    · rename_i env henv
      split
      · split
        · simp
        · intro _; exact csOk_inter_cut hcs names env henv rfl
      · simp
  · simp

theorem cf_install (r1 r2 r3 r4 : Nat) (names : WordLangCutsetsHOL)
    (cs : Spt (BitVec width)) (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s) :
    CfGoal (.install r1 r2 r3 r4 names) (constFpLoop (.install r1 r2 r3 r4 names) cs).1
      (constFpLoop (.install r1 r2 r3 r4 names) cs).2 s := by
  simp only [constFpLoop]
  refine ⟨evaluate_drop_consts cs s _ _ hcs, ?_⟩
  rw [evaluate]
  split
  · simp
  · rename_i env henv
    split
    · dsimp only
      split
      · split
        · split
          · intro _ v w hv
            rw [sptLookup_sptDelete] at hv
            split at hv
            · cases hv
            rename_i hne
            have hv' := lookup_filter_v_SOME_imp _ v w _ hv
            have := csOk_inter_cut (t := { s with locals := env }) hcs names env henv rfl v w hv'
            show sptLookup v (sptInsert r1 _ env) = _
            rw [sptLookup_sptInsert_eq, if_neg hne]
            exact this
          · simp
        · simp
      · simp
    · simp

theorem cf_alloc (n : Nat) (names : WordLangCutsetsHOL) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hok : gcFunConstOk s.gcFun) (hcs : CsOk cs s) :
    CfGoal (.alloc n names) (constFpLoop (.alloc n names) cs).1
      (constFpLoop (.alloc n names) cs).2 s := by
  simp only [constFpLoop]
  refine ⟨evaluate_drop_consts cs s _ _ hcs, ?_⟩
  rw [evaluate]
  split
  · rename_i c _
    unfold alloc
    split
    · simp
    · rename_i envs hce
      split
      · simp
      · rename_i g hg
        split
        · simp
        · rename_i p hp
          have hpok : CsOk (sptFilterV isGcConst (sptInter cs (allNames names))) p := by
            intro v w hv
            have hgc := lookup_filter_v_SOME _ v w _ hv
            have hv' := lookup_filter_v_SOME_imp _ v w _ hv
            rw [sptLookup_sptInterCases] at hv'
            rcases h1 : sptLookup v cs with _ | x <;>
              rcases h2 : sptLookup v (allNames names) with _ | u <;>
              simp only [h1, h2, reduceCtorEq] at hv'
            simp only [Option.some.injEq] at hv'; subst hv'
            have hrel := gc_sf_gc_consts (pushEnv envs none (setStore .allocSize (.word c) s)) g
              ⟨hok, hg⟩
            exact push_env_pop_env_locals_thm (setStore .allocSize (.word c) s) _ g p envs
              names none ⟨hce, rfl, hrel, hp⟩ v (.word x)
              ⟨hcs v x h1, hgc, by rw [h2]; simp⟩
          split
          · simp
          · split
            · simp
            · intro _; exact hpok
            · simp
  · simp

set_option linter.unusedSimpArgs false in
theorem cf_other (p : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hcs : CsOk cs s)
    (hp : p = .skip ∨ (∃ a b, p = .set a b) ∨ p = .tick ∨ (∃ n, p = .raise n) ∨
      (∃ a b, p = .return a b) ∨ (∃ k, p = .break k) ∨ (∃ k, p = .continue k) ∨
      (∃ a b, p = .codeBufferWrite a b) ∨ (∃ a b, p = .dataBufferWrite a b)) :
    CfGoal p (constFpLoop p cs).1 (constFpLoop p cs).2 s := by
  rcases hp with rfl | ⟨a, b, rfl⟩ | rfl | ⟨n, rfl⟩ | ⟨a, b, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ |
      ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ <;>
    simp only [constFpLoop] <;>
    refine ⟨rfl, ?_⟩ <;>
    rw [evaluate] <;>
    (repeat' split) <;>
    first
      | (simp; done)
      | (intro _; exact csOk_same_locals hcs rfl)

theorem evaluate_call_none_ne_none (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    (evaluate (.call none dest args handler) s).1 ≠ none := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht]
  rcases getVars args s with _ | xs
  · simp
  simp only
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp [hbad]
  simp only [hbad, Bool.false_eq_true, if_false]
  rcases wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) s.code s.stackSize with
    _ | ⟨args1, prog, ss⟩
  · simp
  simp only
  cases handler with
  | some _ => simp
  | none =>
    simp only
    by_cases hz : s.clock = 0
    · rw [if_pos hz]; simp
    rw [if_neg hz]
    rcases evaluate prog (callEnv args1 ss (decClock s)) with ⟨r, s1⟩
    simp only
    split
    · simp
    · rename_i hb
      cases r with
      | none => simp [wordSemBadFunReturn] at hb
      | some _ => simp

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `evaluate_const_fp_loop`, by structural recursion on
    the program as HOL's `const_fp_loop_ind`. -/
theorem cf_aux :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width))
      (s : WordSemStateFiniteExact width C F),
      gcFunConstOk s.gcFun → CsOk cs s → CfGoal p (constFpLoop p cs).1 (constFpLoop p cs).2 s
  | .mustTerminate q, cs, s, hok, hcs => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [constFpLoop]
      rcases hq : constFpLoop q cs with ⟨q', cs1⟩
      simp only
      have ih := cf_aux q cs { s with
          clock := wordSemMustTerminateLimit width
          termdep := s.termdep - 1 } hok (csOk_same_locals hcs rfl)
      rw [hq] at ih
      refine ⟨?_, ?_⟩
      · rw [ht, ht, ih.1]
      · rw [ht]
        by_cases hz : s.termdep = 0
        · simp [hz]
        · simp only [hz, dite_false, if_false]
          have ih2 := ih.2
          rcases hev : evaluate q { s with
              clock := wordSemMustTerminateLimit width
              termdep := s.termdep - 1 } with ⟨r, s1⟩
          rw [hev] at ih2
          cases r with
          | none => intro _; exact csOk_same_locals (ih2 rfl) rfl
          | some x => cases x <;> simp
  | .seq p1 p2, cs, s, hok, hcs => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [constFpLoop]
      rcases h1 : constFpLoop p1 cs with ⟨p1', cs1⟩
      have ih1 := cf_aux p1 cs s hok hcs
      rw [h1] at ih1
      simp only [CfGoal] at ih1 ⊢
      rcases h2 : constFpLoop p2 cs1 with ⟨p2', cs2⟩
      simp only
      rcases he1 : evaluate p1 s with ⟨r1, s1⟩
      rw [he1] at ih1
      cases r1 with
      | none =>
        have hok1 : gcFunConstOk s1.gcFun := evaluate_gc_fun_const_ok p1 s none s1 ⟨he1, hok⟩
        have ih2 := cf_aux p2 cs1 s1 hok1 (ih1.2 rfl)
        rw [h2] at ih2
        simp only [CfGoal] at ih2
        refine ⟨?_, ?_⟩
        · rw [ht, ht, ih1.1, he1]; exact ih2.1
        · rw [ht, he1]; exact ih2.2
      | some x =>
        refine ⟨?_, ?_⟩
        · rw [ht, ht, ih1.1, he1]
        · rw [ht, he1]; simp
  | .ite cmp lhs rhs p1 p2, cs, s, hok, hcs => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have ih1 := cf_aux p1 cs s hok hcs
      have ih2 := cf_aux p2 cs s hok hcs
      simp only [constFpLoop]
      rcases hl : sptLookup lhs cs with _ | clhs <;> rcases hr : getVarImmCs rhs cs with _ | crhs
      all_goals simp only
      rotate_left 3
      · -- both known: the If is decided statically
        have hgv : getVar lhs s = some (.word clhs) := hcs lhs clhs hl
        have hgi := get_var_imm_cs_imp_get_var_imm rhs crhs s cs ⟨hcs, hr⟩
        have hev : evaluate (.ite cmp lhs rhs p1 p2) s =
            if Compiler.Encoders.Asm.wordCmpHOL cmp clhs crhs then evaluate p1 s
            else evaluate p2 s := by
          rw [ht, hgv, hgi]
          simp only [wordSemWordCmp]
          split <;> simp_all
        split
        · exact ⟨by rw [hev, if_pos ‹_›]; exact ih1.1, by rw [hev, if_pos ‹_›]; exact ih1.2⟩
        · exact ⟨by rw [hev, if_neg ‹_›]; exact ih2.1, by rw [hev, if_neg ‹_›]; exact ih2.2⟩
      all_goals
        rcases h1 : constFpLoop p1 cs with ⟨p1', cs1⟩
        rcases h2 : constFpLoop p2 cs with ⟨p2', cs2⟩
        rw [h1] at ih1; rw [h2] at ih2
        simp only
        refine ⟨by rw [ht, ht, ih1.1, ih2.1], ?_⟩
        rw [ht]
        rcases getVar lhs s with _ | x <;> rcases getVarImm rhs s with _ | y <;> simp only <;>
          try simp
        rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only
        · simp
        · intro hn v w hv
          exact ih2.2 hn v w (lookup_inter_eq_some cs1 cs2 v w hv).2
        · intro hn v w hv
          exact ih1.2 hn v w (lookup_inter_eq_some cs1 cs2 v w hv).1
  | .loop names body exitNames, cs, s, hok, hcs => by
      simp only [constFpLoop]
      refine ⟨?_, fun _ => csOk_ln _⟩
      exact evaluate_Loop_body_cong_gc gcFunConstOk s names body _ exitNames
        (fun v hv => (cf_aux body .ln v hv (csOk_ln v)).1) hok
  | .call ret dest args handler, cs, s, hok, hcs => by
      cases ret with
      | none =>
        simp only [constFpLoop]
        exact ⟨evaluate_drop_consts cs s _ _ hcs,
          fun hn => absurd hn (evaluate_call_none_ne_none dest args handler s)⟩
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        cases handler with
        | some hv =>
          simp only [constFpLoop]
          exact ⟨evaluate_drop_consts cs s _ _ hcs, fun _ => csOk_ln _⟩
        | none =>
          have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          simp only [constFpLoop]
          rcases hr : constFpLoop retHandler
              (deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names)))) with ⟨rh', cs''⟩
          simp only [CfGoal]
          rw [evaluate_drop_consts cs s _ _ hcs, ht, ht]
          simp only [wordSemAddRetLoc]
          rcases hg : getVars args s with _ | xs
          · simp
          simp only
          by_cases hbad : wordSemBadDestArgs dest args = true
          · simp [hbad]
          simp only [hbad, Bool.false_eq_true, if_false]
          rcases hf : wordSemFindCode dest (.loc l1 l2 :: xs) s.code s.stackSize with
            _ | ⟨args1, prog, ss⟩
          · simp
          simp only
          by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
          · simp [hdc]
          simp only [hdc, if_false]
          rcases hce : wordSemCutEnvs names s.locals with _ | envs
          · simp
          simp only
          by_cases hz : s.clock = 0
          · rw [if_pos hz, if_pos hz]; simp
          rw [if_neg hz, if_neg hz]
          rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs none (decClock s))) with
            ⟨rc, s2⟩
          rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | kk | kk | _ | _ | _ | _
          · simp
          · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
            · simp [hx]
            simp only [hx, if_false]
            rcases hp : popEnv s2 with _ | s1
            · simp
            simp only
            split
            · have hgf : (callEnv args1 ss (pushEnv envs none (decClock s))).gcFun = s.gcFun := rfl
              have hok2 : gcFunConstOk s2.gcFun := by
                rw [← (evaluate_consts prog _ _ s2 hcv).1, hgf]; exact hok
              have hok1 : gcFunConstOk (setVars n ys s1).gcFun :=
                pop_env_gc_fun_const_ok s2 s1 ⟨hp, hok2⟩
              have hsf := evaluate_sf_gc_consts prog _ s2 _ ⟨hcv, by rw [hgf]; exact hok⟩
              simp only [sfMotive] at hsf
              have hcs' : CsOk (deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names))))
                  (setVars n ys s1) := by
                intro v w hv
                obtain ⟨hv1, hvn⟩ := lookup_FOLDR_delete n _ v w hv
                have hgc := lookup_filter_v_SOME _ v w _ hv1
                have hv2 := lookup_filter_v_SOME_imp _ v w _ hv1
                rw [sptLookup_sptInterCases] at hv2
                rcases h1 : sptLookup v cs with _ | c <;>
                  rcases h2 : sptLookup v (allNames names) with _ | u <;>
                  simp only [h1, h2, reduceCtorEq] at hv2
                simp only [Option.some.injEq] at hv2; subst hv2
                rw [get_var_set_vars_ignore v n ys s1 hvn]
                exact push_env_pop_env_locals_thm (decClock s) _ s2 s1 envs names none
                  ⟨hce, rfl, hsf.1, hp⟩ v (.word c) ⟨hcs v c h1, hgc, by rw [h2]; simp⟩
              have ih := cf_aux retHandler _ (setVars n ys s1) hok1 hcs'
              rw [hr] at ih
              exact ih
            · simp
          · simp
          all_goals simp
  | .move pri moves, cs, s, _, hcs => cf_move pri moves cs s hcs
  | .inst i, cs, s, _, hcs => cf_inst i cs s hcs
  | .assign v e, cs, s, _, hcs => cf_assign v e cs s hcs
  | .get v name, cs, s, _, hcs => cf_get v name cs s hcs
  | .opCurrHeap b v w, cs, s, _, hcs => cf_opCurrHeap b v w cs s hcs
  | .locValue v l, cs, s, _, hcs => cf_locValue v l cs s hcs
  | .storeConsts a b c d ws, cs, s, _, hcs => cf_storeConsts a b c d ws cs s hcs
  | .store e v, cs, s, _, hcs => cf_store e v cs s hcs
  | .shareInst op v e, cs, s, _, hcs => cf_shareInst op v e cs s hcs
  | .ffi x0 x1 x2 x3 x4 names, cs, s, _, hcs => cf_ffi x0 x1 x2 x3 x4 names cs s hcs
  | .install r1 r2 r3 r4 names, cs, s, _, hcs => cf_install r1 r2 r3 r4 names cs s hcs
  | .alloc n names, cs, s, hok, hcs => cf_alloc n names cs s hok hcs
  | .skip, cs, s, _, hcs => cf_other _ cs s hcs (by simp)
  | .set a b, cs, s, _, hcs => cf_other _ cs s hcs (by simp)
  | .tick, cs, s, _, hcs => cf_other _ cs s hcs (by simp)
  | .raise n, cs, s, _, hcs => cf_other _ cs s hcs (by simp)
  | WordLangProgHOL.return a b, cs, s, _, hcs => cf_other _ cs s hcs (by simp)
  | WordLangProgHOL.break k, cs, s, _, hcs => cf_other _ cs s hcs (by simp)
  | WordLangProgHOL.continue k, cs, s, _, hcs => cf_other _ cs s hcs (by simp)
  | .codeBufferWrite a b, cs, s, _, hcs => cf_other _ cs s hcs (by simp)
  | .dataBufferWrite a b, cs, s, _, hcs => cf_other _ cs s hcs (by simp)

end ConstFpCases

/-- Exact HOL `evaluate_const_fp_loop` (`word_simpProofScript.sml:929-1158`):
    for arbitrary program, constant set, transformed program/set, state and
    result, the four-conjunct premise gives the same evaluation and, on normal
    termination, a sound returned constant set.  Proved by structural
    recursion on the program as HOL's `const_fp_loop_ind`.  Inherits
    `reals_as_rational_cuts` through `evaluate`. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_const_fp_loop"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_const_fp_loop {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width))
      (p' : WordLangProgHOL (BitVec width)) (cs' : Spt (BitVec width))
      (s : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate p s = (res, s') ∧ constFpLoop p cs = (p', cs') ∧ gcFunConstOk s.gcFun ∧
        (∀ v w, sptLookup v cs = some w → getVar v s = some (.word w)) →
        evaluate p' s = (res, s') ∧
          (res = none → ∀ v w, sptLookup v cs' = some w → getVar v s' = some (.word w)) := by
  intro p cs p' cs' s res s' ⟨he, hc, hok, hcs⟩
  have := cf_aux p cs s hok hcs
  rw [hc] at this
  simp only [CfGoal, he] at this
  exact ⟨this.1, fun hn => this.2 hn⟩

/-- Exact HOL `evaluate_const_fp` (`word_simpProofScript.sml:1160-1167`).  Inherits
    `reals_as_rational_cuts` through `evaluate`. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_const_fp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_const_fp {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      gcFunConstOk s.gcFun → evaluate (constFp p) s = evaluate p s := by
  intro p s hok
  exact (cf_aux p .ln s hok (csOk_ln s)).1

end WordSemStateFiniteExact

end Flapjack
