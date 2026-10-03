import Flapjack.Compiler.Backend.WordSimp.Proofs.SeqAssoc
import Flapjack.Compiler.Backend.WordSimp.Proofs.GcWordConst
import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Misc.SptreeLookup
import Mathlib.Data.List.Forall2
import Flapjack.Misc.Sptree.FilterV
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.MemStoreConst

/-!
# `word_simpProof`: `const_fp` support lemmas

Counterpart of `cakeml/compiler/backend/proofs/word_simpProofScript.sml:128-430`
(bead `flapjack-pxn.18.5.15.2.41`): the GC-constant relations `gc_fun_const_ok`
and `sf_gc_consts`, and the `Assign`/`Move`/`If`/locals/lookup/list/stack lemmas
used by the `const_fp` correctness proof, over the native exact state and the
tagged `word_simp` definitions.  HOL `ALOOKUP` is `sptAListLookup`, `LIST_REL`
is `List.Forall₂`, and HOL `word_exp` is the tagged `wordExp`.
-/

namespace Flapjack

namespace WordSimpConstFpLemmasSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSimpConstFpLemmasSupport

/-- Composition of pointwise relations along `Forall₂` (Flapjack infrastructure,
    HOL `EVERY2_trans`). -/
theorem forall₂_trans' {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} (h : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l1 : List α} {l2 : List β} {l3 : List γ},
      List.Forall₂ R l1 l2 → List.Forall₂ S l2 l3 → List.Forall₂ T l1 l3
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2 => .cons (h _ _ _ h1 h2) (forall₂_trans' h t1 t2)

namespace Compiler.Backend.WordSimp

/-- Exact HOL `gc_fun_const_ok_def` (`word_simpProofScript.sml:135-139`):
    `!x y. f x = SOME y ==> EVERY2 (\a b. is_gc_word_const a ==> b = a) (FST x)
    (FST y)`, with `EVERY2` as `List.Forall₂`. The argument inherits the
    reviewed `gc_fun_type` slot translation (`WordSemGcFun`, argument 4 /
    result 3). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "gc_fun_const_ok_def"
  (fmap_as_finite_support_function := [argument_4, result_3]) (words_as_type_indexed_bitvec)]
def gcFunConstOk {width : Nat} [NeZero width] (f : WordSemGcFun width) : Prop :=
  ∀ x y, f x = some y →
    List.Forall₂ (fun a b => isGcWordConst a = true → b = a) x.1 y.1

/-- Exact HOL `sf_gc_consts_def` (`word_simpProofScript.sml:141-145`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "sf_gc_consts_def" 141
  (words_as_type_indexed_bitvec)]
def sfGcConsts {width : Nat} [NeZero width] :
    WordSemStackFrame width → WordSemStackFrame width → Prop
  | .stackFrame _ l0 sv h, .stackFrame _ l0' sw h' =>
      List.Forall₂ (fun (a b : Nat × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) sv sw ∧
        l0 = l0' ∧ h = h'

/-- Exact HOL `sf_gc_consts_refl` (`word_simpProofScript.sml:154-158`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "sf_gc_consts_refl"
  (words_as_type_indexed_bitvec)]
theorem sfGcConstsRefl {width : Nat} [NeZero width] :
    ∀ x : WordSemStackFrame width, sfGcConsts x x := by
  intro x
  rcases x with ⟨_, l0, sv, h⟩
  exact ⟨List.forall₂_same.mpr fun _ _ => ⟨rfl, fun _ => rfl⟩, rfl, rfl⟩

/-- Exact HOL `sf_gc_consts_trans` (`word_simpProofScript.sml:160-168`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "sf_gc_consts_trans"
  (words_as_type_indexed_bitvec)]
theorem sfGcConstsTrans {width : Nat} [NeZero width] :
    ∀ a b c : WordSemStackFrame width, sfGcConsts a b ∧ sfGcConsts b c → sfGcConsts a c := by
  intro a b c ⟨hab, hbc⟩
  rcases a with ⟨_, l0a, sa, ha⟩
  rcases b with ⟨_, l0b, sb, hb⟩
  rcases c with ⟨_, l0c, sc, hc⟩
  obtain ⟨r1, e1, f1⟩ := hab
  obtain ⟨r2, e2, f2⟩ := hbc
  refine ⟨?_, e1.trans e2, f1.trans f2⟩
  refine forall₂_trans' (fun x y z hxy hyz => ⟨hxy.1.trans hyz.1, fun hx => ?_⟩) r1 r2
  have hy : y.2 = x.2 := hxy.2 hx
  rw [hyz.2 (hy ▸ hx), hy]

end Compiler.Backend.WordSimp

namespace WordSemStateFiniteExact

open Compiler.Backend.WordSimp

/-- Exact HOL `strip_const_thm` (`word_simpProofScript.sml:172-176`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "strip_const_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem strip_const_thm {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (xs : List (WordLangExpHOL (BitVec width))) (x : List (BitVec width))
      (s : WordSemStateFiniteExact width C F),
      stripConst xs = some x → xs.map (fun a => wordExp s a) = x.map (some ∘ WordLocW.word) := by
  intro xs
  induction xs with
  | nil => intro x s h; simp [stripConst] at h; subst h; rfl
  | cons a as ih =>
    intro x s h
    rcases a with c | _ | _ | _ | _ | _ <;> simp only [stripConst, reduceCtorEq] at h
    split at h
    · rename_i ws hws
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.map_cons, Function.comp, ih ws s hws]
      rw [wordExp]
    · cases h

/-- Exact HOL `the_words_thm` (`word_simpProofScript.sml:178-182`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "the_words_thm"
  (words_as_type_indexed_bitvec)]
theorem the_words_thm {width : Nat} [NeZero width] :
    ∀ x : List (BitVec width), theWords (x.map (some ∘ WordLocW.word)) = some x := by
  intro x
  induction x with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, Function.comp, theWords, ih] at *

theorem wordExp_op_eq {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) (op : BinOp) (args : List (WordLangExpHOL (BitVec width))) :
    wordExp s (.op op args) =
      match theWords (args.map (fun a => wordExp s a)) with
      | some ws => (wordOpHOL op ws).map WordLocW.word
      | none => none := by
  rw [wordExp]
  simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
  rfl

/-- Exact HOL `const_fp_exp_word_exp` (`word_simpProofScript.sml:184-201`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "const_fp_exp_word_exp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem const_fp_exp_word_exp {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (e : WordLangExpHOL (BitVec width)) (cs : Spt (BitVec width))
      (s : WordSemStateFiniteExact width C F),
      (∀ v w, sptLookup v cs = some w → getVar v s = some (.word w)) →
        wordExp s (constFpExp e cs) = wordExp s e
  | .var v, cs, s, h => by
      rw [constFpExp]
      rcases hv : sptLookup v cs with _ | x
      · rfl
      · simp only
        rw [wordExp, wordExp, h v x hv]
  | .op op args, cs, s, h => by
      have ih : ∀ a ∈ args, wordExp s (constFpExp a cs) = wordExp s a :=
        fun a ha =>
          have := List.sizeOf_lt_of_mem ha
          const_fp_exp_word_exp a cs s h
      rw [constFpExp]
      simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
      have hmap : (args.map (fun a => constFpExp a cs)).map (fun a => wordExp s a) =
          args.map (fun a => wordExp s a) := by
        rw [List.map_map]; exact List.map_congr_left (fun a ha => ih a ha)
      rcases hsc : stripConst (args.map (fun a => constFpExp a cs)) with _ | ws
      · simp only
        rw [wordExp_op_eq, wordExp_op_eq, hmap]
      · simp only
        have hst := strip_const_thm _ ws s hsc
        rw [hmap] at hst
        rcases hw : wordOpHOL op ws with _ | w
        · simp only
          rw [wordExp_op_eq, wordExp_op_eq, hst, List.map_map]
          have : (fun a => wordExp s a) ∘ (WordLangExpHOL.const : BitVec width → _) =
              some ∘ WordLocW.word := by
            funext a; simp [Function.comp, wordExp]
          rw [this, the_words_thm]
        · simp only
          rw [wordExp, wordExp_op_eq, hst, the_words_thm]
          simp [hw]
  | .shift sh e e1, cs, s, h => by
      have ih1 := const_fp_exp_word_exp e cs s h
      have ih2 := const_fp_exp_word_exp e1 cs s h
      rw [constFpExp]
      split
      · rename_i c c1 hc hc1
        rw [hc] at ih1; rw [hc1] at ih2
        rw [wordExp] at ih1 ih2
        split
        · rename_i w hw
          rw [wordExp, wordExp, ← ih1, ← ih2]
          simp [hw]
        · rename_i hw
          conv_rhs => rw [wordExp]
          rw [← ih1, ← ih2]
          simp [wordExp, hw]
      · rw [wordExp, wordExp, ih1, ih2]
  | .const _, _, _, _ => by simp only [constFpExp]
  | .lookup _, _, _, _ => by simp only [constFpExp]
  | .load _, _, _, _ => by simp only [constFpExp]
termination_by e => sizeOf e

/-- Exact HOL `const_fp_exp_word_exp_const` (`word_simpProofScript.sml:203-228`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "const_fp_exp_word_exp_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem const_fp_exp_word_exp_const {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (e : WordLangExpHOL (BitVec width)) (cs : Spt (BitVec width))
      (s : WordSemStateFiniteExact width C F) (c : BitVec width),
      (∀ v w, sptLookup v cs = some w → getVar v s = some (.word w)) ∧
        constFpExp e cs = .const c →
        wordExp s e = some (.word c) := by
  intro e cs s c ⟨h, hc⟩
  rw [← const_fp_exp_word_exp e cs s h, hc, wordExp]

theorem sptLookup_sptInsert_eq {α : Type} (k n : Nat) (v : α) (t : Spt α) :
    sptLookup k (sptInsert n v t) = if k = n then some v else sptLookup k t := by
  split
  · subst k; exact sptLookup_sptInsert_same _ _ _
  · exact sptLookup_sptInsert_ne _ _ _ _ (by assumption)

theorem getVar_setVars_eq {width : Nat} [NeZero width] {C : Type} {F : Type}
    (ns : List Nat) (xs : List (WordLocW width)) (s : WordSemStateFiniteExact width C F) (v : Nat) :
    getVar v (setVars ns xs s) = sptLookup v (LoopSemStateFiniteExact.sptAlistInsert ns xs s.locals) :=
  rfl

/-- Exact HOL `set_vars_move_NONE` (`word_simpProofScript.sml:232-242`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "set_vars_move_NONE"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem set_vars_move_NONE {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (moves : List (Nat × Nat)) (x : List (WordLocW width)) (s s' : WordSemStateFiniteExact width C F)
      (v : Nat),
      setVars (moves.map Prod.fst) x s = s' ∧ sptAListLookup v moves = none →
        getVar v s' = getVar v s := by
  intro moves
  induction moves with
  | nil => intro x s s' v ⟨h, _⟩; subst h; rfl
  | cons m ms ih =>
    intro x s s' v ⟨h, hl⟩
    subst h
    rcases m with ⟨q, r⟩
    simp only [sptAListLookup] at hl
    split at hl
    · cases hl
    rename_i hne
    rcases x with _ | ⟨y, ys⟩
    · rfl
    · simp only [List.map_cons, getVar_setVars_eq, LoopSemStateFiniteExact.sptAlistInsert]
      rw [sptLookup_sptInsert_eq, if_neg hne]
      exact ih ys s _ v ⟨rfl, hl⟩

/-- Exact HOL `set_vars_move_SOME` (`word_simpProofScript.sml:244-254`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "set_vars_move_SOME"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem set_vars_move_SOME {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (moves : List (Nat × Nat)) (x : List (WordLocW width)) (v w : Nat)
      (s s' : WordSemStateFiniteExact width C F),
      setVars (moves.map Prod.fst) x s = s' ∧ getVars (moves.map Prod.snd) s = some x ∧
        sptAListLookup v moves = some w →
        getVar v s' = getVar w s := by
  intro moves
  induction moves with
  | nil => intro x v w s s' ⟨_, _, hl⟩; cases hl
  | cons m ms ih =>
    intro x v w s s' ⟨h, hg, hl⟩
    subst h
    rcases m with ⟨q, r⟩
    simp only [List.map_cons, getVars] at hg
    split at hg
    · cases hg
    rename_i y hy
    split at hg
    · cases hg
    rename_i ys hys
    simp only [Option.some.injEq] at hg
    subst hg
    simp only [sptAListLookup] at hl
    simp only [getVar_setVars_eq, List.map_cons, LoopSemStateFiniteExact.sptAlistInsert]
    rw [sptLookup_sptInsert_eq]
    split at hl
    · rename_i hvq
      simp only [Option.some.injEq] at hl
      subst hl
      rw [if_pos hvq]
      exact hy.symm
    · rename_i hvq
      rw [if_neg hvq]
      exact ih ys v w s _ ⟨rfl, hys, hl⟩

/-- Exact HOL `get_var_move_thm` (`word_simpProofScript.sml:256-265`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_move_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_var_move_thm {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (s s' : WordSemStateFiniteExact width C F) (moves : List (Nat × Nat))
      (x : List (WordLocW width)) (v : Nat),
      getVars (moves.map Prod.snd) s = some x ∧ setVars (moves.map Prod.fst) x s = s' →
        getVar v s' =
          match sptAListLookup v moves with
          | some w => getVar w s
          | none => getVar v s := by
  intro s s' moves x v ⟨hg, hs⟩
  rcases hl : sptAListLookup v moves with _ | w
  · exact set_vars_move_NONE moves x s s' v ⟨hs, hl⟩
  · exact set_vars_move_SOME moves x v w s s' ⟨hs, hg, hl⟩

/-- Exact HOL `lookup_const_fp_move_cs_NONE` (`word_simpProofScript.sml:267-284`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_const_fp_move_cs_NONE"
  (words_as_type_indexed_bitvec)]
theorem lookup_const_fp_move_cs_NONE {width : Nat} [NeZero width] :
    ∀ (moves : List (Nat × Nat)) (v : Nat) (cs cs' : Spt (BitVec width)),
      sptAListLookup v moves = none ∧ sptLookup v cs = sptLookup v cs' →
        sptLookup v (constFpMoveCs moves cs cs') = sptLookup v cs' := by
  intro moves
  induction moves with
  | nil => intro v cs cs' _; rfl
  | cons m ms ih =>
    intro v cs cs' ⟨hl, he⟩
    rcases m with ⟨q, r⟩
    simp only [sptAListLookup] at hl
    split at hl
    · cases hl
    rename_i hne
    rcases hc : sptLookup r cs with _ | c <;> simp only [constFpMoveCs, hc]
    · rw [ih v cs _ ⟨hl, by rw [sptLookup_sptDelete, if_neg hne, he]⟩, sptLookup_sptDelete,
        if_neg hne]
    · rw [ih v cs _ ⟨hl, by rw [sptLookup_sptInsert_eq, if_neg hne, he]⟩, sptLookup_sptInsert_eq,
        if_neg hne]

/-- Exact HOL `lookup_const_fp_move_cs_SOME_part` (`word_simpProofScript.sml:286-294`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_const_fp_move_cs_SOME_part"
  (words_as_type_indexed_bitvec)]
theorem lookup_const_fp_move_cs_SOME_part {width : Nat} [NeZero width] :
    ∀ (moves : List (Nat × Nat)) (q : Nat) (cs cs' : Spt (BitVec width)) (x : Option (BitVec width)),
      q ∉ moves.map Prod.fst ∧ sptLookup q cs' = x →
        sptLookup q (constFpMoveCs moves cs cs') = x := by
  intro moves
  induction moves with
  | nil => intro q cs cs' x ⟨_, h⟩; exact h
  | cons m ms ih =>
    intro q cs cs' x ⟨hm, h⟩
    rcases m with ⟨a, b⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hm
    rcases hc : sptLookup b cs with _ | c <;> simp only [constFpMoveCs, hc]
    · exact ih q cs _ x ⟨hm.2, by rw [sptLookup_sptDelete, if_neg hm.1, h]⟩
    · exact ih q cs _ x ⟨hm.2, by rw [sptLookup_sptInsert_eq, if_neg hm.1, h]⟩

/-- Exact HOL `lookup_const_fp_move_cs_SOME` (`word_simpProofScript.sml:296-323`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_const_fp_move_cs_SOME"
  (words_as_type_indexed_bitvec)]
theorem lookup_const_fp_move_cs_SOME {width : Nat} [NeZero width] :
    ∀ (moves : List (Nat × Nat)) (v w : Nat) (cs cs' : Spt (BitVec width)),
      sptAListLookup v moves = some w ∧ (moves.map Prod.fst).Nodup ∧
        sptLookup v cs = sptLookup v cs' →
        sptLookup v (constFpMoveCs moves cs cs') = sptLookup w cs := by
  intro moves
  induction moves with
  | nil => intro v w cs cs' ⟨hl, _⟩; cases hl
  | cons m ms ih =>
    intro v w cs cs' ⟨hl, hnd, he⟩
    rcases m with ⟨q, r⟩
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [sptAListLookup] at hl
    split at hl
    · rename_i hvq
      subst hvq
      simp only [Option.some.injEq] at hl
      subst hl
      rcases hc : sptLookup r cs with _ | c <;> simp only [constFpMoveCs, hc]
      · exact lookup_const_fp_move_cs_SOME_part ms v cs _ _
          ⟨hnd.1, by rw [sptLookup_sptDelete, if_pos rfl]⟩
      · exact lookup_const_fp_move_cs_SOME_part ms v cs _ _
          ⟨hnd.1, by rw [sptLookup_sptInsert_eq, if_pos rfl]⟩
    · rename_i hvq
      rcases hc : sptLookup r cs with _ | c <;> simp only [constFpMoveCs, hc]
      · exact ih v w cs _ ⟨hl, hnd.2, by rw [sptLookup_sptDelete, if_neg hvq, he]⟩
      · exact ih v w cs _ ⟨hl, hnd.2, by rw [sptLookup_sptInsert_eq, if_neg hvq, he]⟩

/-- Exact HOL `lookup_const_fp_move_cs` (`word_simpProofScript.sml:325-334`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_const_fp_move_cs"
  (words_as_type_indexed_bitvec)]
theorem lookup_const_fp_move_cs {width : Nat} [NeZero width] :
    ∀ (v : Nat) (moves : List (Nat × Nat)) (cs : Spt (BitVec width)),
      (moves.map Prod.fst).Nodup →
        sptLookup v (constFpMoveCs moves cs cs) =
          match sptAListLookup v moves with
          | some w => sptLookup w cs
          | none => sptLookup v cs := by
  intro v moves cs hnd
  rcases hl : sptAListLookup v moves with _ | w
  · exact lookup_const_fp_move_cs_NONE moves v cs cs ⟨hl, rfl⟩
  · exact lookup_const_fp_move_cs_SOME moves v w cs cs ⟨hl, hnd, rfl⟩

/-- Exact HOL `get_var_imm_cs_imp_get_var_imm` (`word_simpProofScript.sml:338-344`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_imm_cs_imp_get_var_imm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_var_imm_cs_imp_get_var_imm {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (x : WordRegImm (BitVec width)) (y : BitVec width) (s : WordSemStateFiniteExact width C F)
      (cs : Spt (BitVec width)),
      (∀ v w, sptLookup v cs = some w → getVar v s = some (.word w)) ∧ getVarImmCs x cs = some y →
        getVarImm x s = some (.word y) := by
  intro x y s cs ⟨h, hx⟩
  cases x with
  | reg r => exact h r y hx
  | imm i => simp only [getVarImmCs, Option.some.injEq] at hx; subst hx; rfl

/-- Exact HOL `get_var_set_var_thm` (`word_simpProofScript.sml:348-353`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_set_var_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_var_set_var_thm {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (k1 k2 : Nat) (v : WordLocW width) (s : WordSemStateFiniteExact width C F),
      getVar k1 (setVar k2 v s) = if k1 = k2 then some v else getVar k1 s := by
  intro k1 k2 v s
  exact sptLookup_sptInsert_eq k1 k2 v s.locals

/-- Exact HOL `get_var_mem_store_thm` (`word_simpProofScript.sml:355-360`); HOL's
    free post-state `s'` is an explicit binder. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_var_mem_store_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_var_mem_store_thm {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s' : WordSemStateFiniteExact width C F) :
    ∀ (v : Nat) (addr : BitVec width) (x : WordLocW width) (s : WordSemStateFiniteExact width C F),
      memStore addr x s = some s' → getVar v s' = getVar v s := by
  intro v addr x s h
  have := (memStoreConst addr x s s' h).1
  simp only [getVar, this]

/-- Exact HOL `cs_delete_if_set` (`word_simpProofScript.sml:362-369`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "cs_delete_if_set"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cs_delete_if_set {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (x : WordLocW width) (v1 v2 : Nat) (s : WordSemStateFiniteExact width C F)
      (cs : Spt (BitVec width)) (w : BitVec width),
      (∀ v w, sptLookup v cs = some w → getVar v s = some (.word w)) ∧
        sptLookup v2 (sptDelete v1 cs) = some w →
        getVar v2 (setVar v1 x s) = some (.word w) := by
  intro x v1 v2 s cs w ⟨h, hl⟩
  rw [get_var_set_var_thm]
  rw [sptLookup_sptDelete] at hl
  split at hl
  · cases hl
  · rename_i hne
    rw [if_neg hne]
    exact h v2 w hl

/-- Exact HOL `cs_delete_if_set_x2` (`word_simpProofScript.sml:371-378`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "cs_delete_if_set_x2"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cs_delete_if_set_x2 {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (x1 x2 : WordLocW width) (v1 v2 v3 : Nat) (s : WordSemStateFiniteExact width C F)
      (cs : Spt (BitVec width)) (w : BitVec width),
      (∀ v w, sptLookup v cs = some w → getVar v s = some (.word w)) ∧
        sptLookup v3 (sptDelete v2 (sptDelete v1 cs)) = some w →
        getVar v3 (setVar v2 x2 (setVar v1 x1 s)) = some (.word w) := by
  intro x1 x2 v1 v2 v3 s cs w ⟨h, hl⟩
  exact cs_delete_if_set x2 v2 v3 (setVar v1 x1 s) (sptDelete v1 cs) w
    ⟨fun v w' hv => cs_delete_if_set x1 v1 v s cs w' ⟨h, hv⟩, hl⟩

/-- Exact HOL `lookup_inter_eq_some` (`word_simpProofScript.sml:382-387`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_inter_eq_some"]
theorem lookup_inter_eq_some {α : Type} [DecidableEq α] :
    ∀ (m1 m2 : Spt α) (k : Nat) (x : α),
      sptLookup k (sptInterEq m1 m2) = some x → sptLookup k m1 = some x ∧ sptLookup k m2 = some x := by
  intro m1 m2 k x h
  rw [sptLookupInterEq] at h
  rcases h1 : sptLookup k m1 with _ | v <;> rw [h1] at h
  · cases h
  · simp only at h
    split at h
    · rename_i h2; cases h; exact ⟨rfl, h2⟩
    · cases h

/-- Exact HOL `lookup_filter_v_SOME` (`word_simpProofScript.sml:389-393`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_filter_v_SOME"]
theorem lookup_filter_v_SOME {α : Type} :
    ∀ (t : Spt α) (k : Nat) (v : α) (f : α → Bool),
      sptLookup k (sptFilterV f t) = some v → f v = true := by
  intro t k v f h
  rw [sptLookupFilterV] at h
  rcases h1 : sptLookup k t with _ | u <;> rw [h1] at h
  · cases h
  · simp only at h
    split at h
    · rename_i hf; cases h; exact hf
    · cases h

/-- Exact HOL `lookup_filter_v_SOME_imp` (`word_simpProofScript.sml:395-400`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "lookup_filter_v_SOME_imp"]
theorem lookup_filter_v_SOME_imp {α : Type} :
    ∀ (t : Spt α) (k : Nat) (v : α) (f : α → Bool),
      sptLookup k (sptFilterV f t) = some v → sptLookup k t = some v := by
  intro t k v f h
  rw [sptLookupFilterV] at h
  rcases h1 : sptLookup k t with _ | u <;> rw [h1] at h
  · cases h
  · simp only at h
    split at h
    · cases h; rfl
    · cases h

/-- Exact HOL `LIST_REL_prefix` (`word_simpProofScript.sml:404-410`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LIST_REL_prefix"]
theorem LIST_REL_prefix {α β : Type} :
    ∀ (R : α → β → Prop) (l1 l2 : List α) (l1' l2' : List β),
      List.Forall₂ R (l1 ++ l2) (l1' ++ l2') ∧ l1.length = l1'.length → List.Forall₂ R l1 l1' := by
  intro R l1
  induction l1 with
  | nil => intro l2 l1' l2' ⟨_, hl⟩; cases l1' with
    | nil => exact .nil
    | cons _ _ => simp at hl
  | cons a as ih =>
    intro l2 l1' l2' ⟨h, hl⟩
    cases l1' with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.cons_append, List.forall₂_cons] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      exact .cons h.1 (ih l2 bs l2' ⟨h.2, hl⟩)

/-- Exact HOL `LIST_REL_append_left` (`word_simpProofScript.sml:412-419`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LIST_REL_append_left"]
theorem LIST_REL_append_left {α β : Type} :
    ∀ (l0 l1 : List α) (l2 : List β) (R : α → β → Prop),
      List.Forall₂ R (l0 ++ l1) l2 →
        List.Forall₂ R l0 (l2.take l0.length) ∧ List.Forall₂ R l1 (l2.drop l0.length) := by
  intro l0
  induction l0 with
  | nil => intro l1 l2 R h; exact ⟨by simp, by simpa using h⟩
  | cons a as ih =>
    intro l1 l2 R h
    cases l2 with
    | nil => cases h
    | cons b bs =>
      simp only [List.cons_append, List.forall₂_cons] at h
      have := ih l1 bs R h.2
      exact ⟨by simpa using ⟨h.1, this.1⟩, by simpa using this.2⟩

/-- Exact HOL `push_env_set_store_stack` (`word_simpProofScript.sml:423-428`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "push_env_set_store_stack"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem push_env_set_store_stack {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (x1 : Spt (WordLocW width) × Spt (WordLocW width))
      (x2 : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) (x3 : WordStoreHOL)
      (x4 : WordLocW width) (s : WordSemStateFiniteExact width C F),
      (pushEnv x1 x2 (setStore x3 x4 s)).stack = (pushEnv x1 x2 s).stack := by
  intro x1 x2 x3 x4 s
  rcases x2 with _ | ⟨_, _, _, _⟩ <;> rfl

end WordSemStateFiniteExact

end Flapjack
