import Flapjack.Compiler.Backend.WordSimp.Proofs.ConstFpLemmas
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwapStack
import Flapjack.Misc.ListEl
import Flapjack.HolArb

/-!
# `word_simpProof`: GC-constant preservation of the stack

Counterpart of `cakeml/compiler/backend/proofs/word_simpProofScript.sml:430-893`
(bead `flapjack-pxn.18.5.15.2.41`): the association-list and stack lemmas,
`get_above_handler`, the GC relation lemmas and `evaluate_sf_gc_consts`, over
the native exact evaluator.  HOL `EL` is the tagged `holEl` (out of range it is
HOL's unspecified value), HOL `HD` is `holHd`, an incomplete HOL `case` is
completed by the shared unspecified `holArb`, and `LASTN` is `wordSemLastN`.
-/

namespace Flapjack

namespace WordSimpGcConstsSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSimpGcConstsSupport

instance wordSemStackFrameNonempty {width : Nat} [NeZero width] :
    Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

namespace WordSemStateFiniteExact

open Compiler.Backend.WordSimp

/-- Exact HOL local `pop_env_stack_gc` (`word_simpProofScript.sml:430-434`); HOL's
    free post-state `s'` is an explicit binder. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "pop_env_stack_gc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pop_env_stack_gc {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s' : WordSemStateFiniteExact width C F) :
    ∀ s : WordSemStateFiniteExact width C F, popEnv s = some s' → s'.gcFun = s.gcFun :=
  fun s h => (popEnvConst s s' h).2.2.2.2.2.2.2.2.2.2.1

/-- Exact HOL `ALOOKUP_LIST_REL_sf_gc_consts` (`word_simpProofScript.sml:436-448`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_LIST_REL_sf_gc_consts"
  (words_as_type_indexed_bitvec)]
theorem ALOOKUP_LIST_REL_sf_gc_consts {width : Nat} [NeZero width] :
    ∀ (l1 l2 : List (Nat × WordLocW width)) (k : Nat) (v : WordLocW width),
      List.Forall₂ (fun (a b : Nat × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) l1 l2 ∧
        isGcWordConst v = true ∧ sptAListLookup k l1 = some v →
        sptAListLookup k l2 = some v := by
  intro l1 l2 k v ⟨h, hv, hl⟩
  induction h with
  | nil => cases hl
  | @cons a b as bs hab _ ih =>
    rcases a with ⟨ak, av⟩
    rcases b with ⟨bk, bv⟩
    obtain ⟨rfl, hgc⟩ := hab
    simp only [sptAListLookup] at hl ⊢
    split at hl
    · rename_i hk
      simp only [Option.some.injEq] at hl
      subst hl
      rw [if_pos hk]; exact congrArg some (hgc hv)
    · rename_i hk
      rw [if_neg hk]
      exact ih hl

/-- Exact HOL `ALOOKUP_LIST_REL_sf_gc_consts_NONE` (`word_simpProofScript.sml:450-461`); HOL's
    unused binder `v` is kept. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_LIST_REL_sf_gc_consts_NONE"
  (words_as_type_indexed_bitvec)]
theorem ALOOKUP_LIST_REL_sf_gc_consts_NONE {width : Nat} [NeZero width]
    (_v : WordLocW width) :
    ∀ (l1 l2 : List (Nat × WordLocW width)) (k : Nat),
      List.Forall₂ (fun (a b : Nat × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) l1 l2 ∧
        sptAListLookup k l1 = none →
        sptAListLookup k l2 = none := by
  intro l1 l2 k ⟨h, hl⟩
  induction h with
  | nil => rfl
  | @cons a b as bs hab _ ih =>
    rcases a with ⟨ak, av⟩
    rcases b with ⟨bk, bv⟩
    obtain ⟨rfl, -⟩ := hab
    simp only [sptAListLookup] at hl ⊢
    split at hl
    · cases hl
    · rename_i hk
      rw [if_neg hk]
      exact ih hl

/-- Exact HOL `ALL_DISTINCT_PERM_FST` (`word_simpProofScript.sml:463-470`); HOL's
    free function `f` is an explicit binder. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALL_DISTINCT_PERM_FST"]
theorem ALL_DISTINCT_PERM_FST {α β : Type} (f : List (α × β) → List (α × β)) :
    ∀ l : List (α × β), (l.map Prod.fst).Nodup ∧ holPerm l (f l) → ((f l).map Prod.fst).Nodup := by
  intro l ⟨hnd, hp⟩
  exact (((holPerm_iff _ _).mp hp).map Prod.fst).nodup_iff.mp hnd

/-- Exact HOL `ALOOKUP_LIST_REL_value_rel` (`word_simpProofScript.sml:472-480`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_LIST_REL_value_rel"]
theorem ALOOKUP_LIST_REL_value_rel {β : Type} :
    ∀ (f : β → Prop) (l' l : List (Nat × β)) (k : Nat) (v : β),
      List.Forall₂ (fun (a b : Nat × β) => a.1 = b.1 ∧ (f a.2 → b.2 = a.2)) l' l ∧
        sptAListLookup k l' = some v ∧ f v →
        sptAListLookup k l = some v := by
  intro f l' l k v ⟨h, hl, hv⟩
  induction h with
  | nil => cases hl
  | @cons a b as bs hab _ ih =>
    rcases a with ⟨ak, av⟩
    rcases b with ⟨bk, bv⟩
    obtain ⟨rfl, hgc⟩ := hab
    simp only [sptAListLookup] at hl ⊢
    split at hl
    · rename_i hk
      simp only [Option.some.injEq] at hl
      subst hl
      rw [if_pos hk]; exact congrArg some (hgc hv)
    · rename_i hk
      rw [if_neg hk]
      exact ih hl

/-- Exact HOL `ALOOKUP_ALL_DISTINCT_FST_PERM` (`word_simpProofScript.sml:482-486`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_ALL_DISTINCT_FST_PERM"]
theorem ALOOKUP_ALL_DISTINCT_FST_PERM {β : Type} :
    ∀ l1 l2 : List (Nat × β), (l1.map Prod.fst).Nodup ∧ holPerm l1 l2 →
      (fun k => sptAListLookup k l1) = (fun k => sptAListLookup k l2) := by
  intro l1 l2 ⟨hnd, hp⟩
  funext k
  exact sptAListLookup_perm l1 l2 ((holPerm_iff _ _).mp hp) hnd k

/-- Exact HOL `ALOOKUP_ALL_DISTINCT_FST_PERM_SOME` (`word_simpProofScript.sml:488-495`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_ALL_DISTINCT_FST_PERM_SOME"]
theorem ALOOKUP_ALL_DISTINCT_FST_PERM_SOME {β : Type} :
    ∀ (l1 : List (Nat × β)) (f : List (Nat × β) → List (Nat × β)) (k : Nat) (v : β),
      (l1.map Prod.fst).Nodup ∧ holPerm l1 (f l1) ∧ sptAListLookup k l1 = some v →
        sptAListLookup k (f l1) = some v := by
  intro l1 f k v ⟨hnd, hp, hl⟩
  rw [← sptAListLookup_perm l1 (f l1) ((holPerm_iff _ _).mp hp) hnd k, hl]

/-- Exact HOL `pop_env_gc_fun` (`word_simpProofScript.sml:497-501`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "pop_env_gc_fun"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pop_env_gc_fun {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ s s' : WordSemStateFiniteExact width C F, popEnv s = some s' → s'.gcFun = s.gcFun :=
  fun s s' h => pop_env_stack_gc s' s h

/-- Exact HOL `pop_env_gc_fun_const_ok` (`word_simpProofScript.sml:503-508`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "pop_env_gc_fun_const_ok"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pop_env_gc_fun_const_ok {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ s s' : WordSemStateFiniteExact width C F,
      popEnv s = some s' ∧ gcFunConstOk s.gcFun → gcFunConstOk s'.gcFun := by
  intro s s' ⟨h, hok⟩
  rw [pop_env_gc_fun s s' h]; exact hok

/-- Exact HOL `evaluate_gc_fun_const_ok` (`word_simpProofScript.sml:516-521`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_gc_fun_const_ok"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_gc_fun_const_ok {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate p s = (res, s') ∧ gcFunConstOk s.gcFun → gcFunConstOk s'.gcFun := by
  intro p s res s' ⟨h, hok⟩
  rw [← (evaluate_consts p s res s' h).1]; exact hok

/-- Exact HOL `get_above_handler_def` (`word_simpProofScript.sml:523-526`).  HOL's
    `case` has only the handler-frame clause, so every other frame (and an
    out-of-range `EL`) gives HOL's unspecified value. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_above_handler_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def getAboveHandler {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) : Nat :=
  match holEl (s.stack.length - (s.handler + 1)) s.stack with
  | .stackFrame _ _ _ (some (h, _, _)) => h
  | _ => holArb Nat

theorem wordSemLastN_eq_drop {α : Type} (n : Nat) (l : List α) :
    wordSemLastN n l = l.drop (l.length - n) := by
  simp only [wordSemLastN, List.take_reverse, List.reverse_reverse]

theorem forall₂_zip_of_values {width : Nat} [NeZero width] :
    ∀ (l : List (Nat × WordLocW width)) (ys : List (WordLocW width)),
      List.Forall₂ (fun a b => isGcWordConst a = true → b = a) (l.map Prod.snd) ys →
      List.Forall₂ (fun (a b : Nat × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) l ((l.map Prod.fst).zip ys)
  | [], [], _ => .nil
  | (_, _) :: l, _ :: ys, .cons h t => .cons ⟨rfl, h⟩ (forall₂_zip_of_values l ys t)

/-- Exact HOL `enc_stack_dec_stack_is_gc_word_const` (`word_simpProofScript.sml:528-561`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "enc_stack_dec_stack_is_gc_word_const"
  (words_as_type_indexed_bitvec)]
theorem enc_stack_dec_stack_is_gc_word_const {width : Nat} [NeZero width] :
    ∀ (s s' : List (WordSemStackFrame width)) (s'l : List (WordLocW width)),
      List.Forall₂ (fun a b => isGcWordConst a = true → b = a) (wordSemEncStack s) s'l ∧
        wordSemDecStack s'l s = some s' →
        List.Forall₂ sfGcConsts s s' := by
  intro s
  induction s with
  | nil =>
    intro s' s'l ⟨h, hd⟩
    cases h
    simp only [wordSemDecStack, Option.some.injEq] at hd
    subst hd; exact .nil
  | cons fr st ih =>
    intro s' s'l ⟨h, hd⟩
    rcases fr with ⟨n, l0, l, hh⟩
    simp only [wordSemEncStack] at h
    simp only [wordSemDecStack] at hd
    split at hd
    · cases hd
    rename_i hlen
    split at hd
    · cases hd
    rename_i s0 hs0
    simp only [Option.some.injEq] at hd
    subst hd
    have hsplit := LIST_REL_append_left (l.map Prod.snd) (wordSemEncStack st) s'l _ h
    rw [List.length_map] at hsplit
    exact .cons ⟨forall₂_zip_of_values l _ hsplit.1, rfl, rfl⟩ (ih s0 _ ⟨hsplit.2, hs0⟩)

/-- Statement-for-statement rendering of HOL `gc_fun_sf_gc_consts`
    (`word_simpProofScript.sml:563-572`), all nine binders and the conjunctive
    premise as in HOL.  Untagged for the same reason as `gcFunConstOk`: the
    reviewed `gc_fun_type` slot translation is currently accepted by the
    reference checker only for `gc_fun_ok_def`. -/
theorem gc_fun_sf_gc_consts {width : Nat} [NeZero width] :
    ∀ (s : List (WordSemStackFrame width)) (s'l : List (WordLocW width))
      (s' : List (WordSemStackFrame width)) (gcFun : WordSemGcFun width)
      (memory memory' : BitVec width → WordLocW width) (mdomain : BitVec width → Bool)
      (store store' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
      gcFunConstOk gcFun ∧ gcFun (wordSemEncStack s, memory, mdomain, store) = some (s'l, memory', store') ∧
        wordSemDecStack s'l s = some s' →
        List.Forall₂ sfGcConsts s s' := by
  intro s s'l s' gcFun memory memory' mdomain store store' ⟨hok, hg, hd⟩
  exact enc_stack_dec_stack_is_gc_word_const s s' s'l ⟨hok _ _ hg, hd⟩

/-- Exact HOL `gc_sf_gc_consts` (`word_simpProofScript.sml:574-578`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "gc_sf_gc_consts"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gc_sf_gc_consts {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ s s' : WordSemStateFiniteExact width C F,
      gcFunConstOk s.gcFun ∧ gc s = some s' → List.Forall₂ sfGcConsts s.stack s'.stack := by
  intro s s' ⟨hok, h⟩
  unfold gc at h
  dsimp only at h
  split at h
  · cases h
  rename_i wl m st hg
  split at h
  · cases h
  rename_i stack hs
  simp only [Option.some.injEq] at h
  subst h
  exact gc_fun_sf_gc_consts s.stack wl stack s.gcFun s.memory m s.mdomain s.store st ⟨hok, hg, hs⟩

/-- Exact HOL `gc_handler` (`word_simpProofScript.sml:580-584`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "gc_handler"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gc_handler {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ s s' : WordSemStateFiniteExact width C F, gc s = some s' → s'.handler = s.handler :=
  fun s s' h => (gcConst s s' h).2.2.2.2.2.2.2.1

/-- Exact HOL `sf_gc_consts_get_above_handler` (`word_simpProofScript.sml:586-596`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "sf_gc_consts_get_above_handler"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem sf_gc_consts_get_above_handler {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ s s' : WordSemStateFiniteExact width C F,
      List.Forall₂ sfGcConsts s.stack s'.stack ∧ s'.handler = s.handler ∧
        s.handler < s.stack.length →
        getAboveHandler s' = getAboveHandler s := by
  intro s s' ⟨h, hh, hlt⟩
  have hlen := h.length_eq
  unfold getAboveHandler
  rw [hh, ← hlen]
  have hi : s.stack.length - (s.handler + 1) < s.stack.length := by omega
  rw [holEl_eq_getElem _ _ hi, holEl_eq_getElem _ _ (hlen ▸ hi)]
  have hrel := (List.forall₂_iff_get.mp h).2 _ hi (hlen ▸ hi)
  simp only [List.get_eq_getElem] at hrel
  generalize s.stack[s.stack.length - (s.handler + 1)] = f1 at hrel
  generalize s'.stack[s.stack.length - (s.handler + 1)] = f2 at hrel
  rcases f1 with ⟨_, _, _, h1⟩
  rcases f2 with ⟨_, _, _, h2⟩
  obtain ⟨-, -, rfl⟩ := hrel
  rcases h1 with _ | ⟨_, _, _⟩ <;> rfl

theorem pushEnv_stack_cons {width : Nat} [NeZero width] {C : Type} {F : Type}
    (env : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    (pushEnv env handler s).stack =
      .stackFrame s.localsSize (sptToAList env.1) (wordSemEnvToList env.2 s.permute).1
        (handler.map (fun h => (s.handler, h.2.2.1, h.2.2.2))) :: s.stack := by
  rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl

/-- Exact HOL `LIST_REL_call_Result` (`word_simpProofScript.sml:598-608`); HOL's
    unused binder `s'` is kept. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LIST_REL_call_Result"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem LIST_REL_call_Result {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (s _s' s'' s''' : WordSemStateFiniteExact width C F)
      (env : Spt (WordLocW width) × Spt (WordLocW width))
      (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)),
      List.Forall₂ sfGcConsts (pushEnv env handler s).stack s''.stack ∧ popEnv s'' = some s''' ∧
        s''.handler = (pushEnv env handler s).handler →
        List.Forall₂ sfGcConsts s.stack s'''.stack ∧ s'''.handler = s.handler := by
  intro s _ s'' s''' env handler ⟨hrel, hpop, hh⟩
  rw [pushEnv_stack_cons] at hrel
  unfold popEnv at hpop
  generalize hst : s''.stack = st at hrel hpop
  rcases hrel with _ | ⟨hf, hrest⟩
  rename_i f'' rest
  rcases f'' with ⟨m, e0, e, hf''⟩
  obtain ⟨-, -, hfh⟩ := hf
  rcases handler with _ | ⟨n, p, l1, l2⟩
  · simp only [Option.map_none] at hfh
    subst hfh
    simp only [Option.some.injEq] at hpop
    subst hpop
    refine ⟨hrest, ?_⟩
    simp only at hh ⊢
    rw [hh]; rfl
  · simp only [Option.map_some] at hfh
    subst hfh
    simp only [Option.some.injEq] at hpop
    subst hpop
    exact ⟨hrest, rfl⟩

/-- Exact HOL `get_above_handler_call_env_push_env_dec_clock`
    (`word_simpProofScript.sml:610-618`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "get_above_handler_call_env_push_env_dec_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem get_above_handler_call_env_push_env_dec_clock {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (s s' s'' : WordSemStateFiniteExact width C F) (args : List (WordLocW width))
      (lsz : Option Nat) (env : Spt (WordLocW width) × Spt (WordLocW width)) (x0 : Nat)
      (x1 : WordLangProgHOL (BitVec width)) (x2 x3 : Nat),
      s' = callEnv args lsz (pushEnv env (some (x0, x1, x2, x3)) (decClock s)) ∧
        s''.handler = getAboveHandler s' →
        s''.handler = s.handler := by
  intro s s' s'' args lsz env x0 x1 x2 x3 ⟨hs, hh⟩
  subst hs
  rw [hh]
  unfold getAboveHandler
  simp only [callEnv, pushEnv, decClock, List.length_cons, Nat.sub_self]
  rfl

/-- Exact HOL `call_env_push_env_dec_clock_handler_length`
    (`word_simpProofScript.sml:620-625`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "call_env_push_env_dec_clock_handler_length"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem call_env_push_env_dec_clock_handler_length {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (s s' : WordSemStateFiniteExact width C F) (args : List (WordLocW width))
      (lsz : Option Nat) (env : Spt (WordLocW width) × Spt (WordLocW width)) (x0 : Nat)
      (x1 : WordLangProgHOL (BitVec width)) (x2 x3 : Nat),
      s' = callEnv args lsz (pushEnv env (some (x0, x1, x2, x3)) (decClock s)) →
        s'.handler < s'.stack.length := by
  intro s s' args lsz env x0 x1 x2 x3 hs
  subst hs
  simp [callEnv, pushEnv, decClock]

/-- Exact HOL `EVERY2_trans_LASTN_sf_gc_consts` (`word_simpProofScript.sml:627-633`);
    HOL's unused binder `R` is kept. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "EVERY2_trans_LASTN_sf_gc_consts"
  (words_as_type_indexed_bitvec)]
theorem EVERY2_trans_LASTN_sf_gc_consts {width : Nat} [NeZero width] :
    ∀ (l l' l'' : List (WordSemStackFrame width)) (n : Nat) (_R : Prop),
      n ≤ l.length ∧ List.Forall₂ sfGcConsts l l' ∧ List.Forall₂ sfGcConsts (wordSemLastN n l') l'' →
        List.Forall₂ sfGcConsts (wordSemLastN n l) l'' := by
  intro l l' l'' n _ ⟨hn, h1, h2⟩
  exact forall₂_trans' (fun a b c hab hbc => sfGcConstsTrans a b c ⟨hab, hbc⟩)
    (listRelLastN sfGcConsts l l' n ⟨hn, h1⟩) h2

/-- Exact HOL `LIST_REL_push_env` (`word_simpProofScript.sml:635-640`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LIST_REL_push_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem LIST_REL_push_env {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (R : WordSemStackFrame width → WordSemStackFrame width → Prop)
      (s s' : WordSemStateFiniteExact width C F) (env : Spt (WordLocW width) × Spt (WordLocW width))
      (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)),
      List.Forall₂ R (pushEnv env h s).stack s'.stack → List.Forall₂ R s.stack s'.stack.tail := by
  intro R s s' env h hrel
  rw [pushEnv_stack_cons] at hrel
  generalize s'.stack = st at hrel ⊢
  rcases hrel with _ | ⟨_, hrest⟩
  exact hrest

/-- Exact HOL `LASTN_LENGTH_CONS` (`word_simpProofScript.sml:642-646`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LASTN_LENGTH_CONS"]
theorem LASTN_LENGTH_CONS {α : Type} : ∀ (l : List α) (h : α), wordSemLastN l.length (h :: l) = l := by
  intro l h
  rw [wordSemLastN_eq_drop]
  simp

/-- Exact HOL `LASTN_TL_res` (`word_simpProofScript.sml:648-652`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "LASTN_TL_res"]
theorem LASTN_TL_res {α : Type} :
    ∀ (l : List α) (n : Nat) (h : α) (t : List α),
      n < l.length ∧ wordSemLastN (n + 1) l = h :: t → t = wordSemLastN n l := by
  intro l n h t ⟨hn, hl⟩
  rw [wordSemLastN_eq_drop] at hl ⊢
  have hk : l.length - n = (l.length - (n + 1)) + 1 := by omega
  rw [hk, ← List.drop_drop, List.drop_one]
  rw [hl]; rfl

/-- Exact HOL `HD_LASTN` (`word_simpProofScript.sml:654-658`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "HD_LASTN"]
theorem HD_LASTN {α : Type} [Nonempty α] :
    ∀ (l : List α) (n : Nat), 0 < n ∧ n ≤ l.length → holHd (wordSemLastN n l) = holEl (l.length - n) l := by
  intro l n ⟨h0, hn⟩
  rw [wordSemLastN_eq_drop, holEl_eq_getElem _ _ (by omega)]
  have : l.drop (l.length - n) = l[l.length - n]'(by omega) :: l.drop (l.length - n + 1) :=
    List.drop_eq_getElem_cons (by omega)
  rw [this]; rfl

theorem sptAListLookup_toAList {β : Type} (t : Spt β) (k : Nat) :
    sptAListLookup k (sptToAList t) = sptLookup k t := by
  rcases h : sptLookup k t with _ | v
  · apply sptAListLookup_none_of_not_mem
    intro hm
    obtain ⟨⟨k', v'⟩, hmem, rfl⟩ := List.mem_map.mp hm
    rw [(sptMemToAList t k' v').mp hmem] at h
    cases h
  · exact sptAListLookup_of_mem _ k v (sptAllDistinctMapFstToAList t) ((sptMemToAList t k v).mpr h)

theorem envToList_alookup {width : Nat} [NeZero width] (e : Spt (WordLocW width))
    (perm : Nat → Nat → Nat) (k : Nat) :
    sptAListLookup k (wordSemEnvToList e perm).1 = sptLookup k e := by
  have hs := (holPerm_iff _ _).mp
    (Basis.Pure.MlList.sortPerm wordSemKeyValCompare (sptToAList e))
  have hnd0 := sptAllDistinctMapFstToAList e
  have hnd1 : (Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList e)).Nodup :=
    List.Nodup.of_map _ ((hs.map Prod.fst).nodup_iff.mp hnd0)
  have hr := (holPerm_iff _ _).mp (permListRearrange (perm 0) _ hnd1)
  have hp : (sptToAList e).Perm (wordSemEnvToList e perm).1 := hs.trans hr
  rw [← sptAListLookup_perm _ _ hp hnd0, sptAListLookup_toAList]

/-- Exact HOL `push_env_pop_env_locals_thm` (`word_simpProofScript.sml:660-690`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "push_env_pop_env_locals_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem push_env_pop_env_locals_thm {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (s s' s'' s''' : WordSemStateFiniteExact width C F)
      (env : Spt (WordLocW width) × Spt (WordLocW width)) (names : WordLangCutsetsHOL)
      (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)),
      wordSemCutEnvs names s.locals = some env ∧ pushEnv env handler s = s' ∧
        List.Forall₂ sfGcConsts s'.stack s''.stack ∧ popEnv s'' = some s''' →
        ∀ v w, getVar v s = some w ∧ isGcWordConst w = true ∧ sptLookup v (allNames names) ≠ none →
          getVar v s''' = some w := by
  intro s s' s'' s''' env names handler ⟨hcut, hpush, hrel, hpop⟩ v w ⟨hv, hgc, hn⟩
  subst hpush
  rw [pushEnv_stack_cons] at hrel
  unfold popEnv at hpop
  generalize hst : s''.stack = st at hrel hpop
  rcases hrel with _ | ⟨hf, hrest⟩
  rename_i f'' rest
  rcases f'' with ⟨m, e0, e, hf''⟩
  obtain ⟨hlist, he0, -⟩ := hf
  subst he0
  have hloc : s'''.locals = sptUnion (sptFromAList e) (sptFromAList (sptToAList env.1)) := by
    rcases hf'' with _ | ⟨_, _, _⟩ <;> simp only [Option.some.injEq] at hpop <;> subst hpop <;> rfl
  -- unpack the cut
  simp only [wordSemCutEnvs, wordSemCutNames] at hcut
  split at hcut
  · rename_i e1 e2 h1 h2
    simp only [Option.some.injEq] at hcut
    subst hcut
    split at h1
    · simp only [Option.some.injEq] at h1
      subst h1
      split at h2
      · simp only [Option.some.injEq] at h2
        subst h2
        show sptLookup v s'''.locals = some w
        rw [hloc, sptLookup_sptUnion, sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList]
        have hv' : sptLookup v s.locals = some w := hv
        rcases hn2 : sptLookup v names.2 with _ | u2
        · -- not in the GC-ed cut: fall back to the kept cut
          have hnone : sptAListLookup v (wordSemEnvToList (sptInter s.locals names.2) s.permute).1 = none := by
            rw [envToList_alookup, sptLookup_sptInterCases, hn2]; split <;> simp_all
          rw [ALOOKUP_LIST_REL_sf_gc_consts_NONE w _ _ v ⟨hlist, hnone⟩]
          simp only
          rw [sptLookup_sptInterCases, hv']
          have hn1 : sptLookup v names.1 ≠ none := by
            intro hn1
            apply hn
            simp only [Compiler.Backend.WordSimp.allNames]
            rw [sptLookup_sptUnion, hn1, hn2]
          rcases h1' : sptLookup v names.1 with _ | u1
          · exact absurd h1' hn1
          · rfl
        · have hsome : sptAListLookup v (wordSemEnvToList (sptInter s.locals names.2) s.permute).1 =
              some w := by
            rw [envToList_alookup, sptLookup_sptInterCases, hv', hn2]
          rw [ALOOKUP_LIST_REL_sf_gc_consts _ _ v w ⟨hlist, hgc, hsome⟩]
      · cases h2
    · cases h1
  · cases hcut

end WordSemStateFiniteExact

end Flapjack
