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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem pop_env_stack_gc {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s' : WordSemStateFiniteExact width C F) :
    ∀ s : WordSemStateFiniteExact width C F, popEnv s = some s' → s'.gcFun = s.gcFun :=
  fun s h => (popEnvConst s s' h).2.2.2.2.2.2.2.2.2.2.1

/-- Numeric instances of the generic first-match lookup coincide with the
native Spt association-list lookup. Flapjack infrastructure; no HOL original. -/
private theorem natLookup {β : Type} (values : List (Nat × β)) (key : Nat) :
    values.lookup key = sptAListLookup key values := by
  induction values with
  | nil => rfl
  | cons entry values ih =>
    rcases entry with ⟨name, value⟩
    by_cases equal : key = name
    · subst name; simp [sptAListLookup]
    · simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr equal,
        sptAListLookup, equal, if_false, ih]

/-- Exact HOL `ALOOKUP_LIST_REL_sf_gc_consts` (`word_simpProofScript.sml:436-448`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_LIST_REL_sf_gc_consts"
  (words_as_type_indexed_bitvec)]
theorem ALOOKUP_LIST_REL_sf_gc_consts {κ : Type} [DecidableEq κ]
    {width : Nat} [NeZero width] :
    ∀ (l1 l2 : List (κ × WordLocW width)) (k : κ) (v : WordLocW width),
      List.Forall₂ (fun (a b : κ × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) l1 l2 ∧
        isGcWordConst v = true ∧ l1.lookup k = some v →
        l2.lookup k = some v := by
  intro l1 l2 k v ⟨h, hv, hl⟩
  induction h with
  | nil => cases hl
  | @cons a b as bs hab _ ih =>
    rcases a with ⟨ak, av⟩
    rcases b with ⟨bk, bv⟩
    dsimp only at hab
    obtain ⟨equal, hgc⟩ := hab
    subst bk
    by_cases hk : k = ak
    · simp [hk] at hl
      subst v
      simpa [hk] using hgc hv
    · simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hk] using
        ih (by simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hk] using hl)

/-- Full generic HOL lookup law; the key carrier is arbitrary with decidable
HOL equality, and the source's unused binder retains its independent arbitrary type. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_LIST_REL_sf_gc_consts_NONE"
  (words_as_type_indexed_bitvec)]
theorem ALOOKUP_LIST_REL_sf_gc_consts_NONE {κ : Type} [DecidableEq κ]
    {width : Nat} [NeZero width] {ν : Type} (_v : ν) :
    ∀ (l1 l2 : List (κ × WordLocW width)) (k : κ),
      List.Forall₂ (fun (a b : κ × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) l1 l2 ∧
        l1.lookup k = none → l2.lookup k = none := by
  intro l1 l2 k ⟨h, hl⟩
  induction h with
  | nil => rfl
  | @cons a b as bs hab _ ih =>
    rcases a with ⟨ak, av⟩
    rcases b with ⟨bk, bv⟩
    dsimp only at hab
    obtain ⟨equal, -⟩ := hab
    subst bk
    by_cases hk : k = ak
    · simp [hk] at hl
    · simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hk] using
        ih (by simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hk] using hl)

/-- Exact HOL `ALL_DISTINCT_PERM_FST` (`word_simpProofScript.sml:463-470`); HOL's
    free function `f` is an explicit binder. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALL_DISTINCT_PERM_FST"]
theorem ALL_DISTINCT_PERM_FST {α β : Type} (f : List (α × β) → List (α × β)) :
    ∀ l : List (α × β), (l.map Prod.fst).Nodup ∧ holPerm l (f l) → ((f l).map Prod.fst).Nodup := by
  intro l ⟨hnd, hp⟩
  exact (((holPerm_iff _ _).mp hp).map Prod.fst).nodup_iff.mp hnd

/-- Exact HOL `ALOOKUP_LIST_REL_value_rel` (`word_simpProofScript.sml:472-480`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_LIST_REL_value_rel"]
theorem ALOOKUP_LIST_REL_value_rel {κ β : Type} [DecidableEq κ] :
    ∀ (f : β → Prop) (l' l : List (κ × β)) (k : κ) (v : β),
      List.Forall₂ (fun (a b : κ × β) => a.1 = b.1 ∧ (f a.2 → b.2 = a.2)) l' l ∧
        l'.lookup k = some v ∧ f v → l.lookup k = some v := by
  intro f l' l k v ⟨h, hl, hv⟩
  induction h with
  | nil => cases hl
  | @cons a b as bs hab _ ih =>
    rcases a with ⟨ak, av⟩
    rcases b with ⟨bk, bv⟩
    dsimp only at hab
    obtain ⟨equal, hgc⟩ := hab
    subst bk
    by_cases hk : k = ak
    · simp [hk] at hl
      subst v
      simpa [hk] using hgc hv
    · simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hk] using
        ih (by simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr hk] using hl)

/-- Generic first-match lookup of an absent key. Flapjack infrastructure. -/
private theorem lookupNone {κ β : Type} [DecidableEq κ]
    (values : List (κ × β)) (key : κ) (absent : key ∉ values.map Prod.fst) :
    values.lookup key = none := by
  induction values with
  | nil => rfl
  | cons entry values ih =>
    rcases entry with ⟨name, value⟩
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr absent.1]
    exact ih absent.2

/-- Lookup equality under an arbitrary-key distinct-key permutation.
Flapjack proof infrastructure; no separate HOL declaration. -/
private theorem lookupPerm {κ β : Type} [DecidableEq κ]
    (l1 l2 : List (κ × β)) (permutation : l1.Perm l2)
    (distinct : (l1.map Prod.fst).Nodup) (key : κ) : l1.lookup key = l2.lookup key := by
  have distinct2 := (permutation.map Prod.fst).nodup_iff.mp distinct
  by_cases member : key ∈ l1.map Prod.fst
  · obtain ⟨⟨name, value⟩, found, rfl⟩ := List.mem_map.mp member
    rw [allDistinctMemImpALookupSome l1 name value ⟨distinct, found⟩,
      allDistinctMemImpALookupSome l2 name value ⟨distinct2, permutation.mem_iff.mp found⟩]
  · have absent2 : key ∉ l2.map Prod.fst :=
      fun found => member ((permutation.map Prod.fst).mem_iff.mpr found)
    rw [lookupNone l1 key member, lookupNone l2 key absent2]

/-- Full original lookup-function equality with arbitrary HOL key/value types. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_ALL_DISTINCT_FST_PERM"]
theorem ALOOKUP_ALL_DISTINCT_FST_PERM {κ β : Type} [DecidableEq κ] :
    ∀ l1 l2 : List (κ × β), (l1.map Prod.fst).Nodup ∧ holPerm l1 l2 →
      (fun k => l1.lookup k) = (fun k => l2.lookup k) := by
  intro l1 l2 ⟨hnd, hp⟩
  funext k
  exact lookupPerm l1 l2 ((holPerm_iff _ _).mp hp) hnd k

/-- Full original SOME lookup law with arbitrary HOL key/value types. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "ALOOKUP_ALL_DISTINCT_FST_PERM_SOME"]
theorem ALOOKUP_ALL_DISTINCT_FST_PERM_SOME {κ β : Type} [DecidableEq κ] :
    ∀ (l1 : List (κ × β)) (f : List (κ × β) → List (κ × β)) (k : κ) (v : β),
      (l1.map Prod.fst).Nodup ∧ holPerm l1 (f l1) ∧ l1.lookup k = some v →
        (f l1).lookup k = some v := by
  intro l1 f k v ⟨hnd, hp, hl⟩
  rw [← lookupPerm l1 (f l1) ((holPerm_iff _ _).mp hp) hnd k, hl]

/-- Exact HOL `pop_env_gc_fun` (`word_simpProofScript.sml:497-501`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem pop_env_gc_fun {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ s s' : WordSemStateFiniteExact width C F, popEnv s = some s' → s'.gcFun = s.gcFun :=
  fun s s' h => pop_env_stack_gc s' s h

/-- Exact HOL `pop_env_gc_fun_const_ok` (`word_simpProofScript.sml:503-508`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem pop_env_gc_fun_const_ok {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ s s' : WordSemStateFiniteExact width C F,
      popEnv s = some s' ∧ gcFunConstOk s.gcFun → gcFunConstOk s'.gcFun := by
  intro s s' ⟨h, hok⟩
  rw [pop_env_gc_fun s s' h]; exact hok

/-- Exact HOL `evaluate_gc_fun_const_ok` (`word_simpProofScript.sml:516-521`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_gc_fun_const_ok {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate p s = (res, s') ∧ gcFunConstOk s.gcFun → gcFunConstOk s'.gcFun := by
  intro p s res s' ⟨h, hok⟩
  rw [← (evaluate_consts p s res s' h).1]; exact hok

/-- Exact HOL `get_above_handler_def` (`word_simpProofScript.sml:523-526`).  HOL's
    `case` has only the handler-frame clause, so every other frame (and an
    out-of-range `EL`) gives HOL's unspecified value. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
    premise as in HOL.  The two standalone `store`/`store'` finite maps use
    the canonical `HolFiniteMapExact` carrier (named relation entries); the
    `gcFun` binder has the separately tagged, source-reviewed `gc_fun_type`
    alias `WordSemGcFun`, whose nested argument/result maps carry that
    alias's own reviewed slot translation, as for `gc_sf_gc_consts`'s
    `s.gcFun`.  No other difference. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "gc_fun_sf_gc_consts"
  (fmap_as_finite_support_relation := [store, store']) (words_as_type_indexed_bitvec)]
theorem gc_fun_sf_gc_consts {width : Nat} [NeZero width] :
    ∀ (s : List (WordSemStackFrame width)) (s'l : List (WordLocW width))
      (s' : List (WordSemStackFrame width)) (gcFun : WordSemGcFun width)
      (memory memory' : BitVec width → WordLocW width) (mdomain : BitVec width → Bool)
      (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (store' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
      gcFunConstOk gcFun ∧ gcFun (wordSemEncStack s, memory, mdomain, store) = some (s'l, memory', store') ∧
        wordSemDecStack s'l s = some s' →
        List.Forall₂ sfGcConsts s s' := by
  intro s s'l s' gcFun memory memory' mdomain store store' ⟨hok, hg, hd⟩
  exact enc_stack_dec_stack_is_gc_word_const s s' s'l ⟨hok _ _ hg, hd⟩

/-- Exact HOL `gc_sf_gc_consts` (`word_simpProofScript.sml:574-578`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem gc_handler {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ s s' : WordSemStateFiniteExact width C F, gc s = some s' → s'.handler = s.handler :=
  fun s s' h => (gcConst s s' h).2.2.2.2.2.2.2.1

/-- Exact HOL `sf_gc_consts_get_above_handler` (`word_simpProofScript.sml:586-596`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
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
          have transported := ALOOKUP_LIST_REL_sf_gc_consts_NONE w _ _ v
            ⟨hlist, by simpa only [natLookup] using hnone⟩
          rw [show sptAListLookup v _ = none from by simpa only [natLookup] using transported]
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
          have transported := ALOOKUP_LIST_REL_sf_gc_consts _ _ v w
            ⟨hlist, hgc, by simpa only [natLookup] using hsome⟩
          rw [show sptAListLookup v _ = some w from by simpa only [natLookup] using transported]
      · cases h2
    · cases h1
  · cases hcut

section SfGcConsts

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- The conclusion of HOL `evaluate_sf_gc_consts`, case by case on the result
    (untagged rendering of the statement's `case`). -/
noncomputable def sfMotive (s : WordSemStateFiniteExact width C F) :
    Option (WordSemResult width) → WordSemStateFiniteExact width C F → Prop
  | none, s' => List.Forall₂ sfGcConsts s.stack s'.stack ∧ s'.handler = s.handler
  | some (.result _ _), s' => List.Forall₂ sfGcConsts s.stack s'.stack ∧ s'.handler = s.handler
  | some (.exception _ _), s' =>
      s.handler < s.stack.length →
        List.Forall₂ sfGcConsts (wordSemLastN s.handler s.stack) s'.stack ∧
          s'.handler = getAboveHandler s
  | some (.break _), s' => List.Forall₂ sfGcConsts s.stack s'.stack ∧ s'.handler = s.handler
  | some (.continue _), s' => List.Forall₂ sfGcConsts s.stack s'.stack ∧ s'.handler = s.handler
  | some _, _ => True

theorem forall₂_sfGcConsts_refl (l : List (WordSemStackFrame width)) :
    List.Forall₂ sfGcConsts l l :=
  List.forall₂_same.mpr fun x _ => sfGcConstsRefl x

theorem sfMotive_same (s s' : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (hst : s'.stack = s.stack) (hh : s'.handler = s.handler)
    (hres : ∀ x y, res ≠ some (.exception x y)) : sfMotive s res s' := by
  rcases res with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _ <;> simp only [sfMotive] <;>
    first | trivial | exact absurd rfl (hres x y) |
      exact ⟨hst ▸ forall₂_sfGcConsts_refl _, hh⟩

/-- Any result outside `NONE`/`Result`/`Exception`/`Break`/`Continue` satisfies the motive. -/
theorem sfMotive_other (s s' : WordSemStateFiniteExact width C F) (r : WordSemResult width)
    (h : r = .timeOut ∨ r = .notEnoughSpace ∨ (∃ e, r = .finalFfi e) ∨ r = .error) :
    sfMotive s (some r) s' := by
  rcases h with rfl | rfl | ⟨e, rfl⟩ | rfl <;> trivial

theorem sfMotive_shareInst (op : WordMemOp) (v : Nat) (ad : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    sfMotive s (shareInst (rw := width) op v ad s).1 (shareInst (rw := width) op v ad s).2 := by
  cases op <;>
    simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32] <;>
    (repeat' split) <;>
    first
      | (simp only [sfMotive]; done)
      | exact sfMotive_same _ _ _ rfl rfl (fun _ _ h => by cases h)

set_option linter.unusedSimpArgs false in
/-- The permute-constant statements other than `Raise`. -/
theorem sfMotive_const (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgPermuteConst p = true)
    (hr : ∀ n, p ≠ .raise n) :
    sfMotive s (evaluate p s).1 (evaluate p s).2 := by
  cases p <;> simp only [wordProgPermuteConst, Bool.false_eq_true] at hp <;> rw [evaluate] <;>
    (repeat' split) <;>
    first
      | (simp only [sfMotive]; done)
      | exact absurd rfl (hr _)
      | exact sfMotive_same _ _ _ rfl rfl (fun _ _ h => by cases h)
      | exact sfMotive_shareInst _ _ _ _
      | (rename_i h
         have hc := instConstFull _ _ _ h
         exact sfMotive_same _ _ _ hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 (fun _ _ h => by cases h))
      | (rename_i h
         have hc := memStoreConst _ _ _ _ h
         exact sfMotive_same _ _ _ hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1
           (fun _ _ h => by cases h))
      | (dsimp only; split
         · exact sfMotive_same _ _ _ rfl rfl (fun _ _ h => by cases h)
         · simp only [sfMotive])

theorem sfMotive_raise (n : Nat) (s : WordSemStateFiniteExact width C F) :
    sfMotive s (evaluate (.raise n) s).1 (evaluate (.raise n) s).2 := by
  rw [evaluate]
  split
  · simp only [sfMotive]
  · rename_i w hw
    unfold jumpExc
    by_cases hh : s.handler < s.stack.length
    · simp only [hh, if_true]
      rcases hl : wordSemLastN (s.handler + 1) s.stack with _ | ⟨fr, xs⟩
      · simp only [sfMotive]
      · rcases fr with ⟨m, e0, e, _ | ⟨n', l1, l2⟩⟩
        · simp only [sfMotive]
        · simp only [sfMotive]
          intro _
          have hxs := LASTN_TL_res s.stack s.handler _ xs ⟨hh, hl⟩
          refine ⟨hxs ▸ forall₂_sfGcConsts_refl _, ?_⟩
          have hhd := HD_LASTN s.stack (s.handler + 1) ⟨by omega, by omega⟩
          rw [hl] at hhd
          unfold getAboveHandler
          rw [← hhd]
          rfl
    · simp only [hh, if_false, sfMotive]

theorem sfMotive_alloc (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) (hok : gcFunConstOk s.gcFun) :
    sfMotive s (alloc w names s).1 (alloc w names s).2 := by
  unfold alloc
  split
  · simp only [sfMotive]
  · rename_i envs hce
    split
    · simp only [sfMotive]
    · rename_i g hg
      have hrel := gc_sf_gc_consts (pushEnv envs none (setStore .allocSize (.word w) s)) g ⟨hok, hg⟩
      have hgh := gc_handler (pushEnv envs none (setStore .allocSize (.word w) s)) g hg
      split
      · simp only [sfMotive]
      · rename_i p hp
        have hpush : (pushEnv envs none (setStore .allocSize (.word w) s)).stack =
            .stackFrame s.localsSize (sptToAList envs.1)
              (wordSemEnvToList envs.2 s.permute).1 none :: s.stack := rfl
        have hpushh : (pushEnv envs none (setStore .allocSize (.word w) s)).handler = s.handler := rfl
        rw [hpush] at hrel
        have hpst : List.Forall₂ sfGcConsts s.stack p.stack ∧ p.handler = g.handler := by
          unfold popEnv at hp
          generalize hgs : g.stack = gst at hrel hp
          cases hrel with
          | @cons a b as bs hf hrest =>
            rcases b with ⟨m, e0, e, hf''⟩
            obtain ⟨-, -, hfh⟩ := hf
            cases hf'' with
            | some _ => cases hfh
            | none =>
              simp only [Option.some.injEq] at hp
              subst hp
              exact ⟨hrest, rfl⟩
        have hstack : List.Forall₂ sfGcConsts s.stack p.stack := hpst.1
        have hhand : p.handler = s.handler := by rw [hpst.2, hgh, hpushh]
        split
        · simp only [sfMotive]
        · split
          · simp only [sfMotive]
          · exact ⟨hstack, hhand⟩
          · simp only [sfMotive]

theorem wordSemLastN_cons_of_le {α : Type} (n : Nat) (x : α) (l : List α) (h : n ≤ l.length) :
    wordSemLastN n (x :: l) = wordSemLastN n l := by
  rw [wordSemLastN_eq_drop, wordSemLastN_eq_drop]
  simp only [List.length_cons]
  rw [show l.length + 1 - n = (l.length - n) + 1 by omega, List.drop_succ_cons]

/-- Composition of the motive after a step that keeps the stack related and
    the handler. -/
theorem sfMotive_compose {s s1 s2 : WordSemStateFiniteExact width C F} {r : Option (WordSemResult width)}
    (hs : List.Forall₂ sfGcConsts s.stack s1.stack) (hh : s1.handler = s.handler)
    (h2 : sfMotive s1 r s2) : sfMotive s r s2 := by
  have htr : ∀ {l : List (WordSemStackFrame width)}, List.Forall₂ sfGcConsts s1.stack l →
      List.Forall₂ sfGcConsts s.stack l :=
    fun h => forall₂_trans' (fun a b c hab hbc => sfGcConstsTrans a b c ⟨hab, hbc⟩) hs h
  rcases r with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _ <;> simp only [sfMotive] at h2 ⊢
  · exact ⟨htr h2.1, h2.2.trans hh⟩
  · exact ⟨htr h2.1, h2.2.trans hh⟩
  · intro hlt
    have hlen := hs.length_eq
    obtain ⟨hl, hah⟩ := h2 (by rw [hh, ← hlen]; exact hlt)
    refine ⟨?_, ?_⟩
    · rw [hh] at hl
      exact EVERY2_trans_LASTN_sf_gc_consts s.stack s1.stack s2.stack s.handler True
        ⟨by omega, hs, hl⟩
    · rw [hah]; exact sf_gc_consts_get_above_handler s s1 ⟨hs, hh, hlt⟩
  · exact ⟨htr h2.1, h2.2.trans hh⟩
  · exact ⟨htr h2.1, h2.2.trans hh⟩

/-- The motive depends on the start state only through its stack and handler. -/
theorem sfMotive_start_eq {s s' t : WordSemStateFiniteExact width C F} {r : Option (WordSemResult width)}
    (hst : s'.stack = s.stack) (hh : s'.handler = s.handler) (h : sfMotive s' r t) : sfMotive s r t := by
  exact sfMotive_compose (hst ▸ forall₂_sfGcConsts_refl s.stack) hh h

/-- The motive depends on the end state only through its stack and handler. -/
theorem sfMotive_end_eq {s t t' : WordSemStateFiniteExact width C F} {r : Option (WordSemResult width)}
    (hst : t'.stack = t.stack) (hh : t'.handler = t.handler) (h : sfMotive s r t) : sfMotive s r t' := by
  rcases r with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _ <;> simp only [sfMotive] at h ⊢ <;>
    first | trivial | (rw [hst, hh]; exact h)

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `evaluate_sf_gc_consts`, by recursion on HOL's
    termination measure following `evaluate_ind`. -/
theorem sf_aux :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      gcFunConstOk s.gcFun → sfMotive s (evaluate p s).1 (evaluate p s).2
  | .mustTerminate q, s, hok => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      by_cases hz : s.termdep = 0
      · simp only [hz, dite_true, if_true, sfMotive]
      · simp only [hz, dite_false, if_false]
        have ih := sf_aux q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } hok
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at ih
        have ih' := sfMotive_start_eq (s := s) rfl rfl ih
        cases r with
        | none => exact sfMotive_end_eq rfl rfl ih'
        | some x => cases x <;> first | (simp only [sfMotive]; done) | exact sfMotive_end_eq rfl rfl ih'
  | .seq c1 c2, s, hok => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      have ih1 := sf_aux c1 s hok
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at ih1
      have hc := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none =>
        have hok1 : gcFunConstOk s1.gcFun := evaluate_gc_fun_const_ok c1 s none s1 ⟨h1, hok⟩
        exact sfMotive_compose ih1.1 ih1.2 (sf_aux c2 s1 hok1)
      | some x => exact ih1
  | .ite cmp r1 ri c1 c2, s, hok => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      rcases getVar r1 s with _ | x <;> rcases getVarImm ri s with _ | y <;> simp only <;>
        try (simp only [sfMotive]; done)
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only
      · simp only [sfMotive]
      · exact sf_aux c2 s hok
      · exact sf_aux c1 s hok
  | .loop names c exitNames, s, hok => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · simp only [sfMotive]
      simp only
      obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      have ih := sf_aux c { s with locals := l } hok
      rcases hb : evaluate c { s with locals := l } with ⟨rb, s1⟩
      rw [hb] at ih
      have ih' := sfMotive_start_eq (s := s) rfl rfl ih
      have hcl := evaluate_clock c _ rb s1 hb
      have hok1 : gcFunConstOk s1.gcFun := evaluate_gc_fun_const_ok c _ rb s1 ⟨hb, hok⟩
      simp only
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        have hrel : List.Forall₂ sfGcConsts s.stack s1.stack ∧ s1.handler = s.handler := by
          rcases rb with _ | ⟨_ | _ | _ | k | _ | _ | _ | _⟩ <;>
            simp [wordSemContLoop] at hcont <;> simpa only [sfMotive] using ih'
        by_cases hz : s1.clock = 0
        · simp only [hz, dite_true, if_true, sfMotive]
        · simp only [hz, dite_false, if_false, wordSemSTOP]
          exact sfMotive_compose hrel.1 hrel.2
            (sf_aux (.loop names c exitNames) (decClock s1) hok1)
      · simp only [hcont, Bool.false_eq_true, if_false]
        split
        · rcases hce : cutState (exitNames, .ln) s1 with _ | s2
          · simp only [sfMotive]
          · obtain ⟨_, rfl⟩ := cutStateConst _ _ _ hce
            simp only [sfMotive] at ih' ⊢
            exact ih'
        · rename_i hnb
          rcases rb with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _ <;>
            simp only [wordSemExitLoop, wordSemContLoop] at hcont ⊢ <;>
            first | (simp only [sfMotive]; done) | exact ih'
  | .call ret dest args handler, s, hok => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht]
      rcases hg : getVars args s with _ | xs
      · simp only [sfMotive]
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true, sfMotive]
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · simp only [sfMotive]
      simp only
      cases ret with
      | none =>
        cases handler with
        | some _ => simp only [sfMotive]
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · simp only [hz, dite_true, if_true, sfMotive]
          simp only [hz, dite_false, if_false]
          have ih := sf_aux prog (callEnv args1 ss (decClock s)) hok
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at ih
          have ih' := sfMotive_start_eq (s := s) rfl rfl ih
          simp only
          split
          · simp only [sfMotive]
          · exact ih'
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true, sfMotive]
        simp only [hdc, if_false]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · simp only [sfMotive]
        simp only
        by_cases hz : s.clock = 0
        · rw [if_pos hz]; simp only [sfMotive]
        rw [if_neg hz]
        have hokS : gcFunConstOk (callEnv args1 ss (pushEnv envs handler (decClock s))).gcFun := by
          rcases handler with _ | ⟨_, _, _, _⟩ <;> exact hok
        have ih := sf_aux prog (callEnv args1 ss (pushEnv envs handler (decClock s))) hokS
        rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at ih
        have hc := evaluate_clock prog _ rc s2 hcv
        have hok2 : gcFunConstOk s2.gcFun := evaluate_gc_fun_const_ok prog _ rc s2 ⟨hcv, hokS⟩
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | kk | kk | _ | _ | _ | _
        · simp only [sfMotive]
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true, sfMotive]
          simp only [hx, if_false]
          rcases hp : popEnv s2 with _ | s1
          · simp only [sfMotive]
          simp only
          simp only [sfMotive] at ih
          have hcr := LIST_REL_call_Result (decClock s) s2 s2 s1 envs handler
            ⟨ih.1, hp, ih.2⟩
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
          have hok1 : gcFunConstOk s1.gcFun := pop_env_gc_fun_const_ok s2 s1 ⟨hp, hok2⟩
          split
          · exact sfMotive_compose hcr.1 hcr.2
              (sf_aux retHandler (setVars n ys s1) hok1)
          · simp only [sfMotive]
        · cases handler with
          | none =>
            simp only [sfMotive] at ih ⊢
            intro hlt
            have hpl : (callEnv args1 ss (pushEnv envs none (decClock s))).handler <
                (callEnv args1 ss (pushEnv envs none (decClock s))).stack.length := by
              simp only [callEnv, pushEnv, decClock, List.length_cons]; omega
            obtain ⟨hl, hah⟩ := ih hpl
            refine ⟨?_, ?_⟩
            · have := wordSemLastN_cons_of_le s.handler
                (.stackFrame s.localsSize (sptToAList envs.1)
                  (wordSemEnvToList envs.2 s.permute).1 none) s.stack (by omega)
              simp only [callEnv, pushEnv, decClock] at hl
              rw [this] at hl
              exact hl
            · rw [hah]
              unfold getAboveHandler
              simp only [callEnv, pushEnv, decClock, List.length_cons]
              rw [show s.stack.length + 1 - (s.handler + 1) = (s.stack.length - (s.handler + 1)) + 1
                by omega, holEl_cons_succ]
          | some hv =>
            obtain ⟨n', hprog, l1', l2'⟩ := hv
            simp only
            simp only [sfMotive] at ih
            have hpl := call_env_push_env_dec_clock_handler_length s _ args1 ss envs n' hprog l1' l2' rfl
            obtain ⟨hl, hah⟩ := ih hpl
            have hrel : List.Forall₂ sfGcConsts s.stack s2.stack := by
              have := LASTN_LENGTH_CONS s.stack
                (.stackFrame s.localsSize (sptToAList envs.1) (wordSemEnvToList envs.2 s.permute).1
                  (some (s.handler, l1', l2')))
              simp only [callEnv, pushEnv, decClock] at hl
              rw [this] at hl
              exact hl
            have hh2 : s2.handler = s.handler :=
              get_above_handler_call_env_push_env_dec_clock s _ s2 args1 ss envs n' hprog l1' l2'
                ⟨rfl, hah⟩
            split
            · simp only [sfMotive]
            · split
              · exact sfMotive_compose hrel hh2 (sf_aux hprog (setVar n' y s2) hok2)
              · simp only [sfMotive]
        all_goals simp only [sfMotive]
  | .raise n, s, _ => sfMotive_raise n s
  | .alloc n names, s, hok => by
      rw [evaluate]
      split
      · exact sfMotive_alloc _ names s hok
      · simp only [sfMotive]
  | .skip, s, _ => sfMotive_const s _ rfl (by simp)
  | .move a b, s, _ => sfMotive_const s _ rfl (by simp)
  | .inst a, s, _ => sfMotive_const s _ rfl (by simp)
  | .assign a b, s, _ => sfMotive_const s _ rfl (by simp)
  | .get a b, s, _ => sfMotive_const s _ rfl (by simp)
  | .set a b, s, _ => sfMotive_const s _ rfl (by simp)
  | .store a b, s, _ => sfMotive_const s _ rfl (by simp)
  | .tick, s, _ => sfMotive_const s _ rfl (by simp)
  | .storeConsts a b c d f, s, _ => sfMotive_const s _ rfl (by simp)
  | WordLangProgHOL.return a b, s, _ => sfMotive_const s _ rfl (by simp)
  | WordLangProgHOL.break a, s, _ => sfMotive_const s _ rfl (by simp)
  | WordLangProgHOL.continue a, s, _ => sfMotive_const s _ rfl (by simp)
  | .opCurrHeap a b c, s, _ => sfMotive_const s _ rfl (by simp)
  | .locValue a b, s, _ => sfMotive_const s _ rfl (by simp)
  | .install a b c d f, s, _ => sfMotive_const s _ rfl (by simp)
  | .codeBufferWrite a b, s, _ => sfMotive_const s _ rfl (by simp)
  | .dataBufferWrite a b, s, _ => sfMotive_const s _ rfl (by simp)
  | .ffi a b c d f g, s, _ => sfMotive_const s _ rfl (by simp)
  | .shareInst a b c, s, _ => sfMotive_const s _ rfl (by simp)
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc with ⟨_, _⟩)
    try (rcases hcl with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try simp only [decClock, callEnv, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      true_and] at *
    omega

end SfGcConsts

/-- Exact HOL `evaluate_sf_gc_consts` (`word_simpProofScript.sml:692-893`): the
    complete result-indexed conclusion (stack frames related by `sf_gc_consts`
    and handler kept for `NONE`/`Result`/`Break`/`Continue`; for `Exception`, under
    `s.handler < LENGTH s.stack`, the frames above the handler and
    `get_above_handler`; `T` otherwise), rendered by the untagged `sfMotive`.
    Inherits `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_sf_gc_consts {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s s' : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)),
      evaluate p s = (res, s') ∧ gcFunConstOk s.gcFun → sfMotive s res s' := by
  intro p s s' res ⟨h, hok⟩
  have := sf_aux p s hok
  rw [h] at this
  exact this

end WordSemStateFiniteExact

end Flapjack
