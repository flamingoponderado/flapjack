import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Leaves
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws
import Flapjack.Misc.Sorting
import Flapjack.Misc.Sptree.Wf
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Basis.Pure.MlList.SortPerm
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup

/-!
# wordProps `permute_swap_lemma2`/`permute_swap_lemma3` family

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:4790-5195`
(bead `flapjack-pxn.18.5.15.2.36`), with the earlier helpers it uses:
`PERM_list_rearrange` (51), `ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME` (72),
`env_to_list_ALL_DISTINCT` (4665) and `env_to_list_ALL_DISTINCT_FST` (4683),
and HOL's `rich_list$list_rel_lastn`.

HOL `PERM` is the tagged `holPerm`, `ALL_DISTINCT` is `List.Nodup`,
`LIST_REL` is `List.Forall₂`, generic `ALOOKUP` is `List.lookup` (with
decidable key equality), its Nat-keyed uses are `sptAListLookup`, and `LASTN` is
`wordSemLastN`.  HOL's `PERM_STACK` is an `Overload`, not a declaration; it is
rendered by the untagged `permStack` below, clause for clause.
-/

namespace Flapjack

namespace WordSemPermuteSwapStackSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemPermuteSwapStackSupport

/-- Exact HOL `rich_list$list_rel_lastn` (`HOL/src/list/src/rich_listScript.sml:4449-4456`). -/
@[hol "HOL/src/list/src/rich_listScript.sml" "list_rel_lastn"]
theorem listRelLastN {α β : Type} :
    ∀ (f : α → β → Prop) (l1 : List α) (l2 : List β) (n : Nat),
      n ≤ l1.length ∧ List.Forall₂ f l1 l2 →
        List.Forall₂ f (wordSemLastN n l1) (wordSemLastN n l2) := by
  intro f l1 l2 n ⟨_, h⟩
  have hlen := h.length_eq
  unfold wordSemLastN
  apply List.forall₂_reverse_iff.mpr
  exact List.forall₂_take n (List.forall₂_reverse_iff.mpr h)

/-- Exact HOL `PERM_list_rearrange` (`wordPropsScript.sml:51-70`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "PERM_list_rearrange"]
theorem permListRearrange {α : Type} :
    ∀ (f : Nat → Nat) (xs : List α), xs.Nodup → holPerm xs (wordSemListRearrange f xs) := by
  intro f xs hnd
  rw [holPerm_iff]
  unfold wordSemListRearrange
  split
  · rename_i h
    have hnd2 : ((List.range xs.length).attach.map
        (fun (p : { i // i ∈ List.range xs.length }) =>
          xs[f p.1]'(h.1.1 p.1 (List.mem_range.mp p.2)))).Nodup := by
      refine List.Nodup.map_on ?_ (List.nodup_range).attach
      intro ⟨i, hi⟩ _ ⟨j, hj⟩ _ hij
      have hi' := List.mem_range.mp hi
      have hj' := List.mem_range.mp hj
      have hfij : f i = f j := (List.Nodup.getElem_inj_iff hnd).mp hij
      exact Subtype.ext (h.1.2 i hi' j hj' hfij)
    refine (List.perm_ext_iff_of_nodup hnd hnd2).mpr ?_
    intro a
    have := memListRearrange xs a f
    unfold wordSemListRearrange at this
    rw [dif_pos h] at this
    exact this.symm
  · exact List.Perm.refl _

/-- In a list with distinct keys, `ALOOKUP` finds exactly the members. -/
theorem sptAListLookup_of_mem {α : Type} :
    ∀ (xs : List (Nat × α)) (x : Nat) (y : α),
      (xs.map Prod.fst).Nodup → (x, y) ∈ xs → sptAListLookup x xs = some y
  | [], _, _, _, h => by cases h
  | (k, v) :: xs, x, y, hnd, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      simp only [sptAListLookup]
      rcases List.mem_cons.mp h with hm | hm
      · cases hm; simp
      · have hne : x ≠ k := by
          intro hx
          exact hnd.1 ⟨(x, y), hm, hx⟩
        simp only [hne, if_false]
        exact sptAListLookup_of_mem xs x y hnd.2 hm

/-- Exact HOL `ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME` (`wordPropsScript.sml:72-81`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME"]
theorem allDistinctMemImpALookupSome {κ α : Type} [DecidableEq κ]
    (xs : List (κ × α)) (x : κ) (y : α) :
    (xs.map Prod.fst).Nodup ∧ (x, y) ∈ xs → xs.lookup x = some y := by
  intro ⟨distinct, member⟩
  induction xs with
  | nil => cases member
  | cons entry xs ih =>
    rcases entry with ⟨k, v⟩
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      simp
    · have different : x ≠ k := by
        intro equal
        exact distinct.1 (List.mem_map.mpr ⟨(x, y), member, equal⟩)
      simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr different]
        using ih distinct.2 member

theorem sptAListLookup_none_of_not_mem {α : Type} :
    ∀ (xs : List (Nat × α)) (x : Nat), x ∉ xs.map Prod.fst → sptAListLookup x xs = none
  | [], _, _ => rfl
  | (k, v) :: xs, x, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp only [sptAListLookup, h.1, if_false]
      exact sptAListLookup_none_of_not_mem xs x h.2

/-- Distinct-key permutations have the same `ALOOKUP`. -/
theorem sptAListLookup_perm {α : Type} (l1 l2 : List (Nat × α)) (hp : l1.Perm l2)
    (hnd : (l1.map Prod.fst).Nodup) (x : Nat) :
    sptAListLookup x l1 = sptAListLookup x l2 := by
  have hnd2 : (l2.map Prod.fst).Nodup := (hp.map Prod.fst).nodup_iff.mp hnd
  by_cases hm : x ∈ l1.map Prod.fst
  · obtain ⟨⟨k, v⟩, hmem, rfl⟩ := List.mem_map.mp hm
    rw [sptAListLookup_of_mem l1 _ v hnd hmem,
      sptAListLookup_of_mem l2 _ v hnd2 (hp.mem_iff.mp hmem)]
  · have hm2 : x ∉ l2.map Prod.fst := fun h => hm ((hp.map Prod.fst).mem_iff.mpr h)
    rw [sptAListLookup_none_of_not_mem l1 x hm, sptAListLookup_none_of_not_mem l2 x hm2]

/-- Exact HOL `PERM_fromAList` (`wordPropsScript.sml:4797-4813`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "PERM_fromAList"]
theorem permFromAList {α : Type} :
    ∀ (l1 l2 : List (Nat × α)),
      holPerm l1 l2 ∧ (l1.map Prod.fst).Nodup → sptFromAList l1 = sptFromAList l2 := by
  intro l1 l2 ⟨hp, hnd⟩
  rw [holPerm_iff] at hp
  refine (sptEqThm _ _ ⟨sptWfFromAList l1, sptWfFromAList l2⟩).mpr ?_
  intro n
  rw [sptLookup_sptFromAList, sptLookup_sptFromAList]
  exact sptAListLookup_perm l1 l2 hp hnd n

/-- HOL `PERM_STACK` (`wordPropsScript.sml:4790-4793`, an `Overload`):
    frames agree on locals size, handler and kept list, and the GC-ed
    environment of the first is a permutation of the second with distinct
    keys.  Untagged rendering of the overloaded abbreviation. -/
def permStack {width : Nat} [NeZero width] :
    WordSemStackFrame width → WordSemStackFrame width → Prop
  | .stackFrame ss l env h, .stackFrame ss' l' env' h' =>
      ss = ss' ∧ h = h' ∧ l = l' ∧ holPerm env env' ∧ (env.map Prod.fst).Nodup

/-- Exact HOL `stack_size_perm` (`wordPropsScript.sml:4815-4825`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "stack_size_perm"
  (words_as_type_indexed_bitvec)]
theorem stackSizePerm {width : Nat} [NeZero width] :
    ∀ (l1 l2 : List (WordSemStackFrame width)),
      List.Forall₂ permStack l1 l2 → wordSemStackSize l1 = wordSemStackSize l2 := by
  intro l1 l2 h
  induction h with
  | nil => rfl
  | @cons a b as bs hab _ ih =>
    rcases a with ⟨ss, l, env, ha⟩
    rcases b with ⟨ss', l', env', hb⟩
    obtain ⟨rfl, rfl, -, -, -⟩ := hab
    show wordSemOptionAdd _ (wordSemStackSize as) = wordSemOptionAdd _ (wordSemStackSize bs)
    rw [ih]
    cases ha <;> rfl

/-- Exact HOL `env_to_list_ALL_DISTINCT` (`wordPropsScript.sml:4665-4681`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "env_to_list_ALL_DISTINCT"
  (words_as_type_indexed_bitvec)]
theorem envToListAllDistinct {width : Nat} [NeZero width] (y : Spt (WordLocW width))
    (perm : Nat → Nat → Nat) (vs : List (Nat × WordLocW width)) (other : Nat → Nat → Nat) :
    wordSemEnvToList y perm = (vs, other) → (vs.map Prod.fst).Nodup := by
  intro h
  simp only [wordSemEnvToList, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hs := (holPerm_iff _ _).mp
    (Basis.Pure.MlList.sortPerm wordSemKeyValCompare (sptToAList y))
  have hnd0 := sptAllDistinctMapFstToAList y
  have hnd1 : ((Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList y)).map
      Prod.fst).Nodup := (hs.map Prod.fst).nodup_iff.mp hnd0
  have hr := (holPerm_iff _ _).mp (permListRearrange (perm 0) _ (List.Nodup.of_map _ hnd1))
  exact (hr.map Prod.fst).nodup_iff.mp hnd1

/-- Exact HOL `env_to_list_ALL_DISTINCT_FST` (`wordPropsScript.sml:4683-4688`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "env_to_list_ALL_DISTINCT_FST"
  (words_as_type_indexed_bitvec)]
theorem envToListAllDistinctFst {width : Nat} [NeZero width] (y : Spt (WordLocW width))
    (perm : Nat → Nat → Nat) :
    ((wordSemEnvToList y perm).1.map Prod.fst).Nodup :=
  envToListAllDistinct y perm _ (wordSemEnvToList y perm).2 rfl

/-- Exact HOL `env_to_list_PERM` (`wordPropsScript.sml:4827-4842`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "env_to_list_PERM"
  (words_as_type_indexed_bitvec)]
theorem envToListPerm {width : Nat} [NeZero width] (env : Spt (WordLocW width))
    (perm perm' : Nat → Nat → Nat) :
    holPerm (wordSemEnvToList env perm).1 (wordSemEnvToList env perm').1 := by
  rw [holPerm_iff]
  simp only [wordSemEnvToList]
  have hs := (holPerm_iff _ _).mp
    (Basis.Pure.MlList.sortPerm wordSemKeyValCompare (sptToAList env))
  have hnd0 := sptAllDistinctMapFstToAList env
  have hnd1 : (Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList env)).Nodup :=
    List.Nodup.of_map _ ((hs.map Prod.fst).nodup_iff.mp hnd0)
  exact ((holPerm_iff _ _).mp (permListRearrange (perm 0) _ hnd1)).symm.trans
    ((holPerm_iff _ _).mp (permListRearrange (perm' 0) _ hnd1))

namespace WordSemStateFiniteExact

section StackConst

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem cutState_withStack (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (names : WordLangCutsetsHOL) :
    cutState names { s with stack := k } =
      (cutState names s).map (fun s' => { s' with stack := k }) := by
  unfold cutState
  simp only
  split <;> rfl

/-- The stack a swapped run ends with: emptied exactly where the original run
    flushes it, and otherwise the swapped input stack. -/
def stackOut (s' : WordSemStateFiniteExact width C F) (k : List (WordSemStackFrame width)) :
    List (WordSemStackFrame width) :=
  if s'.stack = [] then [] else k

theorem shMemSetVar_withStackOut (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (hs : s.stack ≠ [])
    (res : Option (HolFfiResult F)) (v : Nat) :
    shMemSetVar (rw := width) res v { s with stack := k } =
      ((shMemSetVar (rw := width) res v s).1,
        { (shMemSetVar (rw := width) res v s).2 with
          stack := stackOut (shMemSetVar (rw := width) res v s).2 k }) := by
  cases res with
  | none => simp [shMemSetVar, stackOut, hs]
  | some r => cases r <;> simp [shMemSetVar, stackOut, hs, flushState, setVar]

set_option linter.unusedSimpArgs false in
theorem shareInst_withStackOut (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (hs : s.stack ≠ [])
    (op : WordMemOp) (v : Nat) (ad : BitVec width) :
    shareInst (rw := width) op v ad { s with stack := k } =
      ((shareInst (rw := width) op v ad s).1,
        { (shareInst (rw := width) op v ad s).2 with
          stack := stackOut (shareInst (rw := width) op v ad s).2 k }) := by
  cases op <;> simp only [shareInst, shMemSetVar_withStackOut s k hs] <;>
    simp only [shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32, getVar] <;>
    (repeat' split) <;> first | rfl | simp_all [flushState, setVar, stackOut]

set_option linter.unusedSimpArgs false in
/-- A permute-constant statement other than `Raise` runs the same over any
    replacement of a nonempty stack, ending with `stackOut`. -/
theorem evaluate_withStackOut_const (s : WordSemStateFiniteExact width C F)
    (k : List (WordSemStackFrame width)) (hs : s.stack ≠ [])
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgPermuteConst p = true)
    (hr : ∀ n, p ≠ .raise n) :
    evaluate p { s with stack := k } =
      ((evaluate p s).1, { (evaluate p s).2 with stack := stackOut (evaluate p s).2 k }) := by
  cases p <;> simp only [wordProgPermuteConst, Bool.false_eq_true] at hp <;>
    rw [evaluate, evaluate] <;>
    simp only [getVar, getVars_withStack, wordExp_withStack, inst_withStack,
      shareInst_withStackOut s k hs, memStore_withStack, getStore] <;>
    (repeat' split) <;>
    first
      | rfl
      | (have := (instConstFull _ _ _ ‹inst _ s = some _›).2.2.2.2.2.2.2.2.1
         simp_all [stackOut])
      | (have := (memStoreConst _ _ _ _ ‹memStore _ _ s = some _›).2.2.2.2.2.2.2.2.2.2.2.2.2.1
         simp_all [stackOut])
      | simp_all [flushState, setVar, setVars, setStore, unsetVar, decClock, stackOut]

end StackConst

section SwapHelpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem permStack_fromAList {f1 f2 : WordSemStackFrame width} (h : permStack f1 f2) :
    match f1, f2 with
    | .stackFrame _ _ e _, .stackFrame _ _ e' _ => sptFromAList e = sptFromAList e' := by
  rcases f1 with ⟨_, _, e, _⟩
  rcases f2 with ⟨_, _, e', _⟩
  exact permFromAList e e' ⟨h.2.2.2.1, h.2.2.2.2⟩

theorem jumpExc_swap (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame width)) (hxs : List.Forall₂ permStack xs s.stack) :
    (jumpExc s = none → jumpExc { s with permute := k, stack := xs } = none) ∧
    (∀ s' l1 l2, jumpExc s = some (s', l1, l2) →
      ∃ xs', jumpExc { s with permute := k, stack := xs } =
          some ({ s' with permute := k, stack := xs' }, l1, l2) ∧
        List.Forall₂ permStack xs' s'.stack) := by
  have hlen := hxs.length_eq
  unfold jumpExc
  simp only [hlen]
  by_cases hh : s.handler < s.stack.length
  · simp only [hh, if_true]
    have hl := listRelLastN permStack xs s.stack (s.handler + 1) ⟨by omega, hxs⟩
    generalize wordSemLastN (s.handler + 1) xs = ys at hl
    generalize wordSemLastN (s.handler + 1) s.stack = zs at hl
    cases hl with
    | nil => exact ⟨fun _ => by simp, fun _ _ _ h => (by simp at h)⟩
    | @cons a b as bs hab hrest =>
      rcases a with ⟨m, e0, e, ha⟩
      rcases b with ⟨m', e0', e', hb⟩
      have he := permFromAList e e' ⟨hab.2.2.2.1, hab.2.2.2.2⟩
      obtain ⟨rfl, rfl, rfl, -, -⟩ := hab
      cases ha with
      | none => dsimp only; exact ⟨fun _ => by simp, fun _ _ _ h => (by simp at h)⟩
      | some hv =>
        obtain ⟨n, l1, l2⟩ := hv
        dsimp only
        refine ⟨fun h => (by simp at h), fun s' l1' l2' h => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨as, by rw [he], hrest⟩
  · simp only [hh, if_false]
    exact ⟨fun _ => by simp, fun _ _ _ h => (by simp at h)⟩

theorem popEnv_swap (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame width)) (hxs : List.Forall₂ permStack xs s.stack) :
    (popEnv s = none → popEnv { s with permute := k, stack := xs } = none) ∧
    (∀ s', popEnv s = some s' →
      ∃ xs', popEnv { s with permute := k, stack := xs } =
          some { s' with permute := k, stack := xs' } ∧
        List.Forall₂ permStack xs' s'.stack) := by
  unfold popEnv
  simp only
  generalize s.stack = zs at hxs ⊢
  cases hxs with
  | nil => exact ⟨fun _ => by simp, fun _ h => (by simp at h)⟩
  | @cons a b as bs hab hrest =>
    rcases a with ⟨m, e0, e, ha⟩
    rcases b with ⟨m', e0', e', hb⟩
    have he := permFromAList e e' ⟨hab.2.2.2.1, hab.2.2.2.2⟩
    obtain ⟨rfl, rfl, rfl, -, -⟩ := hab
    cases ha with
    | none =>
      dsimp only
      refine ⟨fun h => (by simp at h), fun s' h => ?_⟩
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨as, by rw [he], hrest⟩
    | some hv =>
      obtain ⟨n, _, _⟩ := hv
      dsimp only
      refine ⟨fun h => (by simp at h), fun s' h => ?_⟩
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨as, by rw [he], hrest⟩

theorem pushEnv_swap (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame width)) (hxs : List.Forall₂ permStack xs s.stack)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    ∃ k' xs', pushEnv envs h { s with permute := k, stack := xs } =
        { pushEnv envs h s with permute := k', stack := xs' } ∧
      List.Forall₂ permStack xs' (pushEnv envs h s).stack := by
  have hlen := hxs.length_eq
  have hframe : ∀ hd, permStack
      (WordSemStackFrame.stackFrame s.localsSize (sptToAList envs.1)
        (wordSemEnvToList envs.2 k).1 hd)
      (WordSemStackFrame.stackFrame s.localsSize (sptToAList envs.1)
        (wordSemEnvToList envs.2 s.permute).1 hd) :=
    fun _ => ⟨rfl, rfl, rfl, envToListPerm envs.2 k s.permute, envToListAllDistinctFst envs.2 k⟩
  rcases h with _ | ⟨_, _, l1, l2⟩
  · have hrel := List.Forall₂.cons (hframe none) hxs
    refine ⟨(wordSemEnvToList envs.2 k).2, _, ?_, hrel⟩
    simp only [pushEnv]
    rw [stackSizePerm _ _ hrel]
  · have hrel := List.Forall₂.cons (hframe (some (s.handler, l1, l2))) hxs
    refine ⟨(wordSemEnvToList envs.2 k).2, _, ?_, hrel⟩
    simp only [pushEnv]
    rw [stackSizePerm _ _ hrel, hlen]

theorem callEnv_swap (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame width)) (hxs : List.Forall₂ permStack xs s.stack)
    (args : List (WordLocW width)) (ss : Option Nat) :
    callEnv args ss { s with permute := k, stack := xs } =
      { callEnv args ss s with permute := k, stack := xs } := by
  simp only [callEnv]
  rw [stackSizePerm _ _ hxs]

theorem cutState_swap (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame width)) (names : WordLangCutsetsHOL) :
    cutState names { s with permute := k, stack := xs } =
      (cutState names s).map (fun s' => { s' with permute := k, stack := xs }) := by
  unfold cutState
  simp only
  split <;> rfl

set_option linter.unusedSimpArgs false in
/-- A permute-constant statement other than `Raise` keeps the stack or
    empties it. -/
theorem evaluate_const_stack (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgPermuteConst p = true)
    (hr : ∀ n, p ≠ .raise n) :
    (evaluate p s).2.stack = s.stack ∨ (evaluate p s).2.stack = [] := by
  cases p <;> simp only [wordProgPermuteConst, Bool.false_eq_true] at hp <;> rw [evaluate] <;>
    (repeat' split) <;>
    first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact absurd rfl (hr _)
      | (left; exact (instConstFull _ _ _ ‹inst _ s = some _›).2.2.2.2.2.2.2.2.1)
      | (left; exact (memStoreConst _ _ _ _ ‹memStore _ _ s = some _›).2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      | (simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
          shMemStore, shMemStoreByte, shMemStore16, shMemStore32]
         repeat' split
         all_goals first | exact Or.inl rfl | exact Or.inr rfl)

end SwapHelpers

section Swap

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem noAlloc_call_ret {n : List Nat} {names : WordLangCutsetsHOL}
    {r : WordLangProgHOL (BitVec width)} {l1 l2 : Nat} {dest : Option Nat} {args : List Nat}
    {h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)}
    (hna : noAllocSubprogsHOL (.call (some (n, names, r, l1, l2)) dest args h) = true) :
    noAllocSubprogsHOL r = true := by
  unfold noAllocSubprogsHOL notCreatedSubprogsWithMemOp at hna
  simp only [Bool.and_eq_true] at hna
  exact hna.1.2

theorem noAlloc_call_handler {ret : Option (List Nat × WordLangCutsetsHOL ×
      WordLangProgHOL (BitVec width) × Nat × Nat)}
    {dest : Option Nat} {args : List Nat} {n : Nat} {hp : WordLangProgHOL (BitVec width)}
    {l1 l2 : Nat}
    (hna : noAllocSubprogsHOL (.call ret dest args (some (n, hp, l1, l2))) = true) :
    noAllocSubprogsHOL hp = true := by
  unfold noAllocSubprogsHOL notCreatedSubprogsWithMemOp at hna
  simp only [Bool.and_eq_true] at hna
  exact hna.2.2

theorem getVars_swap (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame width)) (ns : List Nat) :
    getVars ns { s with permute := k, stack := xs } = getVars ns s := by
  have : ({ s with permute := k, stack := xs } : WordSemStateFiniteExact width C F) =
      { { s with stack := xs } with permute := k } := rfl
  rw [this, getVars_withPermute, getVars_withStack]

/-- Leaf case of the swap recursion: permute-constant statements other than
    `Raise`. -/
theorem swap_const (s : WordSemStateFiniteExact width C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame width)) (hxs : List.Forall₂ permStack xs s.stack)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgPermuteConst p = true)
    (hr : ∀ n, p ≠ .raise n) :
    ∃ k' xs', evaluate p { s with permute := k, stack := xs } =
        ((evaluate p s).1, { (evaluate p s).2 with permute := k', stack := xs' }) ∧
      List.Forall₂ permStack xs' (evaluate p s).2.stack := by
  by_cases hs : s.stack = []
  · rw [hs] at hxs
    cases hxs
    have he : ({ s with permute := k, stack := [] } : WordSemStateFiniteExact width C F) =
        { s with permute := k } := by
      rw [← hs]
    rw [he, evaluate_withPermute_const s k p hp]
    have hst : (evaluate p s).2.stack = [] := by
      rcases evaluate_const_stack s p hp hr with h | h
      · rw [h, hs]
      · exact h
    refine ⟨k, [], ?_, by rw [hst]; exact .nil⟩
    congr 2
    rw [← hst]
  · have hc := evaluate_const_stack s p hp hr
    have he : ({ s with permute := k, stack := xs } : WordSemStateFiniteExact width C F) =
        { { s with stack := xs } with permute := k } := rfl
    rw [he, evaluate_withPermute_const _ k p hp, evaluate_withStackOut_const s xs hs p hp hr]
    refine ⟨k, stackOut (evaluate p s).2 xs, rfl, ?_⟩
    unfold stackOut
    split
    · rename_i h; rw [h]; exact .nil
    · rename_i h
      rcases hc with hc | hc
      · rw [hc]; exact hxs
      · exact absurd hc h

set_option linter.unusedSimpArgs false in
/-- Recursive core of HOL `permute_swap_lemma2`, by recursion on HOL's
    termination measure: running from a state whose permutation oracle is
    replaced and whose stack is `PERM_STACK`-related gives the same result and
    a state differing only in the oracle and a `PERM_STACK`-related stack.
    Each recursive call receives exactly the premises of HOL's induction
    hypothesis; HOL's `res ≠ SOME Error` premise is not needed here. -/
theorem swap_aux :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame width)),
      List.Forall₂ permStack xs s.stack →
      noAllocSubprogsHOL p = true → noInstallSubprogsHOL p = true →
      WordProps.noAllocCode s.code → WordProps.noInstallCode s.code →
      ∃ k' xs', evaluate p { s with permute := k, stack := xs } =
          ((evaluate p s).1, { (evaluate p s).2 with permute := k', stack := xs' }) ∧
        List.Forall₂ permStack xs' (evaluate p s).2.stack
  | .mustTerminate q, s, k, xs, hxs, hna, hni, hca, hci => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.true_and] at hna hni
      by_cases hz : s.termdep = 0
      · simp only [hz, dite_true, if_true]
        exact ⟨k, xs, rfl, hxs⟩
      · simp only [hz, dite_false, if_false]
        obtain ⟨k1, xs1, he, hrel⟩ := swap_aux q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } k xs hxs hna hni hca hci
        have he' : evaluate q { { s with permute := k, stack := xs } with
            clock := wordSemMustTerminateLimit width
            termdep := ({ s with permute := k, stack := xs } :
              WordSemStateFiniteExact width C F).termdep - 1 } = _ := he
        rw [he']
        rcases hq : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at hrel
        cases r with
        | none => exact ⟨k1, xs1, rfl, hrel⟩
        | some x => cases x <;> first | exact ⟨k, xs, rfl, hxs⟩ | exact ⟨k1, xs1, rfl, hrel⟩
  | .seq c1 c2, s, k, xs, hxs, hna, hni, hca, hci => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.and_eq_true] at hna hni
      obtain ⟨k1, xs1, he, hrel⟩ := swap_aux c1 s k xs hxs hna.1 hni.1 hca hci
      have hcode := code_evaluate c1 s hni.1 hci
      rw [he]
      rcases h1 : evaluate c1 s with ⟨r1, s1⟩
      rw [h1] at hrel hcode
      have hc := evaluate_clock c1 s r1 s1 h1
      cases r1 with
      | none =>
        exact swap_aux c2 s1 k1 xs1 hrel hna.2 hni.2 (hcode ▸ hca) (hcode ▸ hci)
      | some x => exact ⟨k1, xs1, rfl, hrel⟩
  | .ite cmp r1 ri c1 c2, s, k, xs, hxs, hna, hni, hca, hci => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [ht, ht]
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.and_eq_true] at hna hni
      have hv : getVar r1 { s with permute := k, stack := xs } = getVar r1 s := rfl
      have hi : getVarImm ri { s with permute := k, stack := xs } = getVarImm ri s := by
        cases ri <;> rfl
      rw [hv, hi]
      rcases getVar r1 s with _ | x <;> rcases getVarImm ri s with _ | y <;> simp only <;>
        try exact ⟨k, xs, rfl, hxs⟩
      rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only
      · exact ⟨k, xs, rfl, hxs⟩
      · exact swap_aux c2 s k xs hxs hna.2 hni.2 hca hci
      · exact swap_aux c1 s k xs hxs hna.1 hni.1 hca hci
  | .loop names c exitNames, s, k, xs, hxs, hna, hni, hca, hci => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hna' := hna
      have hni' := hni
      rw [ht, ht]
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hna' hni'
      rw [cutState_swap]
      rcases hcs : cutState (names, .ln) s with _ | s'
      · exact ⟨k, xs, rfl, hxs⟩
      simp only [Option.map_some]
      obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs
      have hc2 := cutState_clock_termdep _ _ _ hcs
      obtain ⟨k1, xs1, he, hrel⟩ := swap_aux c { s with locals := l } k xs hxs hna' hni' hca hci
      have hcode := code_evaluate c { s with locals := l } hni' hci
      have he' : evaluate c { { s with locals := l } with permute := k, stack := xs } = _ := he
      rw [he']
      rcases hb : evaluate c { s with locals := l } with ⟨rb, s1⟩
      rw [hb] at hrel hcode
      have hcl := evaluate_clock c _ rb s1 hb
      simp only
      by_cases hcont : wordSemContLoop rb = true
      · simp only [hcont, if_true]
        by_cases hz : s1.clock = 0
        · have hz' : ({ s1 with permute := k1, stack := xs1 } :
              WordSemStateFiniteExact width C F).clock = 0 := hz
          simp only [hz, hz', dite_true, if_true]
          exact ⟨k1, [], by simp [flushState, hz], .nil⟩
        · have hz' : ¬ ({ s1 with permute := k1, stack := xs1 } :
              WordSemStateFiniteExact width C F).clock = 0 := hz
          simp only [hz, hz', dite_false, if_false, wordSemSTOP]
          exact swap_aux (.loop names c exitNames) (decClock s1) k1 xs1 hrel hna hni
            (hcode ▸ hca) (hcode ▸ hci)
      · simp only [hcont, Bool.false_eq_true, if_false]
        split
        · rw [cutState_swap]
          rcases hce : cutState (exitNames, .ln) s1 with _ | s2
          · exact ⟨k1, xs1, rfl, hrel⟩
          · obtain ⟨_, rfl⟩ := cutStateConst _ _ _ hce
            exact ⟨k1, xs1, rfl, hrel⟩
        · exact ⟨k1, xs1, rfl, hrel⟩
  | .raise n, s, k, xs, hxs, _, _, _, _ => by
      rw [evaluate, evaluate]
      have hv : getVar n { s with permute := k, stack := xs } = getVar n s := rfl
      rw [hv]
      rcases getVar n s with _ | w
      · exact ⟨k, xs, rfl, hxs⟩
      simp only
      have hj := jumpExc_swap s k xs hxs
      rcases hjs : jumpExc s with _ | ⟨s', l1, l2⟩
      · rw [hj.1 hjs]; exact ⟨k, xs, rfl, hxs⟩
      · obtain ⟨xs', hje, hrel⟩ := hj.2 s' l1 l2 hjs
        rw [hje]
        exact ⟨k, xs', rfl, hrel⟩
  | .alloc a b, s, _, _, _, hna, _, _, _ => by
      simp [noAllocSubprogsHOL, notCreatedSubprogsWithMemOp] at hna
  | .call ret dest args handler, s, k, xs, hxs, hna, hni, hca, hci => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [ht, ht, getVars_swap]
      rcases hg : getVars args s with _ | xs0
      · exact ⟨k, xs, rfl, hxs⟩
      simp only
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true]; exact ⟨k, xs, rfl, hxs⟩
      simp only [hbad, Bool.false_eq_true, if_false]
      rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs0) s.code s.stackSize with
        _ | ⟨args1, prog, ss⟩
      · exact ⟨k, xs, rfl, hxs⟩
      simp only
      have hpa := WordProps.noAllocFindCode s.code dest _ _ _ prog _ ⟨hf, hca⟩
      have hpi := WordProps.noInstallFindCode s.code dest _ _ _ prog _ ⟨hci, hf⟩
      have hdec : decClock ({ s with permute := k, stack := xs } :
          WordSemStateFiniteExact width C F) = { decClock s with permute := k, stack := xs } := rfl
      cases ret with
      | none =>
        cases handler with
        | some _ => exact ⟨k, xs, rfl, hxs⟩
        | none =>
          simp only
          by_cases hz : s.clock = 0
          · have hz' : ({ s with permute := k, stack := xs } :
                WordSemStateFiniteExact width C F).clock = 0 := hz
            rw [if_pos hz', if_pos hz]
            exact ⟨k, [], rfl, .nil⟩
          have hz' : ¬ ({ s with permute := k, stack := xs } :
              WordSemStateFiniteExact width C F).clock = 0 := hz
          simp only [hz, hz', dite_false, if_false]
          rw [hdec, callEnv_swap (decClock s) k xs hxs]
          obtain ⟨k2, xs2, he, hrel⟩ := swap_aux prog (callEnv args1 ss (decClock s)) k xs hxs
            hpa hpi hca hci
          rw [he]
          rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, sc⟩
          rw [hcv] at hrel
          simp only
          split
          · exact ⟨k2, xs2, rfl, hrel⟩
          · exact ⟨k2, xs2, rfl, hrel⟩
      | some rv =>
        obtain ⟨n, names, retHandler, l1, l2⟩ := rv
        simp only
        by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
        · simp only [hdc, if_true]; exact ⟨k, xs, rfl, hxs⟩
        simp only [hdc, if_false]
        have hl : ({ s with permute := k, stack := xs } :
            WordSemStateFiniteExact width C F).locals = s.locals := rfl
        rw [hl]
        rcases hce : wordSemCutEnvs names s.locals with _ | envs
        · exact ⟨k, xs, rfl, hxs⟩
        simp only
        obtain ⟨k1, xs1, hpe, hrel1⟩ := pushEnv_swap (decClock s) k xs hxs envs handler
        by_cases hz : s.clock = 0
        · have hz' : ({ s with permute := k, stack := xs } :
              WordSemStateFiniteExact width C F).clock = 0 := hz
          rw [if_pos hz', if_pos hz]
          obtain ⟨k0, xs0', hpe0, hrel0⟩ := pushEnv_swap s k xs hxs envs handler
          have hsm : (callEnv args1 ss (pushEnv envs handler
              ({ s with permute := k, stack := xs } : WordSemStateFiniteExact width C F))).stackMax =
              (callEnv args1 ss (pushEnv envs handler s)).stackMax := by
            rw [hpe0, callEnv_swap _ k0 xs0' hrel0]
          rw [hsm]
          exact ⟨k, [], rfl, .nil⟩
        have hz' : ¬ ({ s with permute := k, stack := xs } :
            WordSemStateFiniteExact width C F).clock = 0 := hz
        simp only [hz, hz', dite_false, if_false]
        rw [hdec, hpe, callEnv_swap _ k1 xs1 hrel1]
        have hcpre : (callEnv args1 ss (pushEnv envs handler (decClock s))).code = s.code :=
          code_pushEnv envs handler _
        obtain ⟨k2, xs2, he, hrel2⟩ := swap_aux prog
          (callEnv args1 ss (pushEnv envs handler (decClock s))) k1 xs1 hrel1 hpa hpi
          (hcpre ▸ hca) (hcpre ▸ hci)
        have hcode := code_evaluate prog _ hpi (hcpre ▸ hci)
        rw [he]
        rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with
          ⟨rc, s2⟩
        rw [hcv] at hrel2 hcode
        have hc := evaluate_clock prog _ rc s2 hcv
        have h2 : s2.code = s.code := hcode.trans hcpre
        rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | kk | kk | _ | _ | _ | _
        · exact ⟨k2, xs2, rfl, hrel2⟩
        · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
          · simp only [hx, if_true]; exact ⟨k2, xs2, rfl, hrel2⟩
          simp only [hx, if_false]
          have hp := popEnv_swap s2 k2 xs2 hrel2
          rcases hpop : popEnv s2 with _ | s1
          · rw [hp.1 hpop]; exact ⟨k2, xs2, rfl, hrel2⟩
          obtain ⟨xs3, hpe3, hrel3⟩ := hp.2 s1 hpop
          rw [hpe3]
          simp only
          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
            ⟨popEnv_clock _ _ hpop, popEnv_termdep _ _ hpop⟩
          have h3 : s1.code = s.code :=
            ((popEnvConst _ _ hpop).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans h2
          have hlc : ({ s1 with permute := k2, stack := xs3 } :
              WordSemStateFiniteExact width C F).locals = s1.locals := rfl
          rw [hlc]
          split
          · have hsv : setVars n ys ({ s1 with permute := k2, stack := xs3 } :
                WordSemStateFiniteExact width C F) =
                { setVars n ys s1 with permute := k2, stack := xs3 } := rfl
            rw [hsv]
            exact swap_aux retHandler (setVars n ys s1) k2 xs3 hrel3 (noAlloc_call_ret hna)
              (noInstall_call_ret hni) (h3 ▸ hca) (h3 ▸ hci)
          · exact ⟨k2, xs3, rfl, hrel3⟩
        · cases handler with
          | none => exact ⟨k2, xs2, rfl, hrel2⟩
          | some hv =>
            obtain ⟨n', hprog', l1', l2'⟩ := hv
            simp only
            split
            · exact ⟨k2, xs2, rfl, hrel2⟩
            · have hlc : ({ s2 with permute := k2, stack := xs2 } :
                  WordSemStateFiniteExact width C F).locals = s2.locals := rfl
              rw [hlc]
              split
              · have hsv : setVar n' y ({ s2 with permute := k2, stack := xs2 } :
                    WordSemStateFiniteExact width C F) =
                    { setVar n' y s2 with permute := k2, stack := xs2 } := rfl
                rw [hsv]
                exact swap_aux hprog' (setVar n' y s2) k2 xs2 hrel2 (noAlloc_call_handler hna)
                  (noInstall_call_handler hni) (h2 ▸ hca) (h2 ▸ hci)
              · exact ⟨k2, xs2, rfl, hrel2⟩
        all_goals exact ⟨k2, xs2, rfl, hrel2⟩
  | .skip, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .move a b, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .inst a, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .assign a b, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .get a b, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .set a b, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .store a b, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .tick, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .storeConsts a b c d f, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | WordLangProgHOL.return a b, s, k, xs, hxs, _, _, _, _ =>
      swap_const s k xs hxs _ rfl (by simp)
  | WordLangProgHOL.break a, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | WordLangProgHOL.continue a, s, k, xs, hxs, _, _, _, _ =>
      swap_const s k xs hxs _ rfl (by simp)
  | .opCurrHeap a b c, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .locValue a b, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .install a b c d f, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .codeBufferWrite a b, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .dataBufferWrite a b, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .ffi a b c d f g, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
  | .shareInst a b c, s, k, xs, hxs, _, _, _, _ => swap_const s k xs hxs _ rfl (by simp)
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc with ⟨_, _⟩)
    try (rcases hcl with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try (rcases hc3 with ⟨_, _⟩)
    try simp only [decClock, callEnv, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      true_and] at *
    omega

end Swap

/-- Exact HOL `permute_swap_lemma2` (`wordPropsScript.sml:4844-5168`):

    ```
    ∀prog st perm stack.
      let (res,rst) = evaluate(prog,st) in
        res ≠ SOME Error ∧ no_alloc_code st.code ∧ no_alloc prog ∧
        no_install_code st.code ∧ no_install prog ∧
        LIST_REL PERM_STACK stack st.stack
        ⇒
        ∃perm' stack'.
          evaluate(prog,st with <|permute := perm; stack := stack|>) =
            (res,rst with <|permute:=perm'; stack := stack'|>) ∧
          LIST_REL PERM_STACK stack' rst.stack
    ```

    `PERM_STACK` is the untagged rendering `permStack` of HOL's overload.
    Inherits `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem permute_swap_lemma2 {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (perm : Nat → Nat → Nat) (stack : List (WordSemStackFrame width)),
      let (res, rst) := evaluate prog st
      res ≠ some .error ∧ WordProps.noAllocCode st.code ∧ noAllocSubprogsHOL prog = true ∧
        WordProps.noInstallCode st.code ∧ noInstallSubprogsHOL prog = true ∧
        List.Forall₂ permStack stack st.stack →
        ∃ perm' stack', evaluate prog { st with permute := perm, stack := stack } =
            (res, { rst with permute := perm', stack := stack' }) ∧
          List.Forall₂ permStack stack' rst.stack := by
  intro prog st perm stack
  have aux := swap_aux prog st perm stack
  rcases hev : evaluate prog st with ⟨res, rst⟩
  rw [hev] at aux
  rintro ⟨_, hca, hna, hci, hni, hxs⟩
  exact aux hxs hna hni hca hci

/-- Exact HOL `permute_swap_lemma3` (`wordPropsScript.sml:5170-5195`): as
    `permute_swap_lemma2` with the original stack, whose environments have
    distinct keys (HOL `EVERY` over the frames).  HOL's unused binder `stack`
    is kept.  Inherits `reals_as_rational_cuts` through `evaluate`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem permute_swap_lemma3 {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (perm : Nat → Nat → Nat) (_stack : List (WordSemStackFrame width)),
      let (res, rst) := evaluate prog st
      res ≠ some .error ∧ WordProps.noAllocCode st.code ∧ noAllocSubprogsHOL prog = true ∧
        WordProps.noInstallCode st.code ∧ noInstallSubprogsHOL prog = true ∧
        (∀ fr ∈ st.stack, match fr with
          | .stackFrame _ _ vs _ => (vs.map Prod.fst).Nodup) →
        ∃ perm' stack', evaluate prog { st with permute := perm } =
            (res, { rst with permute := perm', stack := stack' }) ∧
          List.Forall₂ permStack stack' rst.stack := by
  intro prog st perm _
  have aux := swap_aux prog st perm st.stack
  rcases hev : evaluate prog st with ⟨res, rst⟩
  rw [hev] at aux
  rintro ⟨_, hca, hna, hci, hni, hd⟩
  have hxs : List.Forall₂ permStack st.stack st.stack := by
    refine List.forall₂_same.mpr fun fr hfr => ?_
    have := hd fr hfr
    rcases fr with ⟨_, _, vs, _⟩
    exact ⟨rfl, rfl, rfl, (holPerm_iff _ _).mpr (List.Perm.refl _), this⟩
  exact aux hxs hna hni hca hci

end WordSemStateFiniteExact

end Flapjack
