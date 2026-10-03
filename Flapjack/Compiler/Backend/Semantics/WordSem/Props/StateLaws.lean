import Flapjack.Compiler.Backend.Semantics.WordSem.Env
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackEq
import Mathlib.Data.List.Forall2

/-!
# wordProps variable, store and stack-size laws

Counterparts of the small `cakeml/compiler/backend/semantics/wordPropsScript.sml`
laws that the Word-to-Stack proof cites (bead
`flapjack-pxn.18.5.15.3.27.1.1.4.4`): `mem_list_rearrange` (32),
`set_var_const` (191), `set_var_with_const` (218), `set_store_const` (380),
`get_var_set_var` (1362), `get_vars_length_lemma` (1765), `stack_size_eq`
(1776), `stack_size_eq2` (1785), `s_key_eq_def2` (1841) and
`LASTN_stack_size_SOME` (4003).  HOL's `OPTION_MAP2 $+` is `wordSemOptionAdd`,
`LASTN` is `wordSemLastN`, `LIST_REL` is `List.Forall₂`, and a HOL `bool`
equation between propositions is `↔`.
-/

namespace Flapjack

namespace WordSemStateLawsSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemStateLawsSupport

/-- Exact HOL `mem_list_rearrange` (`wordPropsScript.sml:32-41`): rearranging
    by any `f` keeps exactly the same members. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "mem_list_rearrange"]
theorem memListRearrange {α : Type} :
    ∀ (ls : List α) (x : α) (f : Nat → Nat), x ∈ wordSemListRearrange f ls ↔ x ∈ ls := by
  intro ls x f
  unfold wordSemListRearrange
  split
  · rename_i h
    constructor
    · intro hx
      obtain ⟨⟨i, hi⟩, _, rfl⟩ := List.mem_map.mp hx
      exact List.getElem_mem _
    · intro hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      obtain ⟨i, hi, hfi⟩ := h.2.2 j hj
      refine List.mem_map.mpr ⟨⟨i, List.mem_range.mpr hi⟩, List.mem_attach _ _, ?_⟩
      simp only [hfi]
  · exact Iff.rfl

namespace WordSemStateFiniteExact

/-- Exact HOL `set_var_const` (`wordPropsScript.sml:191-216`): all twenty-two
    original field equalities. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_var_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVarConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : WordLocW width) (z : WordSemStateFiniteExact width C F) :
    (setVar x y z).localsSize = z.localsSize ∧
    (setVar x y z).fpRegs = z.fpRegs ∧
    (setVar x y z).store = z.store ∧
    (setVar x y z).stack = z.stack ∧
    (setVar x y z).stackLimit = z.stackLimit ∧
    (setVar x y z).stackMax = z.stackMax ∧
    (setVar x y z).stackSize = z.stackSize ∧
    (setVar x y z).memory = z.memory ∧
    (setVar x y z).mdomain = z.mdomain ∧
    (setVar x y z).shMdomain = z.shMdomain ∧
    (setVar x y z).permute = z.permute ∧
    (setVar x y z).compile = z.compile ∧
    (setVar x y z).compileOracle = z.compileOracle ∧
    (setVar x y z).codeBuffer = z.codeBuffer ∧
    (setVar x y z).dataBuffer = z.dataBuffer ∧
    (setVar x y z).gcFun = z.gcFun ∧
    (setVar x y z).handler = z.handler ∧
    (setVar x y z).clock = z.clock ∧
    (setVar x y z).termdep = z.termdep ∧
    (setVar x y z).code = z.code ∧
    (setVar x y z).be = z.be ∧
    (setVar x y z).ffi = z.ffi :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

/-- Exact HOL `set_var_with_const` (`wordPropsScript.sml:218-242`): all
    twenty-two original commutations of `set_var` with a field update. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_var_with_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVarWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : WordLocW width) (z : WordSemStateFiniteExact width C F)
    (ls : Option Nat) (fp : HolFiniteMapExact Nat (BitVec 64))
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (xs : List (WordSemStackFrame width)) (sl : Nat) (sm : Option Nat) (ssize : Spt Nat)
    (m : BitVec width → WordLocW width) (md smd : BitVec width → Bool)
    (p : Nat → Nat → Nat)
    (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (cb : WordSemBuffer width 8) (db : WordSemBuffer width width) (g : WordSemGcFun width)
    (hd clk tdep : Nat) (cd : Spt (Nat × WordLangProgHOL (BitVec width))) (b : Bool)
    (ffi : HolFfiState F) :
    setVar x y { z with localsSize := ls } = { setVar x y z with localsSize := ls } ∧
    setVar x y { z with fpRegs := fp } = { setVar x y z with fpRegs := fp } ∧
    setVar x y { z with store := store } = { setVar x y z with store := store } ∧
    setVar x y { z with stack := xs } = { setVar x y z with stack := xs } ∧
    setVar x y { z with stackLimit := sl } = { setVar x y z with stackLimit := sl } ∧
    setVar x y { z with stackMax := sm } = { setVar x y z with stackMax := sm } ∧
    setVar x y { z with stackSize := ssize } = { setVar x y z with stackSize := ssize } ∧
    setVar x y { z with memory := m } = { setVar x y z with memory := m } ∧
    setVar x y { z with mdomain := md } = { setVar x y z with mdomain := md } ∧
    setVar x y { z with shMdomain := smd } = { setVar x y z with shMdomain := smd } ∧
    setVar x y { z with permute := p } = { setVar x y z with permute := p } ∧
    setVar x y { z with compile := c } = { setVar x y z with compile := c } ∧
    setVar x y { z with compileOracle := co } = { setVar x y z with compileOracle := co } ∧
    setVar x y { z with codeBuffer := cb } = { setVar x y z with codeBuffer := cb } ∧
    setVar x y { z with dataBuffer := db } = { setVar x y z with dataBuffer := db } ∧
    setVar x y { z with gcFun := g } = { setVar x y z with gcFun := g } ∧
    setVar x y { z with handler := hd } = { setVar x y z with handler := hd } ∧
    setVar x y { z with clock := clk } = { setVar x y z with clock := clk } ∧
    setVar x y { z with termdep := tdep } = { setVar x y z with termdep := tdep } ∧
    setVar x y { z with code := cd } = { setVar x y z with code := cd } ∧
    setVar x y { z with be := b } = { setVar x y z with be := b } ∧
    setVar x y { z with ffi := ffi } = { setVar x y z with ffi := ffi } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

/-- Exact HOL `set_store_const` (`wordPropsScript.sml:380-405`): all
    twenty-two original field equalities. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "set_store_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setStoreConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : WordStoreHOL) (y : WordLocW width) (z : WordSemStateFiniteExact width C F) :
    (setStore x y z).locals = z.locals ∧
    (setStore x y z).localsSize = z.localsSize ∧
    (setStore x y z).fpRegs = z.fpRegs ∧
    (setStore x y z).stack = z.stack ∧
    (setStore x y z).stackLimit = z.stackLimit ∧
    (setStore x y z).stackMax = z.stackMax ∧
    (setStore x y z).stackSize = z.stackSize ∧
    (setStore x y z).memory = z.memory ∧
    (setStore x y z).mdomain = z.mdomain ∧
    (setStore x y z).shMdomain = z.shMdomain ∧
    (setStore x y z).permute = z.permute ∧
    (setStore x y z).compile = z.compile ∧
    (setStore x y z).compileOracle = z.compileOracle ∧
    (setStore x y z).codeBuffer = z.codeBuffer ∧
    (setStore x y z).dataBuffer = z.dataBuffer ∧
    (setStore x y z).gcFun = z.gcFun ∧
    (setStore x y z).handler = z.handler ∧
    (setStore x y z).clock = z.clock ∧
    (setStore x y z).termdep = z.termdep ∧
    (setStore x y z).code = z.code ∧
    (setStore x y z).be = z.be ∧
    (setStore x y z).ffi = z.ffi :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

/-- Exact HOL `get_var_set_var` (`wordPropsScript.sml:1362-1366`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_var_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarSetVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (v1 v2 : Nat) (x : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    getVar v1 (setVar v2 x s) = if v1 = v2 then some x else getVar v1 s := by
  unfold getVar setVar
  split
  · subst v1; exact sptLookup_sptInsert_same _ _ _
  · exact sptLookup_sptInsert_ne _ _ _ _ (by assumption)

/-- Exact HOL `get_vars_length_lemma` (`wordPropsScript.sml:1765-1773`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "get_vars_length_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarsLengthLemma {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (ls : List Nat) (s : WordSemStateFiniteExact width C F) (y : List (WordLocW width)),
      getVars ls s = some y → y.length = ls.length := by
  intro ls s
  induction ls with
  | nil => intro y h; simp only [getVars, Option.some.injEq] at h; subst h; rfl
  | cons v vs ih =>
    intro y h
    simp only [getVars] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ys hys
        simp only [Option.some.injEq] at h
        subst h
        simp [ih ys hys]

end WordSemStateFiniteExact

/-- Exact HOL `stack_size_eq` (`wordPropsScript.sml:1776-1783`).  HOL's
    wildcards are distinct universally quantified frame lists in each
    conjunct. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "stack_size_eq"
  (words_as_type_indexed_bitvec)]
theorem stackSizeEq {width : Nat} [NeZero width] (n : Option Nat)
    (l0 l l0' l' : List (Nat × WordLocW width)) (handler : Nat × Nat × Nat)
    (stack : List (WordSemStackFrame width)) :
    wordSemStackSize (.stackFrame n l0 l none :: stack) =
        wordSemOptionAdd n (wordSemStackSize stack) ∧
      wordSemStackSize (.stackFrame n l0' l' (some handler) :: stack) =
        wordSemOptionAdd (n.map (fun m => 3 + m)) (wordSemStackSize stack) ∧
      wordSemStackSize ([] : List (WordSemStackFrame width)) = some 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Exact HOL `stack_size_eq2` (`wordPropsScript.sml:1785-1791`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "stack_size_eq2"
  (words_as_type_indexed_bitvec)]
theorem stackSizeEq2 {width : Nat} [NeZero width] (sfrm : WordSemStackFrame width)
    (stack : List (WordSemStackFrame width)) :
    wordSemStackSize (sfrm :: stack) =
        wordSemOptionAdd (wordSemStackSizeFrame sfrm) (wordSemStackSize stack) ∧
      wordSemStackSize ([] : List (WordSemStackFrame width)) = some 1 :=
  ⟨rfl, rfl⟩

/-- Exact HOL `s_key_eq_def2` (`wordPropsScript.sml:1841-1846`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_def2"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqDef2 {width : Nat} [NeZero width] :
    ∀ l1 l2 : List (WordSemStackFrame width),
      WordSemStackEq.sKeyEq l1 l2 ↔ List.Forall₂ WordSemStackEq.sFrameKeyEq l1 l2
  | [], [] => by simp [WordSemStackEq.sKeyEq]
  | [], _ :: _ => by simp [WordSemStackEq.sKeyEq]
  | _ :: _, [] => by simp [WordSemStackEq.sKeyEq]
  | x :: xs, y :: ys => by
      rw [WordSemStackEq.sKeyEq, List.forall₂_cons, sKeyEqDef2 xs ys, and_comm]

/-- Exact HOL `LASTN_stack_size_SOME` (`wordPropsScript.sml:4003-4014`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "LASTN_stack_size_SOME"
  (words_as_type_indexed_bitvec)]
theorem lastNStackSizeSome {width : Nat} [NeZero width] :
    ∀ (n : Nat) (stack stack' : List (WordSemStackFrame width)) (x : Nat),
      wordSemLastN n stack = stack' ∧ wordSemStackSize stack = some x ∧ n ≤ stack.length →
        ∃ y, wordSemStackSize stack' = some y ∧ y ≤ x := by
  intro n stack
  induction stack generalizing n with
  | nil =>
    intro stack' x ⟨h1, h2, _⟩
    subst h1
    simp only [wordSemLastN, List.reverse_nil, List.take_nil] at h2 ⊢
    exact ⟨x, h2, Nat.le_refl _⟩
  | cons fr st ih =>
    intro stack' x ⟨h1, h2, h3⟩
    subst h1
    have hsz : wordSemStackSize (fr :: st) =
        wordSemOptionAdd (wordSemStackSizeFrame fr) (wordSemStackSize st) := rfl
    rw [hsz] at h2
    rcases hf : wordSemStackSizeFrame fr with _ | a <;>
      rcases hs : wordSemStackSize st with _ | b <;>
      simp only [hf, hs, wordSemOptionAdd, reduceCtorEq, Option.some.injEq] at h2
    by_cases hn : n = st.length + 1
    · subst hn
      refine ⟨x, ?_, Nat.le_refl _⟩
      have : wordSemLastN (st.length + 1) (fr :: st) = fr :: st := by
        simp only [wordSemLastN, List.reverse_cons]
        rw [List.take_of_length_le (by simp)]
        simp
      rw [this, hsz, hf, hs, ← h2]
      rfl
    · have hlast : wordSemLastN n (fr :: st) = wordSemLastN n st := by
        simp only [wordSemLastN, List.reverse_cons]
        rw [List.take_append_of_le_length (by simp; simp at h3; omega)]
      obtain ⟨y, hy, hle⟩ := ih n (wordSemLastN n st) b ⟨rfl, hs, by simp at h3; omega⟩
      exact ⟨y, hlast ▸ hy, by omega⟩

end Flapjack
