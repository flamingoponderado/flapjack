module

public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackEq
public import Mathlib.Data.List.Forall2

@[expose] public section

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

namespace WordSemStateFiniteExact

/-- Exact HOL `inc_clock_def` (`wordPropsScript.sml:4443-4445`): adding `n`
    clock ticks. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inc_clock_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def incClock {width : Nat} [NeZero width] {C : Type} {F : Type} (n : Nat)
    (t : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  { t with clock := t.clock + n }

/-- Exact HOL `inc_clock_0` (`wordPropsScript.sml:4447-4450`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inc_clock_0"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem incClock_zero {width : Nat} [NeZero width] {C : Type} {F : Type}
    (t : WordSemStateFiniteExact width C F) : incClock 0 t = t := by
  simp [incClock]

/-- Exact HOL `inc_clock_inc_clock` (`wordPropsScript.sml:4453-4456`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inc_clock_inc_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem incClock_incClock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n m : Nat) (t : WordSemStateFiniteExact width C F) :
    incClock n (incClock m t) = incClock (n + m) t := by
  simp [incClock]
  omega

end WordSemStateFiniteExact

/-- Exact HOL `with_locals_same_clock` (`wordPropsScript.sml:1450-1454`):
    rewriting the locals and clock to their own values is the same as
    rewriting the locals alone. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "with_locals_same_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem withLocalsSameClock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) (l : Spt (WordLocW width)) :
    ({ s with locals := l, clock := s.clock } : WordSemStateFiniteExact width C F) =
      { s with locals := l } := by
  rfl

/-- Exact HOL `word_cmp_Word_Word` (`wordPropsScript.sml:5197-5200`): on two
    word values the comparison is the tagged asm `word_cmp`. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "word_cmp_Word_Word"
  (words_as_type_indexed_bitvec)]
theorem wordCmpWordWord {width : Nat} [NeZero width] (cmp : Cmp)
    (c c' : BitVec width) :
    wordSemWordCmp cmp (.word c) (.word c') =
      some (Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp c c') := by
  cases cmp
  all_goals rfl

namespace WordSemStateFiniteExact

/-- Exact HOL `push_env_dec_clock_stack` (`wordPropsScript.sml:3879`):
    taking a clock tick before pushing an environment leaves `stack_max` and
    the stack list unchanged. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "push_env_dec_clock_stack"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnv_decClock_stack {width : Nat} [NeZero width] {C : Type} {F : Type}
    (y : Spt (WordLocW width) × Spt (WordLocW width))
    (opt : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (t : WordSemStateFiniteExact width C F) :
    (pushEnv y opt (decClock t)).stackMax = (pushEnv y opt t).stackMax ∧
    (pushEnv y opt (decClock t)).stack = (pushEnv y opt t).stack := by
  cases opt with
  | none => simp [pushEnv, decClock]
  | some h => simp [pushEnv, decClock]

end WordSemStateFiniteExact

/-- Exact HOL `OPTION_MAP2_ADD_0` (`wordPropsScript.sml:4019`): adding a
    `SOME 0` on either side leaves the operand alone. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "OPTION_MAP2_ADD_0"]
theorem wordSemOptionAdd_zero (m : Option Nat) :
    wordSemOptionAdd m (some 0) = m ∧ wordSemOptionAdd (some 0) m = m := by
  rcases m with _ | _
  all_goals simp [wordSemOptionAdd]

/-- Exact HOL `stack_size_some_at_least_one` (`wordPropsScript.sml:3896`):
    a computed stack size is at least one. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "stack_size_some_at_least_one"
  (words_as_type_indexed_bitvec)]
theorem stackSizeSomeAtLeastOne {width : Nat} [NeZero width] :
    ∀ (stk : List (WordSemStackFrame width)) (sz : Nat),
      wordSemStackSize stk = some sz → 1 ≤ sz := by
  intro stk
  induction stk with
  | nil =>
    intro sz h
    simp [wordSemStackSize] at h
    omega
  | cons fr rest ih =>
    intro sz h
    change wordSemOptionAdd (wordSemStackSizeFrame fr) (wordSemStackSize rest) = some sz at h
    rcases hf : wordSemStackSizeFrame fr with _ | a
    · rw [hf] at h
      simp [wordSemOptionAdd] at h
    · rcases hs : wordSemStackSize rest with _ | b
      · rw [hf, hs] at h
        simp [wordSemOptionAdd] at h
      · rw [hf, hs] at h
        simp only [wordSemOptionAdd, Option.some.injEq] at h
        have hb := ih b hs
        omega


/-- Exact HOL `dec_stack_stack_size_some_not_none` (`wordPropsScript.sml:3948`):
    refilling a stack whose size is known leaves a known size. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml"
  "dec_stack_stack_size_some_not_none" (words_as_type_indexed_bitvec)]
theorem decStackStackSizeSomeNotNone {width : Nat} [NeZero width] :
    ∀ (xs : List (WordLocW width)) (stk stk' : List (WordSemStackFrame width)) (x : Nat),
      wordSemDecStack xs stk = some stk' ∧ wordSemStackSize stk = some x →
        wordSemStackSize stk' ≠ none := by
  intro xs stk
  induction stk generalizing xs with
  | nil =>
    intro stk' x premises
    obtain ⟨h1, h2⟩ := premises
    cases xs with
    | nil =>
      simp [wordSemDecStack] at h1
      subst h1
      simp [wordSemStackSize]
    | cons _ _ => simp [wordSemDecStack] at h1
  | cons fr rest ih =>
    intro stk' x premises
    obtain ⟨h1, h2⟩ := premises
    cases fr with
    | stackFrame n l0 l handler =>
      simp only [wordSemDecStack] at h1
      change wordSemOptionAdd (wordSemStackSizeFrame (.stackFrame n l0 l handler))
        (wordSemStackSize rest) = some x at h2
      rcases hf : wordSemStackSizeFrame (.stackFrame n l0 l handler) with _ | a
      · rw [hf] at h2
        simp [wordSemOptionAdd] at h2
      · rcases hr : wordSemStackSize rest with _ | b
        · rw [hf, hr] at h2
          simp [wordSemOptionAdd] at h2
        · by_cases hlt : xs.length < l.length
          · simp only [hlt, if_true] at h1
            simp at h1
          · simp only [hlt, if_false] at h1
            cases hstep : wordSemDecStack (xs.drop l.length) rest with
            | none =>
              rw [hstep] at h1
              simp at h1
            | some s =>
              rw [hstep] at h1
              simp only [Option.some.injEq] at h1
              rw [← h1]
              have ihs : wordSemStackSize s ≠ none :=
                ih (xs.drop l.length) s b ⟨hstep, hr⟩
              have hf' : wordSemStackSizeFrame
                  (.stackFrame n l0 ((l.map Prod.fst).zip (xs.take l.length)) handler) =
                  some a := by
                cases handler with
                | none => simpa [wordSemStackSizeFrame] using hf
                | some h => simpa [wordSemStackSizeFrame] using hf
              change wordSemOptionAdd (wordSemStackSizeFrame
                (.stackFrame n l0 ((l.map Prod.fst).zip (xs.take l.length)) handler))
                (wordSemStackSize s) ≠ none
              rw [hf']
              rcases hs : wordSemStackSize s with _ | c
              · exact absurd hs ihs
              · simp [wordSemOptionAdd]

/-- Exact HOL `dec_stack_stack_size_not_none_not_none`
    (`wordPropsScript.sml:3959`): an unknown stack size stays unknown. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml"
  "dec_stack_stack_size_not_none_not_none" (words_as_type_indexed_bitvec)]
theorem decStackStackSizeNotNoneNotNone {width : Nat} [NeZero width] :
    ∀ (xs : List (WordLocW width)) (stk stk' : List (WordSemStackFrame width)),
      wordSemDecStack xs stk = some stk' ∧ wordSemStackSize stk ≠ none →
        wordSemStackSize stk' ≠ none := by
  intro xs stk
  induction stk generalizing xs with
  | nil =>
    intro stk' premises
    obtain ⟨h1, h2⟩ := premises
    cases xs with
    | nil =>
      simp [wordSemDecStack] at h1
      subst h1
      simp [wordSemStackSize]
    | cons _ _ => simp [wordSemDecStack] at h1
  | cons fr rest ih =>
    intro stk' premises
    obtain ⟨h1, h2⟩ := premises
    cases fr with
    | stackFrame n l0 l handler =>
      simp only [wordSemDecStack] at h1
      change wordSemOptionAdd (wordSemStackSizeFrame (.stackFrame n l0 l handler))
        (wordSemStackSize rest) ≠ none at h2
      rcases hf : wordSemStackSizeFrame (.stackFrame n l0 l handler) with _ | a
      · rw [hf] at h2
        simp [wordSemOptionAdd] at h2
      · have hr : wordSemStackSize rest ≠ none := by
          intro hr0
          rw [hf, hr0] at h2
          simp [wordSemOptionAdd] at h2
        by_cases hlt : xs.length < l.length
        · simp only [hlt, if_true] at h1
          simp at h1
        · simp only [hlt, if_false] at h1
          cases hstep : wordSemDecStack (xs.drop l.length) rest with
          | none =>
            rw [hstep] at h1
            simp at h1
          | some s =>
            rw [hstep] at h1
            simp only [Option.some.injEq] at h1
            rw [← h1]
            have ihs : wordSemStackSize s ≠ none :=
              ih (xs.drop l.length) s ⟨hstep, hr⟩
            have hf' : wordSemStackSizeFrame
                (.stackFrame n l0 ((l.map Prod.fst).zip (xs.take l.length)) handler) =
                some a := by
              cases handler with
              | none => simpa [wordSemStackSizeFrame] using hf
              | some h => simpa [wordSemStackSizeFrame] using hf
            change wordSemOptionAdd (wordSemStackSizeFrame
              (.stackFrame n l0 ((l.map Prod.fst).zip (xs.take l.length)) handler))
              (wordSemStackSize s) ≠ none
            rw [hf']
            rcases hs : wordSemStackSize s with _ | c
            · exact absurd hs ihs
            · simp [wordSemOptionAdd]

/-- Exact HOL `dec_stack_stack_size_some_leq` (`wordPropsScript.sml:3970`):
    refilling never grows the stack size. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml"
  "dec_stack_stack_size_some_leq" (words_as_type_indexed_bitvec)]
theorem decStackStackSizeSomeLeq {width : Nat} [NeZero width] :
    ∀ (xs : List (WordLocW width)) (stk stk' : List (WordSemStackFrame width))
      (x y : Nat),
      wordSemDecStack xs stk = some stk' ∧ wordSemStackSize stk = some x ∧
        wordSemStackSize stk' = some y → y ≤ x := by
  intro xs stk
  induction stk generalizing xs with
  | nil =>
    intro stk' x y premises
    obtain ⟨h1, h2, h3⟩ := premises
    cases xs with
    | nil =>
      simp [wordSemDecStack] at h1
      subst h1
      simp [wordSemStackSize] at h2 h3
      omega
    | cons _ _ => simp [wordSemDecStack] at h1
  | cons fr rest ih =>
    intro stk' x y premises
    obtain ⟨h1, h2, h3⟩ := premises
    cases fr with
    | stackFrame n l0 l handler =>
      simp only [wordSemDecStack] at h1
      change wordSemOptionAdd (wordSemStackSizeFrame (.stackFrame n l0 l handler))
        (wordSemStackSize rest) = some x at h2
      rcases hf : wordSemStackSizeFrame (.stackFrame n l0 l handler) with _ | a
      · rw [hf] at h2
        simp [wordSemOptionAdd] at h2
      · rcases hr : wordSemStackSize rest with _ | b
        · rw [hf, hr] at h2
          simp [wordSemOptionAdd] at h2
        · rw [hf, hr] at h2
          simp only [wordSemOptionAdd, Option.some.injEq] at h2
          by_cases hlt : xs.length < l.length
          · simp only [hlt, if_true] at h1
            simp at h1
          · simp only [hlt, if_false] at h1
            cases hstep : wordSemDecStack (xs.drop l.length) rest with
            | none =>
              rw [hstep] at h1
              simp at h1
            | some s =>
              rw [hstep] at h1
              simp only [Option.some.injEq] at h1
              rw [← h1] at h3
              have hf' : wordSemStackSizeFrame
                  (.stackFrame n l0 ((l.map Prod.fst).zip (xs.take l.length)) handler) =
                  some a := by
                cases handler with
                | none => simpa [wordSemStackSizeFrame] using hf
                | some h => simpa [wordSemStackSizeFrame] using hf
              change wordSemOptionAdd (wordSemStackSizeFrame
                (.stackFrame n l0 ((l.map Prod.fst).zip (xs.take l.length)) handler))
                (wordSemStackSize s) = some y at h3
              rw [hf'] at h3
              rcases hs : wordSemStackSize s with _ | c
              · rw [hs] at h3
                simp [wordSemOptionAdd] at h3
              · rw [hs] at h3
                simp only [wordSemOptionAdd, Option.some.injEq] at h3
                have ihs := ih (xs.drop l.length) s b c ⟨hstep, hr, hs⟩
                omega


open Flapjack.Compiler.Backend.BackendProps

/-- The order on `num option` is transitive. -/
theorem optionLe_trans {a b c : Option Nat} (first : optionLe a b) (second : optionLe b c) :
    optionLe a c := by
  rcases a with _ | x
  all_goals rcases b with _ | y
  all_goals rcases c with _ | z
  all_goals simp only [optionLe] at first second ⊢
  all_goals omega

/-- A sum of option sizes is bounded below by its left operand. -/
theorem optionLe_optionAdd_left {a c b : Option Nat}
    (h : optionLe (wordSemOptionAdd a c) b) : optionLe a b := by
  rcases a with _ | x
  all_goals rcases c with _ | y
  all_goals rcases b with _ | z
  all_goals simp only [wordSemOptionAdd, optionLe] at h ⊢
  all_goals omega

/-- A computed stack size is at least one, in the `option_le` order. -/
theorem optionLe_stackSize {width : Nat} [NeZero width]
    (stack : List (WordSemStackFrame width)) : optionLe (some 1) (wordSemStackSize stack) := by
  rcases hs : wordSemStackSize stack with _ | x
  · simp [optionLe]
  · have hx := stackSizeSomeAtLeastOne stack x hs
    simp only [optionLe]
    omega

/-- Exact HOL `flush_state_option_le_stack_max_preserved`
    (`wordPropsScript.sml:3984`): flushing locals and (for `T`) the stack keeps
    the frame-size bound below `stack_max`.  HOL's `let t = flush_state p s in`
    abbreviation is inlined. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml"
  "flush_state_option_le_stack_max_preserved" (words_as_type_indexed_bitvec)]
theorem flushStateOptionLeStackMaxPreserved {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : WordSemStateFiniteExact width C F) (all : Bool) :
    optionLe (wordSemOptionAdd (wordSemStackSize state.stack) state.localsSize)
        state.stackMax →
      (let t := WordSemStateFiniteExact.flushState all state
       optionLe (wordSemOptionAdd (wordSemStackSize t.stack) t.localsSize) t.stackMax) := by
  intro h
  dsimp only
  cases all with
  | true =>
    simpa [WordSemStateFiniteExact.flushState, wordSemStackSize, wordSemOptionAdd]
      using optionLe_trans (optionLe_stackSize state.stack) (optionLe_optionAdd_left h)
  | false =>
    simpa [WordSemStateFiniteExact.flushState, wordSemOptionAdd_zero]
      using optionLe_optionAdd_left h


/-- Exact HOL `LIST_REL_CONJ2` (`wordPropsScript.sml:1973`): a pointwise
    conjunction splits into the two relations. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "LIST_REL_CONJ2"]
theorem forall₂_conj {α β : Type} (P Q : α → β → Prop) (l1 : List α) (l2 : List β) :
    List.Forall₂ (fun a b => P a b ∧ Q a b) l1 l2 ↔
      List.Forall₂ P l1 l2 ∧ List.Forall₂ Q l1 l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp
    | cons _ _ => simp
  | cons a as ih =>
    cases l2 with
    | nil => simp
    | cons b bs =>
      simp only [List.forall₂_cons, ih]
      constructor
      · intro h
        exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
      · intro h
        exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩

/-- Exact HOL `push_env_stack_max_eq` (`wordPropsScript.sml:4288`): pushing a
    frame sets `stack_max` to the max of the old bound and the new stack size. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "push_env_stack_max_eq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnv_stackMax_eq {width : Nat} [NeZero width] {C : Type} {F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.pushEnv envs handler s).stackMax =
      wordSemOptionMax s.stackMax
        (wordSemStackSize (WordSemStateFiniteExact.pushEnv envs handler s).stack) := by
  cases handler with
  | none => rfl
  | some h =>
    obtain ⟨a, b, c, d⟩ := h
    rfl

end Flapjack
