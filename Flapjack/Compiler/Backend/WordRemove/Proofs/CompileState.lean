import Flapjack.Compiler.Backend.WordRemove
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateDecClock
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.GcConst
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.AllocConst
import Flapjack.Misc.Sptree.Map

/-!
# `word_removeProof`: the `compile_state` group

Counterpart of `cakeml/compiler/backend/proofs/word_removeProofScript.sml:10-260`:
`compile_state_def` and its `[simp]` commutation lemmas with the wordSem state
operations, over the exact `WordSemStateFiniteExact` carrier.
-/

namespace Flapjack.Compiler.Backend.WordRemove

open Flapjack Flapjack.WordSemStateFiniteExact

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged declarations of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

section CompileState


/-- The type of the wordSem `compile` field. -/
abbrev WordCompileFn (width : Nat) [NeZero width] (C : Type) : Type :=
  C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
    Option (List (BitVec 8) × List (BitVec width) × C)

/-- Exact HOL `compile_state_def` (`word_removeProofScript.sml:10-19`):

    ```
    compile_state clk c s =
      s with <| clock := s.clock+clk; termdep := 0;
                code := map (I ## remove_must_terminate) s.code;
                compile_oracle := (I ## (MAP (I ## I ## remove_must_terminate))) o s.compile_oracle;
                compile := c |>
    ```
-/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "compile_state_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  { s with
    clock := s.clock + clk
    termdep := 0
    code := sptMap (fun p => (p.1, removeMustTerminate p.2)) s.code
    compileOracle := fun n =>
      ((s.compileOracle n).1,
        (s.compileOracle n).2.map (fun t => (t.1, t.2.1, removeMustTerminate t.2.2)))
    compile := c }

/-- Exact HOL `compile_state_const` (`word_removeProofScript.sml:21-47`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "compile_state_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compileState_const {width : Nat} [NeZero width] {C : Type} {F : Type}
    (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    (compileState clk c s).locals = s.locals ∧
    (compileState clk c s).permute = s.permute ∧
    (compileState clk c s).ffi = s.ffi ∧
    (compileState clk c s).codeBuffer = s.codeBuffer ∧
    (compileState clk c s).dataBuffer = s.dataBuffer ∧
    (compileState clk c s).code = sptMap (fun p => (p.1, removeMustTerminate p.2)) s.code ∧
    (compileState clk c s).clock = s.clock + clk ∧
    (compileState clk c s).termdep = 0 ∧
    (compileState clk c s).compileOracle = (fun n =>
      ((s.compileOracle n).1,
        (s.compileOracle n).2.map (fun t => (t.1, t.2.1, removeMustTerminate t.2.2)))) ∧
    (compileState clk c s).compile = c ∧
    (compileState clk c s).stack = s.stack ∧
    (compileState clk c s).store = s.store ∧
    (compileState clk c s).fpRegs = s.fpRegs ∧
    (compileState clk c s).memory = s.memory ∧
    (compileState clk c s).mdomain = s.mdomain ∧
    (compileState clk c s).shMdomain = s.shMdomain ∧
    (compileState clk c s).be = s.be ∧
    (compileState clk c s).gcFun = s.gcFun ∧
    (compileState clk c s).handler = s.handler ∧
    (compileState clk c s).localsSize = s.localsSize ∧
    (compileState clk c s).stackSize = s.stackSize ∧
    (compileState clk c s).stackMax = s.stackMax ∧
    (compileState clk c s).stackLimit = s.stackLimit := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `find_code_map_I` (`word_removeProofScript.sml:49-54`):
    `find_code d l (map (I ## f) t) lsz = OPTION_MAP (I ## f ## I) (find_code d l t lsz)`.
    The source and target payloads of `f` and the stack-size payload are three
    independent HOL types; only the argument word-locations share a width. -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "find_code_map_I"
  (words_as_type_indexed_bitvec)]
theorem findCode_map_I {width : Nat} [NeZero width]
    {Source Target StackSize : Type} (d : Option Nat) (l : List (WordLocW width))
    (f : Source → Target) (t : Spt (Nat × Source)) (lsz : Spt StackSize) :
    wordSemFindCode d l (sptMap (fun p => (p.1, f p.2)) t) lsz =
      (wordSemFindCode d l t lsz).map (fun r => (r.1, f r.2.1, r.2.2)) := by
  cases d with
  | some p =>
    simp only [wordSemFindCode, sptLookup_sptMap]
    cases sptLookup p t with
    | none => rfl
    | some e => obtain ⟨a, e⟩ := e; simp only [Option.map]; split <;> rfl
  | none =>
    simp only [wordSemFindCode]
    split
    · rfl
    · split
      · simp only [sptLookup_sptMap]
        rename_i loc _
        cases sptLookup loc t with
        | none => rfl
        | some e => obtain ⟨a, e⟩ := e; simp only [Option.map]; split <;> rfl
      · rfl

/-- Exact HOL `compile_state_update` (`word_removeProofScript.sml:57-75`), with
    HOL's repeated `memory` conjunct kept. -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "compile_state_update"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compileState_update {width : Nat} [NeZero width] {C : Type} {F : Type}
    (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F)
    (f1 : List (WordSemStackFrame width)) (f2 : Nat → Nat → Nat) (f10 : HolFfiState F)
    (f9 : WordSemBuffer width width) (f8 : WordSemBuffer width 8)
    (f7 : BitVec width → WordLocW width) (f6 : Spt (WordLocW width))
    (f5 : BitVec width → WordLocW width) (f4 : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (f11 : HolFiniteMapExact Nat (BitVec 64)) (f3 : Nat) (f12 : Option Nat) (f13 : Spt Nat)
    (f14 : Option Nat) (f15 : Nat) :
    { compileState clk c s with stack := f1 } = compileState clk c { s with stack := f1 } ∧
    { compileState clk c s with permute := f2 } = compileState clk c { s with permute := f2 } ∧
    { compileState clk c s with ffi := f10 } = compileState clk c { s with ffi := f10 } ∧
    { compileState clk c s with dataBuffer := f9 } =
      compileState clk c { s with dataBuffer := f9 } ∧
    { compileState clk c s with codeBuffer := f8 } =
      compileState clk c { s with codeBuffer := f8 } ∧
    { compileState clk c s with memory := f7 } = compileState clk c { s with memory := f7 } ∧
    { compileState clk c s with locals := f6 } = compileState clk c { s with locals := f6 } ∧
    { compileState clk c s with memory := f5 } = compileState clk c { s with memory := f5 } ∧
    { compileState clk c s with store := f4 } = compileState clk c { s with store := f4 } ∧
    { compileState clk c s with fpRegs := f11 } = compileState clk c { s with fpRegs := f11 } ∧
    { compileState clk c s with handler := f3 } = compileState clk c { s with handler := f3 } ∧
    { compileState clk c s with localsSize := f12 } =
      compileState clk c { s with localsSize := f12 } ∧
    { compileState clk c s with stackSize := f13 } =
      compileState clk c { s with stackSize := f13 } ∧
    { compileState clk c s with stackMax := f14 } =
      compileState clk c { s with stackMax := f14 } ∧
    { compileState clk c s with stackLimit := f15 } =
      compileState clk c { s with stackLimit := f15 } := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `get_var_compile_state` (`word_removeProofScript.sml:77-81`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_var_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVar_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    getVar x (compileState clk c s) = getVar x s := rfl

/-- Exact HOL `get_fp_var_compile_state` (`word_removeProofScript.sml:83-87`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_fp_var_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getFpVar_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    getFpVar x (compileState clk c s) = getFpVar x s := rfl

/-- Exact HOL `get_vars_compile_state` (`word_removeProofScript.sml:89-93`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_vars_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVars_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (xs : List Nat) (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.getVars xs (compileState clk c s) =
      WordSemStateFiniteExact.getVars xs s := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [WordSemStateFiniteExact.getVars, ih]; rfl

/-- Exact HOL `set_var_compile_state` (`word_removeProofScript.sml:95-99`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "set_var_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVar_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : WordLocW width) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    setVar x y (compileState clk c s) = compileState clk c (setVar x y s) := rfl

/-- Exact HOL `unset_var_compile_state` (`word_removeProofScript.sml:101-105`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "unset_var_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem unsetVar_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    unsetVar x (compileState clk c s) = compileState clk c (unsetVar x s) := rfl

/-- Exact HOL `set_fp_var_compile_state` (`word_removeProofScript.sml:107-111`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "set_fp_var_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setFpVar_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : BitVec 64) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    setFpVar x y (compileState clk c s) = compileState clk c (setFpVar x y s) := rfl

/-- Exact HOL `set_vars_compile_state` (`word_removeProofScript.sml:113-117`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "set_vars_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVars_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (xs : List Nat) (ys : List (WordLocW width)) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    setVars xs ys (compileState clk c s) = compileState clk c (setVars xs ys s) := rfl

/-- Exact HOL `get_store_compile_state` (`word_removeProofScript.sml:119-123`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_store_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getStore_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : WordStoreHOL) (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    getStore x (compileState clk c s) = getStore x s := rfl

/-- Exact HOL `set_store_compile_state` (`word_removeProofScript.sml:125-129`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "set_store_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setStore_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : WordStoreHOL) (y : WordLocW width) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    setStore x y (compileState clk c s) = compileState clk c (setStore x y s) := rfl

/-- Exact HOL `push_env_compile_state` (`word_removeProofScript.sml:131-135`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "push_env_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnv_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (env : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    pushEnv env h (compileState clk c s) = compileState clk c (pushEnv env h s) := by
  rcases h with _ | ⟨_, _, _, _⟩ <;> rfl

/-- Exact HOL `pop_env_compile_state` (`word_removeProofScript.sml:137-141`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "pop_env_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem popEnv_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    popEnv (compileState clk c s) = (popEnv s).map (compileState clk c) := by
  unfold popEnv
  simp only [compileState]
  split <;> rfl

/-- Exact HOL `call_env_compile_state` (`word_removeProofScript.sml:143-147`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "call_env_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem callEnv_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : List (WordLocW width)) (lsz : Option Nat) (clk : Nat)
    (c : WordCompileFn width C) (z : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.callEnv x lsz (compileState clk c z) =
      compileState clk c (WordSemStateFiniteExact.callEnv x lsz z) := rfl

/-- Exact HOL `flush_state_compile_state` (`word_removeProofScript.sml:149-153`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "flush_state_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem flushState_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Bool) (clk : Nat) (c : WordCompileFn width C)
    (z : WordSemStateFiniteExact width C F) :
    flushState x (compileState clk c z) = compileState clk c (flushState x z) := by
  cases x <;> rfl

/-- Exact HOL `has_space_compile_state` (`word_removeProofScript.sml:155-159`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "has_space_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem hasSpace_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n : WordLocW width) (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    hasSpace n (compileState clk c s) = hasSpace n s := rfl

/-- Exact HOL `gc_compile_state` (`word_removeProofScript.sml:161-167`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "gc_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gc_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    gc (compileState clk c s) = (gc s).map (compileState clk c) := by
  unfold gc
  dsimp only [compileState]
  split
  · rfl
  · split <;> rfl

/-- Exact HOL `alloc_compile_state` (`word_removeProofScript.sml:169-175`):
    `alloc w names (compile_state clk c s) = (I ## compile_state clk c) (alloc w names s)`. -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "alloc_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem alloc_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (w : BitVec width) (names : WordLangCutsetsHOL) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    alloc w names (compileState clk c s) =
      Prod.map id (compileState clk c) (alloc w names s) := by
  unfold alloc
  simp only [show (compileState clk c s).locals = s.locals from rfl, setStore_compileState,
    pushEnv_compileState, gc_compileState]
  cases wordSemCutEnvs names s.locals with
  | none => simp only [flushState_compileState, Prod.map, id]
  | some envs =>
    dsimp only
    cases gc (pushEnv envs none (setStore .allocSize (.word w) s)) with
    | none => simp only [Option.map_none, flushState_compileState, Prod.map, id]
    | some s1 =>
      simp only [Option.map_some, popEnv_compileState]
      cases popEnv s1 with
      | none => simp only [Option.map_none, flushState_compileState, Prod.map, id]
      | some s2 =>
        simp only [Option.map_some, getStore_compileState]
        cases getStore .allocSize s2 with
        | none => rfl
        | some w' =>
          simp only [hasSpace_compileState]
          rcases hasSpace w' s2 with _ | _ | _ <;>
            simp only [flushState_compileState, Prod.map, id]

/-- Exact HOL `mem_load_compile_state` (`word_removeProofScript.sml:177-181`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "mem_load_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memLoad_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (w : BitVec width) (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    memLoad w (compileState clk c s) = memLoad w s := rfl

/-- Exact HOL `mem_store_compile_state` (`word_removeProofScript.sml:183-187`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "mem_store_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memStore_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : BitVec width) (y : WordLocW width) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    memStore x y (compileState clk c s) = (memStore x y s).map (compileState clk c) := by
  unfold memStore
  by_cases h : s.mdomain x = true
  · simp only [show (compileState clk c s).mdomain = s.mdomain from rfl, h, if_true,
      Option.map_some]
    rfl
  · simp only [show (compileState clk c s).mdomain = s.mdomain from rfl, h,
      Bool.false_eq_true, if_false, Option.map_none]

/-- Exact HOL `word_exp_compile_state` (`word_removeProofScript.sml:189-193`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "word_exp_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExp_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (clk : Nat) (c : WordCompileFn width C) :
    ∀ (s : WordSemStateFiniteExact width C F) (y : WordLangExpHOL (BitVec width)),
      wordExp (compileState clk c s) y = wordExp s y
  | s, .const w => by rw [wordExp, wordExp]
  | s, .var v => by rw [wordExp, wordExp]; rfl
  | s, .lookup n => by rw [wordExp, wordExp]; rfl
  | s, .load a => by
      rw [wordExp, wordExp, wordExp_compileState clk c s a]
      rfl
  | s, .op op args => by
      rw [wordExp, wordExp]
      have : (args.attach.map fun (x : { x // x ∈ args }) => wordExp (compileState clk c s) x.1) =
          (args.attach.map fun (x : { x // x ∈ args }) => wordExp s x.1) := by
        apply List.map_congr_left
        intro ⟨e, he⟩ _
        have := List.sizeOf_lt_of_mem he
        exact wordExp_compileState clk c s e
      simp only [] at this ⊢
      rw [this]
  | s, .shift sh e1 e2 => by
      rw [wordExp, wordExp, wordExp_compileState clk c s e1, wordExp_compileState clk c s e2]
termination_by _ e => sizeOf e

/-- Exact HOL `assign_compile_state` (`word_removeProofScript.sml:195-199`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "assign_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assign_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : WordLangExpHOL (BitVec width)) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    assign x y (compileState clk c s) = (assign x y s).map (compileState clk c) := by
  unfold assign
  rw [wordExp_compileState]
  split <;> rfl

set_option linter.unusedSimpArgs false in
/-- Exact HOL `inst_compile_state` (`word_removeProofScript.sml:201-207`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "inst_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem inst_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : WordLangInst (BitVec width)) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    inst i (compileState clk c s) = (inst i s).map (compileState clk c) := by
  cases i with
  | skip => rfl
  | const r w => simp only [inst, assign, wordExp_compileState]; split <;> rfl
  | arith a =>
    cases a <;> simp only [inst, assign, wordExp_compileState, getVars_compileState] <;>
      (repeat' split) <;> first | rfl | simp_all
  | mem op r a =>
    have hm : (compileState clk c s).memory = s.memory := rfl
    have hd : (compileState clk c s).mdomain = s.mdomain := rfl
    have hb : (compileState clk c s).be = s.be := rfl
    cases a
    cases op <;> simp only [inst, wordExp_compileState, getVar_compileState,
      memLoad_compileState, memStore_compileState, hm, hd, hb] <;>
      (repeat' split) <;> first | rfl | simp_all
  | fp f =>
    cases f <;> simp only [inst, getFpVar_compileState, getVar_compileState] <;>
      (repeat' split) <;> first | rfl | simp_all

/-- Exact HOL `cut_state_compile_state` (`word_removeProofScript.sml:209-215`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "cut_state_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem cutState_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (names : WordLangCutsetsHOL) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    cutState names (compileState clk c s) = (cutState names s).map (compileState clk c) := by
  unfold cutState
  rw [show (compileState clk c s).locals = s.locals from rfl]
  split <;> rfl

/-- Exact HOL local `evaluate_add_clock_compile_state`
    (`word_removeProofScript.sml:217-227`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml"
  "evaluate_add_clock_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_add_clock_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p : WordLangProgHOL (BitVec width)) (clk : Nat)
    (c : WordCompileFn width C) (s s' : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) :
    evaluate p (compileState clk c s) = (res, compileState 0 c s') ∧
      res ≠ some .timeOut →
    ∀ extra, evaluate p (compileState (clk + extra) c s) = (res, compileState extra c s') := by
  intro ⟨h, hr⟩ extra
  have := evaluate_add_clock extra p _ res _ ⟨h, hr⟩
  have h1 : ({ compileState clk c s with clock := (compileState clk c s).clock + extra } :
      WordSemStateFiniteExact width C F) = compileState (clk + extra) c s := by
    simp only [compileState, Nat.add_assoc]
  have h2 : ({ compileState 0 c s' with clock := (compileState 0 c s').clock + extra } :
      WordSemStateFiniteExact width C F) = compileState extra c s' := by
    simp only [compileState, Nat.add_zero]
  rw [h1, h2] at this
  exact this

/-- Exact HOL `compile_state_dec_clock` (`word_removeProofScript.sml:229-233`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "compile_state_dec_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compileState_decClock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    s.clock ≠ 0 → compileState clk c (decClock s) = decClock (compileState clk c s) := by
  intro h
  simp only [compileState, decClock]
  congr 1
  omega

/-- Exact HOL `jump_exc_compile_state` (`word_removeProofScript.sml:235-239`):
    `jump_exc (compile_state clk c s) = OPTION_MAP (compile_state clk c ## I) (jump_exc s)`. -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "jump_exc_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem jumpExc_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (clk : Nat) (c : WordCompileFn width C)
    (s : WordSemStateFiniteExact width C F) :
    jumpExc (compileState clk c s) = (jumpExc s).map (Prod.map (compileState clk c) id) := by
  unfold jumpExc
  have hh : (compileState clk c s).handler = s.handler := rfl
  have hs : (compileState clk c s).stack = s.stack := rfl
  by_cases h : s.handler < s.stack.length
  · simp only [hh, hs, h, if_true]
    split <;> rfl
  · simp only [hh, hs, h, if_false, Option.map_none]

/-- Exact HOL `get_var_imm_compile_state` (`word_removeProofScript.sml:241-245`). -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "get_var_imm_compile_state"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarImm_compileState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : WordRegImm (BitVec width)) (clk : Nat)
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.getVarImm x (compileState clk c s) =
      WordSemStateFiniteExact.getVarImm x s := by
  cases x <;> rfl

/-- Exact HOL `push_env_case_handler` (`word_removeProofScript.sml:247-252`), an
    equation between state transformers as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "push_env_case_handler"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem pushEnv_case_handler {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (f : WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)) :
    (pushEnv x (match handler with
        | none => none
        | some (v, prog, l1, l2) => some (v, f prog, l1, l2)) :
      WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F) =
      pushEnv x handler := by
  funext s
  rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl

/-- Exact HOL local `pair_map_I` (`word_removeProofScript.sml:254-260`), with
    HOL `##` (`PAIR_MAP`) as `Prod.map` and `I` as `id`. -/
@[hol "cakeml/compiler/backend/proofs/word_removeProofScript.sml" "pair_map_I"]
theorem pair_map_I {α β γ δ : Type} (f : β → γ) :
    (fun (p : α × β) => match p with | (k, v) => (k, f v)) = Prod.map id f ∧
    (fun (p : β × δ) => match p with | (k, v) => (f k, v)) = Prod.map f id := by
  constructor <;> funext ⟨_, _⟩ <;> rfl

end CompileState

end Flapjack.Compiler.Backend.WordRemove
