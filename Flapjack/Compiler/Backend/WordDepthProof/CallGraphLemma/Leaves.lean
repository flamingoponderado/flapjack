import Flapjack.Compiler.Backend.WordDepthProof.CallGraphLemma.Motive

/-!
# `max_depth_call_graph_lemma`: leaf cases

The `evaluate_ind` cases of `word_depthProofScript.sml:147-788`
`max_depth_call_graph_lemma` whose run leaves `stack_max`, `stack_size` and
(on normal completion) `locals_size` unchanged, and the `Install` case, whose
call graph is `Unknown`. Each carries the original theorem's tag and is the
genuine case of `depthPost` for its constructor.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps
open WordSemStateFiniteExact

namespace CallGraphLemmaLeavesWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CallGraphLemmaLeavesWitnesses

open CallGraphLemmaLeavesWitnesses

/-- Leaf-case closing tactic: unfold one evaluator step and discharge each
branch (Flapjack infrastructure). -/
macro "depth_leaf" : tactic => `(tactic| (
  apply depthPost_of_const
  intro herr
  rw [evaluate] at herr ⊢
  repeat' split
  all_goals (first
    | (simp at herr; done)
    | (simp_all [flushState, setVar, setVars, unsetVar, setStore, decClock, setFpVar]; done)
    | skip)))

/-- `max_depth_call_graph_lemma`, `Skip` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Skip {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) : depthPost .skip s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `StoreConsts` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_StoreConsts {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 a o : Nat) (ws : List (Bool × BitVec width)) (s : WordSemStateFiniteExact width C F) :
    depthPost (.storeConsts t1 t2 a o ws) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `Move` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Move {width : Nat} [NeZero width] {C F : Type}
    (pri : Nat) (moves : List (Nat × Nat)) (s : WordSemStateFiniteExact width C F) :
    depthPost (.move pri moves) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `Inst` case (`inst_const_full`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Inst {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    depthPost (.inst i) s := by
  apply depthPost_of_const
  intro herr
  rw [evaluate] at herr ⊢
  cases hi : inst i s with
  | none => simp [hi] at herr
  | some next =>
      have := instConstFull i s next hi
      exact ⟨this.2.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2.2, fun _ => this.2.2.2.2.2.2.2.2.2.1⟩

/-- `max_depth_call_graph_lemma`, `Assign` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Assign {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (e : WordLangExpHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    depthPost (.assign v e) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `Get` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Get {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (name : WordStoreHOL) (s : WordSemStateFiniteExact width C F) :
    depthPost (.get v name) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `Set` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Set {width : Nat} [NeZero width] {C F : Type}
    (v : WordStoreHOL) (e : WordLangExpHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    depthPost (.set v e) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `OpCurrHeap` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_OpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (b : BinOp) (dst src : Nat) (s : WordSemStateFiniteExact width C F) :
    depthPost (.opCurrHeap b dst src) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `Tick` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Tick {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) : depthPost .tick s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `Break` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Break {width : Nat} [NeZero width] {C F : Type}
    (k : Nat) (s : WordSemStateFiniteExact width C F) : depthPost (.break k) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `Continue` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Continue {width : Nat} [NeZero width] {C F : Type}
    (k : Nat) (s : WordSemStateFiniteExact width C F) : depthPost (.continue k) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `Return` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Return {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (ms : List Nat) (s : WordSemStateFiniteExact width C F) :
    depthPost (.return n ms) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `LocValue` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_LocValue {width : Nat} [NeZero width] {C F : Type}
    (r l1 : Nat) (s : WordSemStateFiniteExact width C F) : depthPost (.locValue r l1) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `CodeBufferWrite` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_CodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (s : WordSemStateFiniteExact width C F) :
    depthPost (.codeBufferWrite r1 r2) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `DataBufferWrite` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_DataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (s : WordSemStateFiniteExact width C F) :
    depthPost (.dataBufferWrite r1 r2) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `Store` case (`mem_store_const`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Store {width : Nat} [NeZero width] {C F : Type}
    (e : WordLangExpHOL (BitVec width)) (v : Nat) (s : WordSemStateFiniteExact width C F) :
    depthPost (.store e v) s := by
  apply depthPost_of_const
  intro herr
  rw [evaluate] at herr ⊢
  repeat' split
  all_goals first
    | (simp at herr; done)
    | (simp_all; done)
    | (rename_i hm; have := memStoreConst _ _ _ _ hm; simp_all)

/-- `max_depth_call_graph_lemma`, `Raise` case (`jump_exc_const`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Raise {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : WordSemStateFiniteExact width C F) : depthPost (.raise n) s := by
  apply depthPost_of_const
  intro herr
  rw [evaluate] at herr ⊢
  repeat' split
  all_goals first
    | (simp at herr; done)
    | (simp_all; done)
    | (rename_i hj; have := jumpExcConst _ _ _ hj; simp_all)

/-- `max_depth_call_graph_lemma`, `FFI` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_FFI {width : Nat} [NeZero width] {C F : Type}
    (fi : Flapjack.Basis.Pure.MlString.MlString) (p1 l1 p2 l2 : Nat) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) : depthPost (.ffi fi p1 l1 p2 l2 names) s := by
  depth_leaf

/-- `max_depth_call_graph_lemma`, `ShareInst` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_ShareInst {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (v : Nat) (e : WordLangExpHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) : depthPost (.shareInst op v e) s := by
  apply depthPost_of_const
  intro herr
  rw [evaluate] at herr ⊢
  repeat' split
  all_goals first
    | (simp at herr; done)
    | (cases op <;>
        simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
          shMemStore, shMemStoreByte, shMemStore16, shMemStore32] at herr ⊢ <;>
        (repeat' split) <;> simp_all [flushState, setVar])

/-- `max_depth_call_graph_lemma`, `Install` case: its call graph is `Unknown`,
so the bound is `NONE` and the stack-size conjunct is vacuous. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem maxDepthCallGraphLemma_Install {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F) :
    depthPost (.install ptr len dptr dlen names) s := by
  intro funs n ns funs2 _
  simp only [callGraph, maxDepth]
  refine ⟨?_, fun h => absurd rfl h.2⟩
  rw [optionMap2_none_right, optionMap2_none_right, optionMap2_none_right]
  trivial

end Flapjack.Compiler.Backend.WordDepthProof
