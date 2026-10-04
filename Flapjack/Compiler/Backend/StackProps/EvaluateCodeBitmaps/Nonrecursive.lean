import Flapjack.Compiler.Backend.StackProps.SharedMemoryClock
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Misc.ShiftSeq

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Nonrecursive
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Canonical imported state codec witness; representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Full native skip induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsSkip {width : Nat} [NeZero width] {C F : Type} (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.skip : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_skip] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native halt induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsHalt {width : Nat} [NeZero width] {C F : Type} (v : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.halt v : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_halt] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native ret induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsRet {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.ret n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_ret] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native raise induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsRaise {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.raise n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_raise] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native break induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsBreak {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.break n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_break] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native continue induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsContinue {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.continue n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_continue] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native get induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsGet {width : Nat} [NeZero width] {C F : Type} (v : Nat) (name : StoreName) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.get v name : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_get] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native set induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsSet {width : Nat} [NeZero width] {C F : Type} (name : StoreName) (v : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.set name v : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_set] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native opCurrHeap induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsOpCurrHeap {width : Nat} [NeZero width] {C F : Type} (binop : HolBinop) (v src : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.opCurrHeap binop v src : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_opCurrHeap] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native tick induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsTick {width : Nat} [NeZero width] {C F : Type} (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.tick : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_tick] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native locValue induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsLocValue {width : Nat} [NeZero width] {C F : Type} (r l1 l2 : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.locValue r l1 l2 : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_locValue] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native stackAlloc induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsStackAlloc {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackAlloc n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_stackAlloc] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native stackFree induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsStackFree {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackFree n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_stackFree] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native stackLoad induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsStackLoad {width : Nat} [NeZero width] {C F : Type} (r n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackLoad r n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_stackLoad] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native stackLoadAny induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsStackLoadAny {width : Nat} [NeZero width] {C F : Type} (r rn : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackLoadAny r rn : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_stackLoadAny] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native stackStore induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsStackStore {width : Nat} [NeZero width] {C F : Type} (r n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackStore r n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_stackStore] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native stackStoreAny induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsStackStoreAny {width : Nat} [NeZero width] {C F : Type} (r rn : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackStoreAny r rn : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_stackStoreAny] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native stackGetSize induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsStackGetSize {width : Nat} [NeZero width] {C F : Type} (r : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackGetSize r : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_stackGetSize] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native stackSetSize induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsStackSetSize {width : Nat} [NeZero width] {C F : Type} (r : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackSetSize r : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_stackSetSize] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native bitmapLoad induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsBitmapLoad {width : Nat} [NeZero width] {C F : Type} (r v : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.bitmapLoad r v : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_bitmapLoad] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native codeBufferWrite induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsCodeBufferWrite {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.codeBufferWrite r1 r2 : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_codeBufferWrite] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full native dataBufferWrite induction case: the sole premise is actual source
execution; all three original existential conclusions are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsDataBufferWrite {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.dataBufferWrite r1 r2 : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_dataBufferWrite] at execution
  repeat' (first |
    (simp only [Prod.mk.injEq] at execution; obtain ⟨-, equality⟩ := execution; subst post) |
    split at execution | dsimp only at execution)
  all_goals exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

/-- Full shared-memory induction case, including helper failures, timeouts,
loads, stores and final FFI results. Preservation is derived from the actual
shared-memory helper execution, never supplied as a premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateCodeBitmapsShMemOp {width : Nat} [NeZero width] {C F : Type}
    (op : HolMemop) (r a : Nat) (w : BitVec width)
    (s post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.shMemOp op r (.addr a w) : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten := by
  classical
  rw [StackSemEvaluate.evaluate_shMemOp] at execution
  split at execution
  · split at execution
    · obtain ⟨-, equality⟩ := Prod.mk.inj execution
      subst post
      exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩
    · have preserved := StackPropsSharedMemoryClock.shMemOpConst _ _ _ _ _ _ execution
      obtain ⟨-, -, -, -, code, -, -, -, -, bitmaps, -, oracle⟩ := preserved
      exact ⟨0, by change post.compileOracle = s.compileOracle; exact oracle,
        by simpa [StackSemStateOps.decClock] using code,
        by simpa [StackSemStateOps.decClock] using bitmaps⟩
  · obtain ⟨-, equality⟩ := Prod.mk.inj execution
    subst post
    exact ⟨0, rfl, rfl, (List.append_nil s.bitmaps).symm⟩

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Nonrecursive
