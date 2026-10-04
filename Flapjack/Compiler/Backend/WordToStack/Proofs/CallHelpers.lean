import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Results
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

/-!
# Word-to-Stack call helper lemmas

Small facts used by the `Call` cases of `comp_correct`
(`word_to_stackProofScript.sml`): `evaluate_SeqStackFree` (960-972),
`compile_result_NOT_2` (3423-3429) and `compile_prog_stack_size` (7546-7551).
-/

namespace Flapjack.WordToStackProofs.CallHelpers
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Canonical StackSem codec re-export for the evaluator's map translation;
no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Exact HOL `evaluate_SeqStackFree` (`word_to_stackProofScript.sml:960-972`).
HOL's free `f`, `p` and `t` are explicit. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateSeqStackFree {width : Nat} [NeZero width] {C F : Type}
    (f : Nat) (p : HolProg width) (t : StackSemStateFiniteExact width C F) :
    t.useStack = true ∧ t.stackSpace ≤ t.stack.length →
      StackSemEvaluate.evaluate (seqStackFreeNative f p, t) =
        StackSemEvaluate.evaluate (.seq (.stackFree f) p, t) := by
  rintro ⟨huse, hle⟩
  unfold seqStackFreeNative
  split
  · rename_i h0
    subst h0
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_stackFree,
      if_neg (by simp [huse]), if_neg (by omega)]
    simp only [StackSemControl.fixClock, Nat.add_zero, Nat.min_self]
  · rfl

/-- Exact HOL `evaluate_SeqStackFree` (`word_to_stackProofScript.sml:3286-3293`),
the script's second, non-local declaration of the same statement. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateSeqStackFree' {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    s.useStack = true ∧ s.stackSpace ≤ s.stack.length →
      StackSemEvaluate.evaluate (seqStackFreeNative n p, s) =
        StackSemEvaluate.evaluate (.seq (.stackFree n) p, s) :=
  evaluateSeqStackFree n p s

/-- Exact HOL `compile_result_NOT_2` (`word_to_stackProofScript.sml:3423-3429`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "compile_result_NOT_2"
  (words_as_type_indexed_bitvec)]
theorem compileResultNot2 {width : Nat} [NeZero width] (x : WordSemResult width) :
    goodDimindex width →
      CompCorrect.compileResult x ≠ StackSemResult.halt (.word (2 : BitVec width)) := by
  intro h heq
  exact (CompCorrect.haltEqCompileResult x).2 h heq.symm

/-- Exact HOL `compile_prog_stack_size` (`word_to_stackProofScript.sml:7546-7551`).
HOL's free variables are explicit; `compile_prog` is the native
`compileProgNative`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileProgStackSize {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (perf : Bool) (wordProg : WordLangProgHOL (BitVec width))
    (x k : Nat) (bs : AppList (BitVec width) × Nat) (stackProg : HolProg width) (fs : Nat)
    (bs2 : AppList (BitVec width) × Nat) :
    compileProgNative ac perf wordProg x k bs = (stackProg, fs, bs2) → x - k ≤ fs := by
  intro h
  simp only [compileProgNative] at h
  have hfs := congrArg (fun r => r.2.1) h
  simp only at hfs
  rw [← hfs]
  split <;> omega

end Flapjack.WordToStackProofs.CallHelpers
