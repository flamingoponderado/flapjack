import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopHelpers
import Flapjack.Pancake.WordConvs.PredicateEquations

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-specific collection of four projections of the accepted source
convention theorem; there is no separate HOL declaration for this collection.
Inputs to its other twenty-two clauses are specialized only because they do
not occur in these four projections. The actual source subprograms, cutsets,
comparison, register and operand remain arbitrary. -/
private theorem recursiveNoShareClauses {width : Nat} [NeZero width]
    (p p1 p2 body : WordLangProgHOL (BitVec width))
    (liveIn liveOut : Spt Unit) (cmp : Cmp) (reg : Nat) (ri : WordRegImm (BitVec width)) :
    (noShareInstSubprogsHOL (.mustTerminate p) = noShareInstSubprogsHOL p) ∧
    (noShareInstSubprogsHOL (.seq p1 p2) = (noShareInstSubprogsHOL p1 && noShareInstSubprogsHOL p2)) ∧
    (noShareInstSubprogsHOL (.loop liveIn body liveOut) = noShareInstSubprogsHOL body) ∧
    (noShareInstSubprogsHOL (.ite cmp reg ri p1 p2) = (noShareInstSubprogsHOL p1 && noShareInstSubprogsHOL p2)) := by
  have clauses := noShareInstDef
    (p := p)
    (p1 := p1)
    (p2 := p2)
    (c := body)
    (names := liveIn)
    (exitNames := liveOut)
    (v0 := cmp)
    (v1 := reg)
    (v2 := ri)
    (r := none)
    (dest := none)
    (args := [])
    (h := none)
    (v3 := 0)
    (v4 := (.ln, .ln))
    (v5 := 0)
    (l := 0)
    (v6 := .load)
    (v7 := 0)
    (v8 := (.var 0))
    (v9 := 0)
    (v10 := 0)
    (v11 := 0)
    (v12 := 0)
    (v13 := (.ln, .ln))
    (v18 := 0)
    (v19 := [])
    (v20 := .skip)
    (v21 := 0)
    (v22 := (.var 0))
    (v23 := 0)
    (v24 := .currHeap)
    (v25 := .currHeap)
    (v26 := (.var 0))
    (v27 := (.var 0))
    (v28 := 0)
    (v46 := 0)
    (v47 := 0)
    (v48 := 0)
    (v49 := 0)
    (v50 := [])
    (v51 := 0)
    (v52 := 0)
    (v53 := [])
    (v54 := 0)
    (v55 := 0)
    (v56 := .add)
    (v57 := 0)
    (v58 := 0)
    (v66 := 0)
    (v67 := 0)
    (v68 := 0)
    (v69 := 0)
    (v70 := (.implode []))
    (v71 := 0)
    (v72 := 0)
    (v73 := 0)
    (v74 := 0)
    (v75 := (.ln, .ln))
  exact ⟨clauses.1, clauses.2.1, clauses.2.2.1, clauses.2.2.2.1⟩

/-- Structural-motive MustTerminate piece. Its child hypothesis quantifies over
all bitmap/frame inputs, unlike the argument-specific IH from HOL's `comp_ind`.
The source hypotheses and conclusion are otherwise unchanged. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemopMustTerminate {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (body : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.mustTerminate body) = true)
    (compiled : compNative conf perf (.mustTerminate body) bs frame = (output, residual))
    (ih : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL body = true →
      compNative conf perf body subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true := by
  have source := (recursiveNoShareClauses body body body body .ln .ln .equal 0 (.reg 0)).1
  have result := compiled
  simp only [compNative] at result
  exact ih bs frame output residual (source ▸ guard) result

/-- Structural-motive Loop piece. Its child hypothesis quantifies over all
bitmap/frame inputs, unlike HOL's argument-specific `comp_ind` hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemopLoop {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (liveIn liveOut : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.loop liveIn body liveOut) = true)
    (compiled : compNative conf perf (.loop liveIn body liveOut) bs frame = (output, residual))
    (ih : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL body = true →
      compNative conf perf body subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true := by
  have source := (recursiveNoShareClauses body body body body liveIn liveOut .equal 0 (.reg 0)).2.2.1
  have child := ih bs frame (compNative conf perf body bs frame).1
    (compNative conf perf body bs frame).2 (source ▸ guard) rfl
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  exact child

/-- Structural-motive Seq piece. Child hypotheses quantify over all bitmap/frame
inputs; HOL's `comp_ind` fixes the second child's bitmap to the first output. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemopSeq {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (first second : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.seq first second) = true)
    (compiled : compNative conf perf (.seq first second) bs frame = (output, residual))
    (ihFirst : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL first = true →
      compNative conf perf first subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true)
    (ihSecond : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL second = true →
      compNative conf perf second subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true := by
  have source := (recursiveNoShareClauses first first second first .ln .ln .equal 0 (.reg 0)).2.1
  have both := Bool.and_eq_true_iff.mp (source ▸ guard)
  have safeFirst := ihFirst bs frame (compNative conf perf first bs frame).1
    (compNative conf perf first bs frame).2 both.1 rfl
  have safeSecond := ihSecond (compNative conf perf first bs frame).2 frame
    (compNative conf perf second (compNative conf perf first bs frame).2 frame).1
    (compNative conf perf second (compNative conf perf first bs frame).2 frame).2
    both.2 rfl
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  simp only [noShmemop, safeFirst, safeSecond, Bool.true_and]

/-- Structural-motive If piece. Both child hypotheses quantify over all
bitmap/frame inputs, rather than HOL's argument-specific `comp_ind` hypotheses.
Immediate acceptance is split in the proof, not assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemopIf {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (cmp : Cmp) (reg : Nat) (ri : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.ite cmp reg ri first second) = true)
    (compiled : compNative conf perf (.ite cmp reg ri first second) bs frame = (output, residual))
    (ihFirst : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL first = true →
      compNative conf perf first subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true)
    (ihSecond : ∀ (subBs : AppList (BitVec width) × Nat) (subFrame : Nat × Nat × Nat)
      (subOutput : HolProg width) (subResidual : AppList (BitVec width) × Nat),
      noShareInstSubprogsHOL second = true →
      compNative conf perf second subBs subFrame = (subOutput, subResidual) →
      noShmemop subOutput = true) :
    noShmemop output = true := by
  have source := (recursiveNoShareClauses first first second first .ln .ln cmp reg ri).2.2.2
  have both := Bool.and_eq_true_iff.mp (source ▸ guard)
  have safeFirst := ihFirst bs frame (compNative conf perf first bs frame).1
    (compNative conf perf first bs frame).2 both.1 rfl
  have safeSecond := ihSecond (compNative conf perf first bs frame).2 frame
    (compNative conf perf second (compNative conf perf first bs frame).2 frame).1
    (compNative conf perf second (compNative conf perf first bs frame).2 frame).2
    both.2 rfl
  have result := congrArg Prod.fst compiled
  cases ri with
  | reg n =>
    simp only [compNative] at result
    rw [← result, wStackLoadNoShmemop]
    simp only [noShmemop, safeFirst, safeSecond, Bool.true_and]
  | imm value =>
    simp only [compNative] at result
    by_cases immediate : conf.validImm (.inr cmp) value = true
    · simp only [immediate, if_true] at result
      rw [← result, wStackLoadNoShmemop]
      simp only [noShmemop, safeFirst, safeSecond, Bool.true_and]
    · simp only [immediate, Bool.false_eq_true, if_false] at result
      rw [← result]
      simp only [noShmemop, wStackLoadNoShmemop, safeFirst, safeSecond, Bool.true_and]

end Flapjack.Compiler.Backend.WordToStack.Native
