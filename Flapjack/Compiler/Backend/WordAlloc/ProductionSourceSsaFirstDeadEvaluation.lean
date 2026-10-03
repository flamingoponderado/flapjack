import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeSsaFirstDeadEvaluation
import Flapjack.Compiler.Backend.WordToStack.ProductionSourceFlat

namespace Flapjack.WordAlloc
open Compiler.Backend.WordAlloc WordSemStateFiniteExact

open Classical in
/-- Actual source caller composition: native input availability and flatness
are derived from every Loop function body, then the original SSA and first
dead-code evaluation conclusion applies. The original initial locals-domain
hypothesis is retained. No source-flat, codec-success or target-run premise is
assumed. This Flapjack API composition has no independent HOL declaration;
later allocator phases and production/native evaluator correspondence remain
separate obligations. Imported native semantic assurance limits apply. -/
theorem executedSourceSsa_firstDead_evaluation
    {width : Nat} [NeZero width] {C F : Type}
    (name : Nat) (parameters : List Nat) (body : LoopProg (BitVec width))
    (state : WordSemStateFiniteExact width C F)
    (domain : sptDomain state.locals = (fun key => key ∈ evenList parameters.length)) :
    ∃ native : WordLangProgHOL (BitVec width),
      wordLangProgToHOL (wordBeforeSsaAllocatorBody
        (LoopToWord.loopToWordCompFunc name parameters body)) = some native ∧
      ∃ ssaOutput : WordSsaState × List Nat × WordProg (BitVec width),
        wordFullSsaCcTransNativeWithState parameters.length
          (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) =
            some ssaOutput ∧
        ∃ deadOutput : WordProg (BitVec width),
          wordLangProgFromHOL (removeDeadProg (fullSsaCcTrans parameters.length native)) =
            some deadOutput ∧
          RiscV.wordRemoveDeadProgramViaHOL ssaOutput.2.2 = deadOutput ∧
          ∃ permutation : Nat → Nat → Nat,
            let sourceRun := evaluate native {state with permute := permutation}
            if sourceRun.1 = some .error then True else
              let targetRun := evaluate
                (removeDeadProg (fullSsaCcTrans parameters.length native)) state
              sourceRun.1 = targetRun.1 ∧ wordStateEqRel sourceRun.2 targetRun.2 ∧
                match sourceRun.1 with
                | none => True
                | some (.break _) => True
                | some (.continue _) => True
                | some _ => sourceRun.2.locals = targetRun.2.locals := by
  obtain ⟨native, encoded, flat⟩ := executedSourceAllocatorInput_nativeFlat name parameters body
  exact ⟨native, encoded, nativeSsa_firstDead_evaluation parameters.length _ native
    encoded state domain flat⟩

end Flapjack.WordAlloc
