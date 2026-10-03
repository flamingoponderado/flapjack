import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeSSAEvaluation
import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeDeadEvaluation
import Flapjack.Pancake.Proofs.WordConvs.SSAFlatFull

namespace Flapjack.WordAlloc
open Compiler.Backend.WordAlloc WordSemStateFiniteExact

open Classical in
/-- Flapjack actual API composition of the SSA producer and first native
cleanup, in the executed allocator order. Both actual outputs are derived.
The original source flat convention and initial locals-domain hypotheses
supply the original semantic premises; no output invariant, decoder success
or target run is assumed. This has no separately named HOL original and does
not establish the separate production/native evaluator correspondence or
later allocator phases. The imported native semantic assurance limits apply. -/
theorem nativeSsa_firstDead_evaluation {width : Nat} [NeZero width] {C F : Type}
    (count : Nat) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (state : WordSemStateFiniteExact width C F)
    (domain : sptDomain state.locals = (fun key => key ∈ evenList count))
    (flat : flatExpConventions native = true) :
    ∃ ssaOutput : WordSsaState × List Nat × WordProg (BitVec width),
      wordFullSsaCcTransNativeWithState count source = some ssaOutput ∧
      ∃ deadOutput : WordProg (BitVec width),
        wordLangProgFromHOL (removeDeadProg (fullSsaCcTrans count native)) = some deadOutput ∧
        RiscV.wordRemoveDeadProgramViaHOL ssaOutput.2.2 = deadOutput ∧
        ∃ permutation : Nat → Nat → Nat,
          let sourceRun := evaluate native {state with permute := permutation}
          if sourceRun.1 = some .error then True else
            let targetRun := evaluate (removeDeadProg (fullSsaCcTrans count native)) state
            sourceRun.1 = targetRun.1 ∧ wordStateEqRel sourceRun.2 targetRun.2 ∧
              match sourceRun.1 with
              | none => True
              | some (.break _) => True
              | some (.continue _) => True
              | some _ => sourceRun.2.locals = targetRun.2.locals := by
  have available := wordFullSsaCcTransNativeWithState_domain count source
  simp only [wordFullSsaCcTransNativeWithState, encoded, Option.bind_some,
    Option.isSome_some] at available
  cases produced : wordFullSsaCcTransNativeWithStateFromHOL count native with
  | none => simp [produced] at available
  | some ssaOutput =>
    have actual : wordFullSsaCcTransNativeWithState count source = some ssaOutput := by
      simp [wordFullSsaCcTransNativeWithState, encoded, produced]
    have ssaEncoded := nativeSsaDecodedProgram_literal count source native encoded ssaOutput produced
    rcases wordRemoveDeadProgramViaHOL_sourceNative ssaOutput.2.2
        (fullSsaCcTrans count native) ssaEncoded with ⟨deadOutput, decoded, routed⟩
    rcases fullSsaCcTransCorrect native state count domain with ⟨permutation, ssa⟩
    refine ⟨ssaOutput, actual, deadOutput, decoded, routed, permutation, ?_⟩
    dsimp only at ssa ⊢
    by_cases failed : (evaluate native {state with permute := permutation}).1 = some .error
    · simp only [failed, if_pos]
    · rw [if_neg failed] at ssa ⊢
      have targetNonerror : (evaluate (fullSsaCcTrans count native) state).1 ≠ some .error := by
        rw [← ssa.1]
        exact failed
      rcases nativeDead_evaluation ssaOutput.2.2 (fullSsaCcTrans count native) ssaEncoded state
          (evaluate (fullSsaCcTrans count native) state).2
          (evaluate (fullSsaCcTrans count native) state).1
          ⟨fullSsaCcTrans_flatExpConventions native count flat, rfl, targetNonerror⟩ with
        ⟨_, _, _, targetLocals, deadRun, deadLocals⟩
      rw [deadRun]
      refine ⟨ssa.1, ?_, ?_⟩
      · simpa only [wordStateEqRel] using ssa.2.1
      · have ssaLocals := ssa.2.2
        rw [ssa.1] at ssaLocals ⊢
        cases result : (evaluate (fullSsaCcTrans count native) state).1 with
        | none => trivial
        | some value =>
          cases value <;> simp only [result] at ssaLocals deadLocals ⊢
          all_goals first | trivial | exact ssaLocals.trans deadLocals

end Flapjack.WordAlloc
