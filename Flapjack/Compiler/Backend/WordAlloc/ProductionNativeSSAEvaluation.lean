import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSACanonicalImage
import Flapjack.Compiler.Backend.WordAlloc.Proofs.FullSSACorrect

namespace Flapjack.WordAlloc
open Compiler.Backend.WordAlloc WordSemStateFiniteExact

open Classical in
/-- The actual native SSA facade produces a tuple whose encoded body satisfies
the complete original SSA evaluation conclusion. Availability and literal
output encoding are derived from the real source encoder and SSA producer.
Only the original initial locals-domain condition is retained; no memory
guard, decoder success, output invariant or desired target evaluation is
assumed. This actual API composition has no separate HOL original; subsequent
cleanup and the production evaluator relation remain separate obligations. -/
theorem nativeSsa_evaluation {width : Nat} [NeZero width] {C F : Type}
    (count : Nat) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (state : WordSemStateFiniteExact width C F)
    (domain : sptDomain state.locals = (fun key => key ∈ evenList count)) :
    ∃ (output : WordSsaState × List Nat × WordProg (BitVec width))
        (nativeOutput : WordLangProgHOL (BitVec width)),
      wordFullSsaCcTransNativeWithState count source = some output ∧
      wordLangProgToHOL output.2.2 = some nativeOutput ∧
      ∃ permutation : Nat → Nat → Nat,
        let sourceRun := evaluate native {state with permute := permutation}
        if sourceRun.1 = some .error then True else
          let targetRun := evaluate nativeOutput state
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
  | some output =>
    have outputEncoded := nativeSsaDecodedProgram_literal count source native encoded output produced
    have actual : wordFullSsaCcTransNativeWithState count source = some output := by
      simp [wordFullSsaCcTransNativeWithState, encoded, produced]
    exact ⟨output, fullSsaCcTrans count native, actual, outputEncoded,
      fullSsaCcTransCorrect native state count domain⟩

end Flapjack.WordAlloc
