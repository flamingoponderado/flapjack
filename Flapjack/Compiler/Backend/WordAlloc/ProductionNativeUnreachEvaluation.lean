import Flapjack.Compiler.Backend.WordUnreach.Production
import Flapjack.Compiler.Backend.WordUnreach.Proofs

namespace Flapjack.WordAlloc
open Compiler.Backend.WordUnreach WordSemStateFiniteExact

/-- Flapjack actual native-unreach API composition. The executed result and its
exact native decoding are derived from the input codec, then the original
non-error evaluation theorem preserves the complete result and state. No
output success or target evaluation is assumed. This wrapper has no independent
HOL declaration and does not establish the remaining allocator phases or the
production/native evaluator relation. Imported native assurance limits apply. -/
theorem nativeUnreach_evaluation {width : Nat} [NeZero width] {C F : Type}
    (source : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (state finalState : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (sourceRun : evaluate native state = (result, finalState))
    (nonerror : result ≠ some .error) :
    ∃ output : WordProg (BitVec width),
      RiscV.wordRemoveUnreachViaHOL? source = some output ∧
      wordLangProgFromHOL (removeUnreach native) = some output ∧
      evaluate (removeUnreach native) state = (result, finalState) := by
  have available := RiscV.wordRemoveUnreachViaHOL?_isSome source
    (by simp only [encoded, Option.isSome_some])
  unfold RiscV.wordRemoveUnreachViaHOL? at available
  simp only [encoded, Option.bind_some] at available
  cases decoded : wordLangProgFromHOL (removeUnreach native) with
  | none => simp [decoded] at available
  | some output =>
      refine ⟨output, ?_, rfl, ?_⟩
      · simp only [RiscV.wordRemoveUnreachViaHOL?, encoded, Option.bind_some, decoded]
      · exact evaluateRemoveUnreach native state result finalState ⟨sourceRun, nonerror⟩

end Flapjack.WordAlloc
