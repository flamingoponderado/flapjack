import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.Compiler.Backend.WordUnreach.ProductionEncoderDomain
import Flapjack.Compiler.Backend.WordUnreach.ProductionMemoryDomain
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

/-!
# Executed unreachable-code removal through the reviewed `remove_unreach`

HOL `word_to_word$compile_single` (`word_to_wordScript.sml:31`) runs
`remove_unreach` after `three_to_two_reg_prog`. The executed allocator consumer
runs the tagged `WordUnreach.removeUnreach` (`Seq_assoc_right e Skip`, with
`SimpSeq` and `merge_moves`) at that point: the production program is encoded
with `wordLangProgToHOL`, the reviewed pass runs on the exact `wordLang$prog`
carrier, and the result is decoded with `wordLangProgFromHOL`. A program outside
the codec's domain is an explicit failure; no second implementation of the pass
is used. Flapjack production routing with no HOL declaration of its own.
-/

namespace Flapjack.RiscV

/-- Executed unreachable-code removal via the reviewed `removeUnreach`. -/
def wordRemoveUnreachViaHOL? {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) : Option (WordProg (BitVec width)) :=
  (wordLangProgToHOL program).bind
    (fun native => wordLangProgFromHOL (Compiler.Backend.WordUnreach.removeUnreach native))

/-- Every accepted executed result is the decoded reviewed pass output on the
encoded input (Flapjack routing fact; no evaluation is assumed). -/
theorem wordRemoveUnreachViaHOL?_native {width : Nat} [NeZero width]
    (program result : WordProg (BitVec width))
    (accepted : wordRemoveUnreachViaHOL? program = some result) :
    ∃ native, wordLangProgToHOL program = some native ∧
      wordLangProgFromHOL (Compiler.Backend.WordUnreach.removeUnreach native) = some result := by
  unfold wordRemoveUnreachViaHOL? at accepted
  cases hencode : wordLangProgToHOL program with
  | none => simp [hencode] at accepted
  | some native =>
      simp only [hencode, Option.bind_some] at accepted
      exact ⟨native, rfl, accepted⟩

/-- An accepted executed result lies in the input codec's domain: it is a
decoder image. Carrier closure only, not evaluator equivalence. -/
theorem wordRemoveUnreachViaHOL?_outputCodec {width : Nat} [NeZero width]
    (program result : WordProg (BitVec width))
    (accepted : wordRemoveUnreachViaHOL? program = some result) :
    (wordLangProgToHOL result).isSome = true := by
  obtain ⟨_, _, decoded⟩ := wordRemoveUnreachViaHOL?_native program result accepted
  simp [wordLangProgToHOL_of_fromHOL _ result decoded]

/-- The executed pass succeeds on every codec-accepted program: the reviewed
pass introduces no decoder failure. No output is assumed. -/
theorem wordRemoveUnreachViaHOL?_isSome {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordRemoveUnreachViaHOL? program).isSome = true := by
  unfold wordRemoveUnreachViaHOL?
  cases encoded : wordLangProgToHOL program with
  | none => simp [encoded] at accepted
  | some native =>
      simpa only [Option.bind_some] using
        Compiler.Backend.WordUnreach.removeUnreach_of_toHOL_decoder_isSome program native encoded

/-- The executed pass preserves executed allocator support; dropped tails can
only remove instructions. Runtime-domain fact, not evaluator equivalence. -/
theorem wordRemoveUnreachViaHOL?_memoryGuard {width : Nat} [NeZero width]
    (program result : WordProg (BitVec width))
    (accepted : wordRemoveUnreachViaHOL? program = some result)
    (supported : RiscV.allocatorMemorySupported program = true) :
    RiscV.allocatorMemorySupported result = true := by
  obtain ⟨native, encoded, decoded⟩ := wordRemoveUnreachViaHOL?_native program result accepted
  rw [Compiler.Backend.WordUnreach.memDomain_decode _ result decoded]
  apply Compiler.Backend.WordUnreach.removeUnreach_memDomain
  rw [Compiler.Backend.WordUnreach.encoderImage_memDomain program native encoded]
  exact supported

end Flapjack.RiscV
