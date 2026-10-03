import Flapjack.Compiler.Backend.WordRemove
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

/-!
# Executed `remove_must_terminate` through the reviewed definition

HOL `word_to_word$full_compile_single` (`word_to_wordScript.sml:37-40`) applies
`remove_must_terminate` to every allocated function. The executed compiler runs
the tagged `WordRemove.removeMustTerminate` at the same point: the allocated
production program is encoded with `wordLangProgToHOL`, the reviewed pass runs
on the exact `wordLang$prog` carrier, and the result is decoded with
`wordLangProgFromHOL`. A program outside the codec's domain (the executable-only
five-register AddCarry, which the original compiler never produces) is an
explicit failure; no second implementation of the pass is used. Flapjack
production routing with no HOL declaration of its own.
-/

namespace Flapjack.RiscV

/-- Executed MustTerminate removal via the reviewed `removeMustTerminate`. -/
def wordRemoveMustTerminateViaHOL? {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) : Option (WordProg (BitVec width)) :=
  (wordLangProgToHOL program).bind
    (fun native => wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate native))

/-- Every accepted executed result is the decoded reviewed pass output on the
encoded input (Flapjack routing fact; no evaluation is assumed). -/
theorem wordRemoveMustTerminateViaHOL?_native {width : Nat} [NeZero width]
    (program result : WordProg (BitVec width))
    (accepted : wordRemoveMustTerminateViaHOL? program = some result) :
    ∃ native, wordLangProgToHOL program = some native ∧
      wordLangProgFromHOL (Compiler.Backend.WordRemove.removeMustTerminate native) = some result := by
  unfold wordRemoveMustTerminateViaHOL? at accepted
  cases hencode : wordLangProgToHOL program with
  | none => simp [hencode] at accepted
  | some native =>
      simp only [hencode, Option.bind_some] at accepted
      exact ⟨native, rfl, accepted⟩

end Flapjack.RiscV
