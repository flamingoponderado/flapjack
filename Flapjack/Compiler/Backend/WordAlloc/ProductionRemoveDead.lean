import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.RiscV.WordDeadCode

/-!
# Executed word dead-code removal through reviewed `remove_dead_prog`

The executed allocator boundary runs HOL `remove_dead_prog`
(`word_allocScript.sml:1004-1006`, Flapjack `WordAlloc.removeDeadProg`) on the
exact `wordLang$prog` carrier: the production program is encoded with
`wordLangProgToHOL`, `removeDeadProg` runs, and the result is decoded with
`wordLangProgFromHOL`. A program the codec rejects (the executable-only
five-register AddCarry, or a nested use of it) keeps the historical executable
pass `wordRemoveDeadProgram`; this is the router's existing compatibility branch
for the broader Word extension, not a performance exception.
-/

namespace Flapjack.RiscV

/-- Executed dead-code removal via the reviewed `removeDeadProg` (Flapjack
production routing; see the module docstring for the codec and compatibility
behaviour). -/
def wordRemoveDeadProgramViaHOL {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) : WordProg (BitVec width) :=
  match (wordLangProgToHOL program).bind
      (fun native => wordLangProgFromHOL (WordAlloc.removeDeadProg native)) with
  | some result => result
  | none => wordRemoveDeadProgram program

/-- On a codec-accepted program whose reviewed result decodes, the executed
pass is exactly the decoded `removeDeadProg` result (Flapjack routing fact). -/
theorem wordRemoveDeadProgramViaHOL_native {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (result : WordProg (BitVec width)) (hencode : wordLangProgToHOL program = some native)
    (hdecode : wordLangProgFromHOL (WordAlloc.removeDeadProg native) = some result) :
    wordRemoveDeadProgramViaHOL program = result := by
  simp [wordRemoveDeadProgramViaHOL, hencode, hdecode]

end Flapjack.RiscV
