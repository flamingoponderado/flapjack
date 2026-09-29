import Flapjack.Pancake.LoopToWord.WordContextCodec

/-! Focused tests for the executed/exact Loop-to-Word variable context bridge. -/

namespace Flapjack.Test.WordContextCodecParity

open Flapjack

def duplicateContext : WordContext :=
  { vars := [(3, 8), (3, 9)] }

def hitContext : WordContext :=
  { vars := [(5, 12), (6, 13)] }

def emptyContext : WordContext :=
  { vars := [] }

example : LoopToWord.findVarHOL
    (wordContextToHOLContext duplicateContext) 3 = 8 := by
  have h : lookupNatInfo 3 duplicateContext.vars = some 8 := by rfl
  exact (findVarHOL_wordFindVar_of_lookup duplicateContext 3 8 h).trans
    (by rfl)

#guard LoopToWord.findVarHOL (wordContextToHOLContext duplicateContext) 3 == 8
#guard wordFindVar duplicateContext 3 == 8
#guard LoopToWord.findVarHOL (wordContextToHOLContext hitContext) 5 == 12
#guard wordFindVar hitContext 5 == 12
/-! The `loop_to_word_defs_probe.out` direct HOL EVAL row
`lt_find_var_miss=0` checks a nonzero name absent from a nonempty context.
This production fixture checks the same default with an empty context. -/
#guard LoopToWord.findVarHOL (wordContextToHOLContext emptyContext) 4 == 0
#guard wordFindVar emptyContext 4 == 0

example : LoopToWord.findVarHOL (wordContextToHOLContext emptyContext) 4 =
    wordFindVar emptyContext 4 := by
  exact findVarHOL_wordFindVar emptyContext 4

def codecChecks : List Bool :=
  [LoopToWord.findVarHOL (wordContextToHOLContext duplicateContext) 3 == 8,
   wordFindVar duplicateContext 3 == 8,
   LoopToWord.findVarHOL (wordContextToHOLContext hitContext) 5 == 12,
   wordFindVar hitContext 5 == 12,
   LoopToWord.findVarHOL (wordContextToHOLContext emptyContext) 4 == 0,
   wordFindVar emptyContext 4 == 0]

def runChecks : IO Bool := do
  let passed := codecChecks.all id
  if passed then
    IO.println "PASS WordContext/Spt lookup bridge (hit, duplicate, and default cases)"
  else
    IO.println "FAIL WordContext/Spt lookup bridge"
  pure passed

end Flapjack.Test.WordContextCodecParity
