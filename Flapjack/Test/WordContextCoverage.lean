import Flapjack.Pancake.LoopToWord.WordContextCoverage

namespace Flapjack

private def coverageProbe : LoopProg Nat :=
  .assign 5 (.var 9)

example :
    (lookupNatInfo 5 (LoopToWord.loopToWordCompContext [] coverageProbe)).isSome := by
  apply loopToWordCompContext_lookup_of_referenced
  simp [coverageProbe, LoopToWord.loopReferencedVars, loopVarsOfExp]

example :
    (lookupNatInfo 9 (LoopToWord.loopToWordCompContext [] coverageProbe)).isSome := by
  apply loopToWordCompContext_lookup_of_referenced
  simp [coverageProbe, LoopToWord.loopReferencedVars, loopVarsOfExp]

example :
    LoopToWord.findVarHOL
        (wordContextToHOLContext
          { vars := LoopToWord.loopToWordCompContext [] coverageProbe }) 5 =
      wordFindVar { vars := LoopToWord.loopToWordCompContext [] coverageProbe } 5 := by
  apply findVarHOL_wordFindVar_of_loopToWordCompContext_referenced
  simp [coverageProbe, LoopToWord.loopReferencedVars, loopVarsOfExp]

example :
    LoopToWord.findVarHOL
        (wordContextToHOLContext
          { vars := LoopToWord.loopToWordCompContext [] coverageProbe }) 9 =
      wordFindVar { vars := LoopToWord.loopToWordCompContext [] coverageProbe } 9 := by
  apply findVarHOL_wordFindVar_of_loopToWordCompContext_referenced
  simp [coverageProbe, LoopToWord.loopReferencedVars, loopVarsOfExp]

example :
    lookupNatInfo 3
      (LoopToWord.loopToWordCompContext [] (.skip : LoopProg Nat)) = none := by
  rfl

example :
    LoopToWord.findVarHOL
        (wordContextToHOLContext
          { vars := LoopToWord.loopToWordCompContext [] (.skip : LoopProg Nat) }) 3 = 0 ∧
      wordFindVar { vars := LoopToWord.loopToWordCompContext [] (.skip : LoopProg Nat) } 3 = 0 := by
  apply findVarHOL_wordFindVar_of_missing
  rfl

#guard (lookupNatInfo 5
  (LoopToWord.loopToWordCompContext [] coverageProbe)).isSome
#guard (lookupNatInfo 9
  (LoopToWord.loopToWordCompContext [] coverageProbe)).isSome
#guard (lookupNatInfo 3
  (LoopToWord.loopToWordCompContext [] (.skip : LoopProg Nat))) == none

end Flapjack
