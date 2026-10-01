import Flapjack.RiscV.OracleAllocator

namespace Flapjack

example :
    wordOracleColouringOk 13 26
      (.delta [4] [2]) [] [] = true := by
  decide +kernel

example :
    wordOracleColouringOk 13 26
      (.delta [3] [2]) [] [(3, 3)] = false := by
  decide +kernel

/-- The oracle decision is unchanged by routing the clash-tree check through the
reviewed checker: it is the executed `wordClashTreeCheck` verdict. -/
example (colours stackStart : Nat) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (oracle : NatInfoMap Nat) :
    wordOracleColouringOk colours stackStart tree forced oracle =
      (let colour := wordOracleColour oracle
       (wordClashTreeCheck colour tree [] []).isSome &&
         wordOracleEdgesSafe colour forced &&
           wordOracleStackSafe colour stackStart
             (wordClashTreeNames tree).eraseDups) :=
  wordOracleColouringOk_eq_wordClashTreeCheck colours stackStart tree forced oracle

/-- Concrete routing guard: the reviewed-check decision matches the executed
checker on an accepted and a rejected delta. -/
example :
    wordOracleClashTreeCheck (wordOracleColour []) (.delta [4] [2]) =
      (wordClashTreeCheck (wordOracleColour []) (.delta [4] [2]) [] []).isSome :=
  wordOracleClashTreeCheck_eq (wordOracleColour []) (.delta [4] [2])

#guard
    (wordAllocateFunctionWithOracle [2]
      (.assign 4 (.var 2) : WordProg Nat) 13 26 []).isSome = true

example [OfNat α 0] (parameters : List Nat) (program : WordProg α)
    (colours stackStart : Nat) (oracle : NatInfoMap Nat)
    (state : WordSsaState) (renamedParameters : List Nat)
    (renamedProgram : WordProg α)
    (halloc : wordAllocateFunctionWithOracle parameters program colours stackStart oracle =
      some (state, renamedParameters, renamedProgram)) :
    wordOracleColouringOk colours stackStart
        (WordClashTree.seq
          (.set (wordSsaRenameFunction parameters program).2.fst)
          (wordClashTree (wordSsaRenameFunction parameters program).2.snd []))
        (wordProgForcedClashes (wordSsaRenameFunction parameters program).2.snd)
        oracle = true := by
  exact wordAllocateFunctionWithOracle_sound parameters program colours stackStart oracle
    state renamedParameters renamedProgram halloc

end Flapjack
