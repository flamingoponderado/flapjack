import Flapjack.Pancake.Proofs.LoopToWord.WordToBytes

/-!
# Kernel replay for `loop_to_wordProof$TAKE_1_word_to_bytes`

Replays `takeOneWordToBytesHOL`
(`Flapjack.Pancake.Proofs.LoopToWord.WordToBytes`) at the 32- and 64-bit
dimensions admitted by `good_dimindex`. The concrete rows match
`loop_to_word_take_word_to_bytes_probe.out`, which prints both the proved HOL
statement and the HOL EVAL results for `TAKE 1 (word_to_bytes w F)` and
`[get_byte 0w w F]`.
-/

namespace Flapjack.Test.LoopToWordTakeWordToBytesParity

open Flapjack

/-- The exact theorem at width 32 for a low byte of `0xAB`. -/
example : (panWordToBytesHOL (0xAB : RiscV.Word 32) false).take 1
    = [getByteHOL8 0 (0xAB : RiscV.Word 32) false] :=
  takeOneWordToBytesHOL (0xAB : RiscV.Word 32) (by left; rfl)

/-- The exact theorem at width 64 for a low byte of `0xAB`. -/
example : (panWordToBytesHOL (0xAB : RiscV.Word 64) false).take 1
    = [getByteHOL8 0 (0xAB : RiscV.Word 64) false] :=
  takeOneWordToBytesHOL (0xAB : RiscV.Word 64) (by right; rfl)

/-- The `good_dimindex` side condition excludes dimensions below 8 bits, so the
    source theorem does not apply at, for example, width 24. -/
example : ¬ goodDimindex 24 := by unfold goodDimindex; omega

def takeWordToBytesChecks : List Bool :=
  [ (panWordToBytesHOL (0 : RiscV.Word 32) false).take 1 == [0],
    (panWordToBytesHOL (1 : RiscV.Word 32) false).take 1 == [1],
    (panWordToBytesHOL (0xAB : RiscV.Word 32) false).take 1 == [0xAB],
    (panWordToBytesHOL (0 : RiscV.Word 64) false).take 1 == [0],
    (panWordToBytesHOL (1 : RiscV.Word 64) false).take 1 == [1],
    (panWordToBytesHOL (0xAB : RiscV.Word 64) false).take 1 == [0xAB],
    (panWordToBytesHOL (0xAB : RiscV.Word 32) false).take 1
      == [getByteHOL8 0 (0xAB : RiscV.Word 32) false],
    (panWordToBytesHOL (0xAB : RiscV.Word 64) false).take 1
      == [getByteHOL8 0 (0xAB : RiscV.Word 64) false] ]

#guard takeWordToBytesChecks.all id

def runChecks : IO Bool := do
  let passed := takeWordToBytesChecks.all id
  if passed then
    IO.println "PASS Loop-to-Word TAKE_1_word_to_bytes exact parity rows"
  else
    IO.println "FAIL Loop-to-Word TAKE_1_word_to_bytes exact parity rows"
  pure passed

end Flapjack.Test.LoopToWordTakeWordToBytesParity
