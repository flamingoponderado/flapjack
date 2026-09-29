import Flapjack.Pancake.LoopToWord.Proofs.RelationsExact

/-!
# Original HOL parity for `loop_to_wordProof$globals_rel`

The four concrete finite-map observations replay direct original-HOL EVAL
rows from `scripts/hol-probes/loop_to_word_globals_rel_probe.out`. -/

namespace Flapjack.Test.LoopToWordGlobalsRelParity

open Flapjack

private def sourceMatch : HolFiniteMapExact (BitVec 5) (WordLocW 64) :=
  HolFiniteMapExact.empty.updateEq (1, .word (9 : BitVec 64))

private def targetMatch : HolFiniteMapExact WordStoreHOL (WordLocW 64) :=
  HolFiniteMapExact.empty.updateEq (.temp (1 : BitVec 5), .word (9 : BitVec 64))

private def targetDifferentValue : HolFiniteMapExact WordStoreHOL (WordLocW 64) :=
  HolFiniteMapExact.empty.updateEq (.temp (1 : BitVec 5), .word (10 : BitVec 64))

private def targetDifferentKey : HolFiniteMapExact WordStoreHOL (WordLocW 64) :=
  HolFiniteMapExact.empty.updateEq (.temp (2 : BitVec 5), .word (9 : BitVec 64))

private def sourceEmpty : HolFiniteMapExact (BitVec 5) (WordLocW 64) :=
  HolFiniteMapExact.empty

example : loopToWordGlobalsRelHOLExact sourceMatch targetMatch := by
  simp [loopToWordGlobalsRelHOLExact, sourceMatch, targetMatch,
    HolFiniteMapExact.updateEq, HolFiniteMapExact.empty, FUPDATE_HOL]

example : ∀ n v, sourceMatch.lookup n = some v →
    targetMatch.lookup (.temp n) = some v := by
  apply loopToWordGlobalsRelIntroHOLExact sourceMatch targetMatch
  exact fun n v hLookup => by
    simpa [sourceMatch, targetMatch, HolFiniteMapExact.updateEq,
      HolFiniteMapExact.empty, FUPDATE_HOL] using hLookup

example : ¬ loopToWordGlobalsRelHOLExact sourceMatch targetDifferentValue := by
  simp [loopToWordGlobalsRelHOLExact, sourceMatch, targetDifferentValue,
    HolFiniteMapExact.updateEq, HolFiniteMapExact.empty, FUPDATE_HOL]

example : ¬ loopToWordGlobalsRelHOLExact sourceMatch targetDifferentKey := by
  simp [loopToWordGlobalsRelHOLExact, sourceMatch, targetDifferentKey,
    HolFiniteMapExact.updateEq, HolFiniteMapExact.empty, FUPDATE_HOL]

/-- The source implication is vacuous for an empty source map, irrespective of
    target-only `Temp` entries, matching the HOL direction of implication. -/
example : loopToWordGlobalsRelHOLExact sourceEmpty targetDifferentKey := by
  simp [loopToWordGlobalsRelHOLExact, sourceEmpty, targetDifferentKey,
    HolFiniteMapExact.updateEq, HolFiniteMapExact.empty, FUPDATE_HOL]

def globalsRelProbeChecks : List Bool :=
  [ sourceMatch.lookup (1 : BitVec 5) == some (.word (9 : BitVec 64)) &&
      targetMatch.lookup (.temp (1 : BitVec 5)) == some (.word (9 : BitVec 64)),
    sourceMatch.lookup (1 : BitVec 5) == some (.word (9 : BitVec 64)) &&
      !(targetDifferentValue.lookup (.temp (1 : BitVec 5)) ==
        some (.word (9 : BitVec 64))),
    sourceMatch.lookup (1 : BitVec 5) == some (.word (9 : BitVec 64)) &&
      targetDifferentKey.lookup (.temp (1 : BitVec 5)) == none,
    sourceEmpty.lookup (1 : BitVec 5) == none &&
      targetDifferentKey.lookup (.temp (2 : BitVec 5)) == some (.word (9 : BitVec 64)) ]

#guard globalsRelProbeChecks.all id

def runChecks : IO Bool := do
  let passed := globalsRelProbeChecks.all id
  if passed then
    IO.println "PASS Loop-to-Word globals_rel exact HOL EVAL rows"
  else
    IO.println "FAIL Loop-to-Word globals_rel exact HOL EVAL rows"
  pure passed

end Flapjack.Test.LoopToWordGlobalsRelParity
