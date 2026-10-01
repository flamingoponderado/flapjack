import Flapjack.RiscV.ClashTreeCodec

/-! Kernel tests for the `WordClashTree`/`RegAlloc.ClashTree` codec and the
executed/reviewed checker agreement (`Flapjack/RiscV/ClashTreeCodec.lean`).

These are finite observations, not the general theorem (which is
`wordClashTreeCheck_agrees`); they pin the concrete delta/set/seq/branch
behaviour and the canonical-fragment roundtrip.  The checker agreement is at
the level of the returned set domains, so the guards compare member sets. -/

namespace Flapjack.Test.ClashTreeCodecParity

open Flapjack
open Flapjack.ClashTreeCodec
open Flapjack.RegAlloc

/-- Same member set for two concrete name lists. -/
def sameSet (left right : List Nat) : Bool :=
  left.all (fun name => name ∈ right) && right.all (fun name => name ∈ left)

/-- The codec maps payloads through `listToNumSet` and preserves deltas. -/
def codecGuard : Bool :=
  (match wordClashTreeToReviewed (.delta [1] [2]) with
   | ClashTree.delta w r => w == [1] && r == [2]
   | _ => false) &&
  (match reviewedToWordClashTree (.delta [1] [2]) with
   | WordClashTree.delta w r => w == [1] && r == [2]
   | _ => false)

#guard codecGuard

/-- Concrete agreement: `delta` writes/reads. -/
def deltaAgreementGuard : Bool :=
  match wordClashTreeCheck (fun x => x) (.delta [1] [2]) [] [],
    checkClashTree (fun x => x)
      (wordClashTreeToReviewed (.delta [1] [2])) .ln .ln with
  | some (names, coloured), some (namesS, colouredS) =>
      sameSet names (numSetToList namesS) && sameSet coloured (numSetToList colouredS)
  | none, none => true
  | _, _ => false

#guard deltaAgreementGuard

/-- Concrete agreement: fixed `set` payload. -/
def setAgreementGuard : Bool :=
  match wordClashTreeCheck (fun x => x) (.set [1, 2]) [] [],
    checkClashTree (fun x => x)
      (wordClashTreeToReviewed (.set [1, 2])) .ln .ln with
  | some (names, coloured), some (namesS, colouredS) =>
      sameSet names (numSetToList namesS) && sameSet coloured (numSetToList colouredS)
  | none, none => true
  | _, _ => false

#guard setAgreementGuard

/-- Concrete agreement: `seq` checks its right child first. -/
def seqAgreementGuard : Bool :=
  match wordClashTreeCheck (fun x => x)
      (.seq (.delta [1] [2]) (.set [3])) [] [],
    checkClashTree (fun x => x)
      (wordClashTreeToReviewed (.seq (.delta [1] [2]) (.set [3]))) .ln .ln with
  | some (names, coloured), some (namesS, colouredS) =>
      sameSet names (numSetToList namesS) && sameSet coloured (numSetToList colouredS)
  | none, none => true
  | _, _ => false

#guard seqAgreementGuard

/-- Concrete agreement: `branch` with a fixed live set. -/
def branchSomeAgreementGuard : Bool :=
  match wordClashTreeCheck (fun x => x)
      (.branch (some [1]) (.delta [] []) (.delta [] [])) [] [],
    checkClashTree (fun x => x)
      (wordClashTreeToReviewed (.branch (some [1]) (.delta [] []) (.delta [] []))) .ln .ln with
  | some (names, coloured), some (namesS, colouredS) =>
      sameSet names (numSetToList namesS) && sameSet coloured (numSetToList colouredS)
  | none, none => true
  | _, _ => false

#guard branchSomeAgreementGuard

/-- Concrete agreement: `branch` without a fixed live set (the filtered
right-minus-left set). -/
def branchNoneAgreementGuard : Bool :=
  match wordClashTreeCheck (fun x => x)
      (.branch none (.delta [] [1]) (.delta [] [2])) [] [],
    checkClashTree (fun x => x)
      (wordClashTreeToReviewed (.branch none (.delta [] [1]) (.delta [] [2]))) .ln .ln with
  | some (names, coloured), some (namesS, colouredS) =>
      sameSet names (numSetToList namesS) && sameSet coloured (numSetToList colouredS)
  | none, none => true
  | _, _ => false

#guard branchNoneAgreementGuard

/-- A failing case: `id` is not injective on `{1,2}` after a forced alias. -/
def failureAgreementGuard : Bool :=
  match wordClashTreeCheck (fun _ => 0) (.set [1, 2]) [] [],
    checkClashTree (fun _ => 0)
      (wordClashTreeToReviewed (.set [1, 2])) .ln .ln with
  | none, none => true
  | _, _ => false

#guard failureAgreementGuard

/-- Canonical-fragment roundtrip of the codec. -/
example : reviewedToWordClashTree (wordClashTreeToReviewed (.set [0])) =
    WordClashTree.set [0] :=
  reviewedToWordClashTree_toReviewed (.set [0])
    (by simp [CanonicalTree, CanonicalList, numSetToList, listToNumSet,
      sptFromAList, sptToAList, sptFoldi])

example : reviewedToWordClashTree
    (wordClashTreeToReviewed (.seq (.delta [1] [2]) (.set [0]))) =
    WordClashTree.seq (WordClashTree.delta [1] [2]) (WordClashTree.set [0]) :=
  reviewedToWordClashTree_toReviewed (.seq (.delta [1] [2]) (.set [0]))
    (by simp [CanonicalTree, CanonicalList, numSetToList, listToNumSet,
      sptFromAList, sptToAList, sptFoldi])

/-- The reviewed-check routing keeps the executed checker's success/failure
verdict. -/
example :
    (wordClashTreeCheckViaReviewed (fun x => x) (.delta [1] [2]) [] []).isSome =
      (wordClashTreeCheck (fun x => x) (.delta [1] [2]) [] []).isSome :=
  wordClashTreeCheckViaReviewed_isSome (fun x => x) (.delta [1] [2]) [] []

/-- A concrete routing guard over the same trees as the agreement guards: the
routing result's member sets match the executed checker's. -/
def routingGuard : Bool :=
  (match wordClashTreeCheckViaReviewed (fun x => x) (.delta [1] [2]) [] [],
     wordClashTreeCheck (fun x => x) (.delta [1] [2]) [] [] with
   | some (n, c), some (n', c') => sameSet n n' && sameSet c c'
   | none, none => true
   | _, _ => false) &&
  (match wordClashTreeCheckViaReviewed (fun _ => 0) (.set [1, 2]) [] [],
     wordClashTreeCheck (fun _ => 0) (.set [1, 2]) [] [] with
   | none, none => true
   | _, _ => false)

#guard routingGuard
example :
    (wordClashTreeCheckViaReviewed (fun _ => 0) (.set [1, 2]) [] []).isSome =
      (wordClashTreeCheck (fun _ => 0) (.set [1, 2]) [] []).isSome :=
  wordClashTreeCheckViaReviewed_isSome (fun _ => 0) (.set [1, 2]) [] []

def parityGuard : Bool :=
  codecGuard && deltaAgreementGuard && setAgreementGuard && seqAgreementGuard &&
    branchSomeAgreementGuard && branchNoneAgreementGuard && failureAgreementGuard &&
    routingGuard

/-! ## Original-HOL `check_clash_tree` oracle rows (numeric colour function)

`scripts/hol-probes/reg_alloc_check_clash_tree_probeScript.sml` EVALs the
original HOL `check_clash_tree` on the trees below with the finite-map-backed
numeric colour function `col` (`1↦1, 2↦2, 3↦3, 4↦4`, else `0`) or the
colliding `badCol` (`1↦1, 2↦1`). The examples run the same inputs through the
codec and the reviewed `checkClashTree`; the `#guard`s below pin the executed
`wordClashTreeCheck` verdicts. -/

/-- Numeric colour function matching the probe's finite-map-backed `colour`. -/
def col (name : Nat) : Nat :=
  match name with
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | _ => 0

/-- Colliding numeric colour function matching the probe's `bad_colour`. -/
def badCol (name : Nat) : Nat :=
  match name with
  | 1 => 1
  | 2 => 1
  | _ => 0

/-- `delta_live`: Delta writes/reads with nonempty `live = flive = {3}`. -/
example : checkClashTree col (wordClashTreeToReviewed (.delta [1] [2]))
    (listToNumSet [3]) (listToNumSet [3]) =
    some (listToNumSet [2, 3], listToNumSet [2, 3]) := by decide +kernel

/-- `set_fixed`: a fixed Set, ignoring `live`/`flive`. -/
example : checkClashTree col (wordClashTreeToReviewed (.set [1]))
    (listToNumSet [3]) (listToNumSet [3]) =
    some (listToNumSet [1], listToNumSet [1]) := by decide +kernel

/-- `branch_none`: the merged right-minus-left set is checked. -/
example : checkClashTree col
    (wordClashTreeToReviewed (.branch none (.delta [] [1]) (.delta [] [2])))
    (listToNumSet [3]) (listToNumSet [3]) =
    some (listToNumSet [2, 1, 3], listToNumSet [2, 1, 3]) := by decide +kernel

/-- `branch_some`: the fixed live set is checked with `checkCol`. -/
example : checkClashTree col
    (wordClashTreeToReviewed (.branch (some [1]) (.delta [] []) (.delta [] [])))
    (listToNumSet [3]) (listToNumSet [3]) =
    some (listToNumSet [1], listToNumSet [1]) := by decide +kernel

/-- `seq_right_first`: Seq checks its right child first. -/
example : checkClashTree col
    (wordClashTreeToReviewed (.seq (.delta [2] []) (.delta [] [1])))
    (listToNumSet [3]) (listToNumSet [3]) =
    some (listToNumSet [1, 3], listToNumSet [1, 3]) := by decide +kernel

/-- `delta_flive_collision`: the incoming `flive` already holds the write's
colour. -/
example : checkClashTree col (wordClashTreeToReviewed (.delta [1] []))
    (listToNumSet []) (listToNumSet [1]) = none := by decide +kernel

/-- `set_colour_collision`: `badCol` is not injective on `{1,2}`. -/
example : checkClashTree badCol (wordClashTreeToReviewed (.set [1, 2]))
    (listToNumSet [3]) (listToNumSet [3]) = none := by decide +kernel

/-- Executed `wordClashTreeCheck` verdicts for the same oracle rows. -/
def oracleRowsGuard : Bool :=
  (wordClashTreeCheck col (.delta [1] [2]) [3] [3]).isSome &&
  (wordClashTreeCheck col (.set [1]) [3] [3]).isSome &&
  (wordClashTreeCheck col (.branch none (.delta [] [1]) (.delta [] [2])) [3] [3]).isSome &&
  (wordClashTreeCheck col (.branch (some [1]) (.delta [] []) (.delta [] [])) [3] [3]).isSome &&
  (wordClashTreeCheck col (.seq (.delta [2] []) (.delta [] [1])) [3] [3]).isSome &&
  !(wordClashTreeCheck col (.delta [1] []) [] [1]).isSome &&
  !(wordClashTreeCheck badCol (.set [1, 2]) [3] [3]).isSome

#guard oracleRowsGuard

def runChecks : IO Bool := do
  if parityGuard && oracleRowsGuard then
    IO.println "PASS WordClashTree/RegAlloc.ClashTree codec agreement"
  else
    IO.println "FAIL WordClashTree/RegAlloc.ClashTree codec agreement"
  pure (parityGuard && oracleRowsGuard)

end Flapjack.Test.ClashTreeCodecParity
