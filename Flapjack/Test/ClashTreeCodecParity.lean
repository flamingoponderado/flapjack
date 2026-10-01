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

def parityGuard : Bool :=
  codecGuard && deltaAgreementGuard && setAgreementGuard && seqAgreementGuard &&
    branchSomeAgreementGuard && branchNoneAgreementGuard && failureAgreementGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS WordClashTree/RegAlloc.ClashTree codec agreement"
  else
    IO.println "FAIL WordClashTree/RegAlloc.ClashTree codec agreement"
  pure parityGuard

end Flapjack.Test.ClashTreeCodecParity
