import Flapjack.RiscV.CorrectnessColour

/-! The matching HOL observations on `check_colouring_ok_alt`'s assignment
    write/live-after set are in
    `scripts/hol-probes/word_alloc_live_colour_noalias_probe.out`.  This is a
    local clash-checker prerequisite for HOL `colouring_ok`; it is not a port
    of the full Word evaluator theorem. -/

namespace Flapjack.Test.WordColourLivenessParity

open Flapjack Flapjack.RiscV

def destination : Nat := 1
def liveAfter : List Nat := [2, 3]
def goodColouring : NatInfoMap Nat := [(1, 8), (2, 9), (3, 10)]
def badColouring : NatInfoMap Nat := [(1, 8), (2, 8), (3, 10)]

def goodColour (name : Nat) : Nat :=
  if name = 1 then 8 else if name = 2 then 9 else if name = 3 then 10 else 0

def allocatorEdges : List (Nat × Nat) := wordClashPairs [destination] liveAfter
def allocatorColouring : NatInfoMap Nat := [(3, 5), (2, 4), (1, 3)]

def allocatorColour (name : Nat) : Nat :=
  match lookupNatInfo name allocatorColouring with
  | some colour => colour
  | none => 0

#guard goodColour 2 != goodColour destination
#guard goodColour 3 != goodColour destination
#guard allocatorColour 2 != allocatorColour destination
#guard allocatorColour 3 != allocatorColour destination

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [
      ("no-alias theorem covers the first live-after variable",
        decide (goodColour 2 ≠ goodColour destination)),
      ("no-alias theorem covers the second live-after variable",
        decide (goodColour 3 ≠ goodColour destination)),
      ("allocator output derives live-after no-alias",
        decide (allocatorColour 2 ≠ allocatorColour destination) &&
          decide (allocatorColour 3 ≠ allocatorColour destination))]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.WordColourLivenessParity
