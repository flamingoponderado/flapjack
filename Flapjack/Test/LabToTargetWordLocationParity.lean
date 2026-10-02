import Flapjack.Compiler.Backend.LabToTarget.WordLocation
namespace Flapjack.Test.LabToTargetWordLocationParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget
private def labs : Spt (Spt Nat) := sptInsert 1 (sptInsert 5 20 .ln) .ln
example : wordLocVal (100 : BitVec 8) labs (.word 255) = some 255 := by decide +kernel
example : wordLocVal (100 : BitVec 8) labs (.loc 1 5) = some 120 := by decide +kernel
example : wordLocVal (250 : BitVec 8) labs (.loc 1 5) = some 14 := by decide +kernel
example : wordLocVal (100 : BitVec 8) labs (.loc 2 5) = none := by decide +kernel
example : wordLocVal (100 : BitVec 8) labs (.loc 1 6) = none := by decide +kernel
example : wordLocVal (1 : BitVec 1) labs (.loc 1 5) = some 1 := by decide +kernel
example {width : Nat} [NeZero width] (p w : BitVec width) (xs : Spt (Spt Nat)) :
    wordLocVal p xs (.word w) = some w := rfl
example {width : Nat} [NeZero width] (p : BitVec width) (xs : Spt (Spt Nat))
    (k1 k2 q : Nat) (h : labLookup k1 k2 xs = some q) :
    wordLocVal p xs (.loc k1 k2) = some (p + BitVec.ofNat width q) := by
  simp [wordLocVal, h]
example {width : Nat} [NeZero width] (p : BitVec width) (xs : Spt (Spt Nat))
    (k1 k2 : Nat) (h : labLookup k1 k2 xs = none) :
    wordLocVal p xs (.loc k1 k2) = none := by simp [wordLocVal, h]

def runChecks : IO Bool := do
  IO.println "PASS original word/location conversion (6 observations, 3 full generic consumers)"
  return true
end Flapjack.Test.LabToTargetWordLocationParity
