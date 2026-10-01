import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASetup.EvenListDistinct
namespace Flapjack.Test.SSASetupParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
-- Kernel regressions replay the same inputs and observations as the original probe.
private def observe (r : List Nat × Spt Nat × Nat) (keys : List Nat) :=
  (r.1, keys.map (fun k => sptLookup k r.2.1), r.2.2)
example : (evenList 0, evenList 1, evenList 5) = ([],[0],[0,2,4,6,8]) := by decide +kernel
example : observe (listNextVarRename [] (sptFromAList [(9,99)]) 5) [0,1,2,9] =
  ([],[none,none,none,some 99],5) := by decide +kernel
example : observe (listNextVarRename [1,2,1] (sptFromAList [(9,99),(1,88)]) 5) [0,1,2,9] =
  ([5,9,13],[none,some 13,some 9,some 99],17) := by decide +kernel
example : observe (listNextVarRename [0,4] (.bn .ln .ln) 0) [0,1,4] =
  ([0,4],[some 0,none,some 4],8) := by decide +kernel
example : let r := nextVarRename 9 (sptFromAList [(9,99),(1,88)]) 101
  (r.1,[1,9].map (fun k => sptLookup k r.2.1),r.2.2) =
    (101,[some 88,some 101],105) := by decide +kernel
private def setupObservation {width : Nat} [NeZero width] (n start : Nat)
    (p : WordLangProgHOL (BitVec width)) :=
  let r := setupSSA (outputWidth := width) n start p
  (match r.1 with | .move tag moves => (tag,moves) | _ => (0,[]), [0,2,4,6].map (fun k => sptLookup k r.2.1),r.2.2)
example : setupObservation 0 7 (.skip : WordLangProgHOL (BitVec 1)) =
  ((1, []),[none,none,none,none],7) := by decide +kernel
example : setupObservation 1 0 (.assign 999 (.var 999) : WordLangProgHOL (BitVec 32)) =
  ((1, [(0,0)]),[some 0,none,none,none],4) := by decide +kernel
example : setupObservation 3 5 (.skip : WordLangProgHOL (BitVec 64)) =
  ((1, [(5,0),(9,2),(13,4)]),[some 5,some 9,some 13,none],17) := by decide +kernel
example : setupObservation 3 101 (.assign 999 (.var 999) : WordLangProgHOL (BitVec 80)) =
  ((1, [(101,0),(105,2),(109,4)]),[some 101,some 105,some 109,none],113) := by decide +kernel
private def heterogeneousObservation {inputWidth outputWidth : Nat}
    [NeZero inputWidth] [NeZero outputWidth] (n start : Nat)
    (p : WordLangProgHOL (BitVec inputWidth)) :=
  let r := setupSSA (outputWidth := outputWidth) n start p
  (match r.1 with | .move tag moves => (tag,moves) | _ => (0,[]),
    [0,2,4,6].map (fun k => sptLookup k r.2.1),r.2.2)
example : heterogeneousObservation (outputWidth := 80) 3 5
    (.assign 999 (.var 999) : WordLangProgHOL (BitVec 1)) =
    ((1,[(5,0),(9,2),(13,4)]),[some 5,some 9,some 13,none],17) := by decide +kernel
example : heterogeneousObservation (outputWidth := 1) 3 101
    (.assign 999 (.var 999) : WordLangProgHOL (BitVec 80)) =
    ((1,[(101,0),(105,2),(109,4)]),[some 101,some 105,some 109,none],113) := by decide +kernel
-- The unused input carrier must not constrain the independently typed output.
example : (setupSSA (outputWidth := 80) 3 5
    (.assign 999 (.var 999) : WordLangProgHOL (BitVec 1))).1 =
    (.move 1 [(5,0),(9,2),(13,4)] : WordLangProgHOL (BitVec 80)) := by rfl
example : (setupSSA (outputWidth := 1) 3 101
    (.assign 999 (.var 999) : WordLangProgHOL (BitVec 80))).1 =
    (.move 1 [(101,0),(105,2),(109,4)] : WordLangProgHOL (BitVec 1)) := by rfl
-- The full infrastructure theorem applies to every count, without a bound.
example (count : Nat) : (evenList count).Nodup := evenListNodup count
example : (evenList 0).Nodup := evenListNodup 0
example : (evenList 1).Nodup := evenListNodup 1
example : (evenList 5).Nodup := evenListNodup 5
end Flapjack.Test.SSASetupParity
