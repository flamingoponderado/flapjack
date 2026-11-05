import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsAlookupMapParity

open Flapjack

def entries3 : List (String × (Nat × Nat)) :=
  [("a", (1, 10)), ("b", (2, 20))]

def entries4 : List (String × (Nat × Nat × Nat)) :=
  [("a", (1, 10, 100)), ("b", (2, 20, 200))]

/-- Exercise a non-`String` lookup key. -/
def natEntries3 : List (Nat × (Nat × Nat)) :=
  [(1, (1, 10)), (2, (2, 20))]

theorem alookupMap3NatPointwise :
    (fun name => lookupInfo name
        (natEntries3.map (fun entry => (entry.1, entry.2.1, entry.2.2 + 1)))) 2 =
      (lookupInfo 2 natEntries3).map (fun value => (value.1, value.2 + 1)) :=
  by simp [lookupInfo, natEntries3]

theorem alookupMap3Pointwise :
    (fun name => lookupInfo name
        (entries3.map (fun entry => (entry.1, entry.2.1, entry.2.2 + 1)))) "b" =
      (lookupInfo "b" entries3).map (fun value => (value.1, value.2 + 1)) :=
  by simp [lookupInfo, entries3]

theorem alookupMap4Pointwise :
    (fun name => lookupInfo name
        (entries4.map (fun entry =>
          (entry.1, entry.2.1, entry.2.2.1 + 1, entry.2.2.2)))) "b" =
      (lookupInfo "b" entries4).map (fun value => (value.1, value.2.1 + 1, value.2.2)) :=
  by simp [lookupInfo, entries4]

def alookupMapGuard : Bool :=
  (lookupInfo "b" (entries3.map (fun entry => (entry.1, entry.2.1, entry.2.2 + 1))) ==
      some (2, 21)) &&
    (lookupInfo "b"
        (entries4.map (fun entry =>
          (entry.1, entry.2.1, entry.2.2.1 + 1, entry.2.2.2))) ==
      some (2, 21, 200)) &&
    (lookupInfo 2 (natEntries3.map (fun entry => (entry.1, entry.2.1, entry.2.2 + 1))) ==
      some (2, 21))

#eval alookupMapGuard
#guard alookupMapGuard

def runChecks : IO Bool := do
  if alookupMapGuard then
    IO.println "PASS pan_globals ALOOKUP_MAP3/ALOOKUP_MAP4"
    pure true
  else
    IO.println "FAIL pan_globals ALOOKUP_MAP3/ALOOKUP_MAP4"
    pure false

end Flapjack.Test.PanGlobalsAlookupMapParity