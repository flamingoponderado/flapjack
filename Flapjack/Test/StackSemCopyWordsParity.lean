import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts

/-! Kernel replay of all four direct original HOL `copy_words_def` observations.
Source: `cakeml/compiler/backend/semantics/stackSemScript.sml:711-722`; fixture
`scripts/hol-probes/stacksem_copy_words_probe.out`. -/
namespace Flapjack.Test.StackSemCopyWordsParity
open StackSemStoreConsts

/-- Project a successful outer-copy result onto the final address and the memory
cells at the listed addresses, matching the HOL probe's observed tuple. -/
private def project {width : Nat} [NeZero width] (addrs : List (BitVec width))
    (r : Option (BitVec width × (BitVec width → WordLocW width))) :
    Option (BitVec width × List (WordLocW width)) :=
  match r with
  | none => none
  | some (a, m) => some (a, addrs.map m)

-- normal_continue
example : project [0, 1, 2, 6, 7] (copyWordsExact 0 (0 : BitVec 8) 100
    ([0x81, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x01] : List (BitVec 8))
    (fun _ => True) (fun _ => .loc 9 9)) =
    some (7, [.word 117, .word 34, .word 51, .word 119, .loc 9 9]) := by decide +kernel

-- stops_early
example : project [0, 1, 5, 6] (copyWordsExact 0 (0 : BitVec 8) 100
    ([0x7F, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F] : List (BitVec 8))
    (fun _ => True) (fun _ => .loc 9 9)) =
    some (6, [.word 110, .word 111, .word 115, .loc 9 9]) := by decide +kernel

-- zero_pattern
example : project [0] (copyWordsExact 0 (0 : BitVec 8) 100
    ([0x81, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x00] : List (BitVec 8))
    (fun _ => True) (fun _ => .loc 9 9)) = none := by decide +kernel

-- out_of_range
example : project [0] (copyWordsExact 5 (0 : BitVec 8) 100
    ([0x01, 0x02] : List (BitVec 8))
    (fun _ => True) (fun _ => .loc 9 9)) = none := by decide +kernel

/-- Executable PASS check for the four fixtures above. -/
def runChecks : IO Bool := do
  let rows : List (String × Bool) := [
    ("normal_continue", project [0, 1, 2, 6, 7] (copyWordsExact 0 (0 : BitVec 8) 100
      ([0x81, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x01] : List (BitVec 8))
      (fun _ => True) (fun _ => .loc 9 9)) ==
      some (7, [.word 117, .word 34, .word 51, .word 119, .loc 9 9])),
    ("stops_early", project [0, 1, 5, 6] (copyWordsExact 0 (0 : BitVec 8) 100
      ([0x7F, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F] : List (BitVec 8))
      (fun _ => True) (fun _ => .loc 9 9)) ==
      some (6, [.word 110, .word 111, .word 115, .loc 9 9])),
    ("zero_pattern", project [0] (copyWordsExact 0 (0 : BitVec 8) 100
      ([0x81, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x00] : List (BitVec 8))
      (fun _ => True) (fun _ => .loc 9 9)) == none),
    ("out_of_range", project [0] (copyWordsExact 5 (0 : BitVec 8) 100
      ([0x01, 0x02] : List (BitVec 8))
      (fun _ => True) (fun _ => .loc 9 9)) == none)]
  if rows.all (·.2) then
    IO.println "StackSemCopyWordsParity: PASS (4/4 probe rows)"
    pure true
  else
    IO.println "StackSemCopyWordsParity: FAIL (probe row mismatch)"
    pure false

end Flapjack.Test.StackSemCopyWordsParity
