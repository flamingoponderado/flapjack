import Flapjack.Compiler.Backend.LabToTarget.NavigationBounds

namespace Flapjack.Test.LabToTargetNavigationBoundsParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps
private def lines : List (LabLineHOL 8) :=
  [.asm (.cbw 1 2) [] 99, .label 1 5 42, .labAsm .halt 0 [] 88, .label 1 7 43]
private def code : LabProgHOL 8 :=
  [⟨9, [.asm (.cbw 3 4) [] 100, .label 9 8 44]⟩, ⟨1, lines⟩, ⟨2, []⟩]
example : secLocToPc 0 ([] : List (LabLineHOL 1)) = some 0 := by decide +kernel
example : secLocToPc 7 lines = some 2 := by decide +kernel
example : lenNoLab lines = 2 := by decide +kernel
example : locToPc 2 0 code = some 3 := by decide +kernel
example : (code.map (fun sec => lenNoLab sec.lines)).sum = 3 := by decide +kernel
example : secLocToPc 0 ([] : List (LabLineHOL 80)) = some 0 := by decide +kernel
-- Full theorem applications exercise equality at the final instruction boundary.
example : 2 ≤ lenNoLab lines := secLocToPc_bound 7 lines 2 (by decide +kernel)
example : 3 ≤ (code.map (fun sec => lenNoLab sec.lines)).sum :=
  locToPc_bound code 2 0 3 ⟨by simp [code, lines, secLabelsOk, secLabelOk], by decide +kernel⟩
-- Arbitrary-width theorem applications retain all native instruction carriers.
example {width : Nat} [NeZero width] (xs : List (LabLineHOL width)) :
    0 ≤ lenNoLab xs := secLocToPc_bound 0 xs 0 (by cases xs <;> simp [secLocToPc])

def runChecks : IO Bool := do
  IO.println "PASS original native navigation bounds (6 observations, 3 theorem applications)"
  return true
end Flapjack.Test.LabToTargetNavigationBoundsParity
