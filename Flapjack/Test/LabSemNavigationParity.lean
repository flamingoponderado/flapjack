import Flapjack.Compiler.Backend.LabSem.Navigation

namespace Flapjack.Test.LabSemNavigationParity
open Flapjack.Compiler.Backend.LabSem

private def code : LabProgHOL 8 :=
  [⟨9, []⟩, ⟨1, [.label 1 0 91, .asm (.asmi (.inst (.const 2 11))) [] 31,
    .label 1 5 92, .labAsm (.jump (.lab 2 0)) 0 [] 32, .label 1 7 93,
    .asm (.cbw 3 4) [] 33]⟩, ⟨8, []⟩,
   ⟨2, [.label 2 0 94, .asm (.asmi (.inst .skip)) [] 34,
    .label 2 4 95, .labAsm .halt 0 [] 35]⟩]

-- Original HOL labsem_navigation_probe.out: nav_fetch0=T.
example : asmFetchAux 0 code = some (.asm (.asmi (.inst (.const 2 11))) [] 31) := by simp [code, asmFetchAux, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_fetch1=T.
example : asmFetchAux 1 code = some (.labAsm (.jump (.lab 2 0)) 0 [] 32) := by simp [code, asmFetchAux, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_fetch2=T.
example : asmFetchAux 2 code = some (.asm (.cbw 3 4) [] 33) := by simp [code, asmFetchAux, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_fetch3=T.
example : asmFetchAux 3 code = some (.asm (.asmi (.inst .skip)) [] 34) := by simp [code, asmFetchAux, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_fetch4=T.
example : asmFetchAux 4 code = some (.labAsm .halt 0 [] 35) := by simp [code, asmFetchAux, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_fetch_end=T.
example : asmFetchAux 5 code = none := by simp [code, asmFetchAux, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_length=T.
example : asmCodeLength code = 5 := by simp [code, asmCodeLength, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_entry1=T.
example : locToPc 1 0 code = some 0 := by simp [code, locToPc]

-- Original HOL labsem_navigation_probe.out: nav_entry2=T.
example : locToPc 2 0 code = some 3 := by simp [code, locToPc, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_empty9=T.
example : locToPc 9 0 code = some 0 := by simp [code, locToPc]

-- Original HOL labsem_navigation_probe.out: nav_empty8=T.
example : locToPc 8 0 code = some 3 := by simp [code, locToPc, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_label5=T.
example : locToPc 1 5 code = some 1 := by simp [code, locToPc, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_label7=T.
example : locToPc 1 7 code = some 2 := by simp [code, locToPc, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_label4=T.
example : locToPc 2 4 code = some 4 := by simp [code, locToPc, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_missing=T.
example : locToPc 1 99 code = none := by simp [code, locToPc, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_missingsection=T.
example : locToPc 77 0 code = none := by simp [code, locToPc, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_return0=T.
example : getLabAfter (resultWidth := 8) 0 code = some (.loc 1 5) := by simp [code, nextLabel, getLabAfter, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_return1=T.
example : getLabAfter (resultWidth := 8) 1 code = some (.loc 1 7) := by simp [code, nextLabel, getLabAfter, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_return2=T.
example : getLabAfter (resultWidth := 8) 2 code = some (.loc 2 0) := by simp [code, nextLabel, getLabAfter, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_return3=T.
example : getLabAfter (resultWidth := 8) 3 code = some (.loc 2 4) := by simp [code, nextLabel, getLabAfter, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_return4=T.
example : getLabAfter (resultWidth := 8) 4 code = none := by simp [code, nextLabel, getLabAfter, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_return5=T.
example : getLabAfter (resultWidth := 8) 5 code = none := by simp [code, getLabAfter, isLabelHOL]

-- Original HOL labsem_navigation_probe.out: nav_first_label=T.
example : nextLabel (resultWidth := 8) code = some (.loc 1 0) := by simp [code, nextLabel]

end Flapjack.Test.LabSemNavigationParity
