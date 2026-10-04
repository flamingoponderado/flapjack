import Flapjack.Compiler.Backend.LabToTarget.FilterSkip
import Flapjack.Compiler.Backend.LabToTarget.CodeSafety

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Full original safety-disjunction preservation. Both source alternatives
and every FFI-name witness remain unchanged; actual Install fetches pull back
to the unfiltered program. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem noInstallOrNoShareMemFilterSkip {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (ffiNames : List HolFfiName) :
    noInstallOrNoShareMem code ffiNames → noInstallOrNoShareMem (filterSkip code) ffiNames := by
  rintro (⟨hno,hffi⟩ | hno)
  · exact Or.inl ⟨(noShareMemFilterSkip code).mpr hno,hffi⟩
  · apply Or.inr
    intro p position bytes len hfetch
    obtain ⟨originalPc,horiginal⟩ := asmFetchAuxFilterSkip code p
      (.labAsm .install position bytes len) ⟨hfetch,rfl⟩
    exact hno originalPc position bytes len horiginal

end Flapjack.Compiler.Backend.LabToTarget
