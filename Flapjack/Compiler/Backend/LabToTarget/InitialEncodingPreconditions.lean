import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Compiler.Backend.LabProps.Native
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Full original initial-encoder preservation theorem. The encoder is arbitrary
and independent of the configuration in the sole precondition premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encSecList_pre {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (enc : HolAsm width → List (BitVec 8)) (c : AsmConfigExact width) :
    allEncOkPreHOL c code → allEncOkPreHOL c (encSecList enc code) := by
  intro hp sec hm
  obtain ⟨original,horiginal,rfl⟩ := List.mem_map.mp hm
  intro line hl
  obtain ⟨input,hinput,rfl⟩ := List.mem_map.mp hl
  have hi := hp original horiginal input hinput
  cases input with
  | label _ _ _ => simp [encLine,lineOkPreHOL]
  | asm _ _ _ => exact hi
  | labAsm _ _ _ _ => simp [encLine,lineOkPreHOL]
end Flapjack.Compiler.Backend.LabToTarget
