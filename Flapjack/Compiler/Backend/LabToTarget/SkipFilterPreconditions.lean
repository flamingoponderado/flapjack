import Flapjack.Compiler.Backend.LabFilter.Map
import Flapjack.Compiler.Backend.LabProps.Native

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabFilter

/-- Full original pre-encoding preservation under the actual skip filter.
Every surviving line retains its original precondition; no successful
compilation or post-encoding condition is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem allEncOkPreFilterSkip {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString)
      (BitVec width)))) (config : AsmConfigExact width) :
    allEncOkPreHOL config code → allEncOkPreHOL config (filterSkip code) := by
  intro hsource sectionData hmem line hline
  rw [filterSkipMap] at hmem
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmem
  exact hsource original horiginal line (List.mem_filter.mp hline).1

end Flapjack.Compiler.Backend.LabToTarget
