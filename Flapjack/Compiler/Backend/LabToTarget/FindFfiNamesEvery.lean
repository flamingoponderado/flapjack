import Flapjack.Compiler.Backend.LabToTarget.CodeAppend

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Basis.Pure.MlString

/-- Full original output classification of the actual FFI-name collector. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findFfiNamesEvery {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (names : List HolFfiName) :
    findFfiNames code = names → ∀ name ∈ names, ∃ s, name = .extCall s := by
  intro heq
  subst names
  fun_induction findFfiNames code with
  | case1 => simp
  | case2 k rest ih => simpa only [findFfiNames] using ih
  | case3 k xs rest s pos bytes len ih =>
    rw [listAddIfFresh_thm]
    split
    · exact ih
    · intro name hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact ih name hmem
      · exact ⟨s, List.mem_singleton.mp hmem⟩
  | case4 k x xs rest hx ih => exact ih

end Flapjack.Compiler.Backend.LabToTarget
