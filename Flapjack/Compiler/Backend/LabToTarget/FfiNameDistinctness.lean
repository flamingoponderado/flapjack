import Flapjack.Compiler.Backend.LabToTarget.CodeAppend

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- Full original unconditional distinctness of collected FFI names. The
collector inserts a name only when absent; there is no source validity premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findFfiNames_nodup {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (findFfiNames code).Nodup := by
  fun_induction findFfiNames code
  all_goals try exact List.nodup_nil
  all_goals try assumption
  all_goals rw [listAddIfFresh_thm]
  all_goals split
  all_goals try assumption
  all_goals simp_all [List.nodup_append]
  all_goals intro a ha he
  all_goals subst a
  all_goals contradiction

end Flapjack.Compiler.Backend.LabToTarget
