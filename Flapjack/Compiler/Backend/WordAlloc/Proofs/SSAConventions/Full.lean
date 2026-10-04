import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Program
import Flapjack.Compiler.Backend.WordAlloc.FullSSA
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LimitVar.Properties

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Original unconditional full SSA pre-convention theorem. The source limit
and setup properties establish the input hypotheses of the full recursive
compiler theorem; no target convention or evaluation is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fullSsaCcTrans_preAllocConventions {width : Nat} [NeZero width]
    (count : Nat) (program : WordLangProgHOL (BitVec width)) :
    preAllocConventionsHOL (fullSsaCcTrans count program) = true := by
  have allocated := (limitVarProps program (limitVar program) rfl).1
  have setup := setupSSAProps2 (limitVar program) count program allocated
  generalize produced : setupSSA (outputWidth := width) count (limitVar program) program = result
  rcases result with ⟨move, ssa, next⟩
  rw [produced] at setup
  have bodyPre := ssaCcTrans_preAllocConventions program ssa next [] ⟨setup.2.1, setup.1⟩
  generalize bodyEq : ssaCcTrans program ssa next [] = bodyResult
  rcases bodyResult with ⟨body, finalMap, finalNext⟩
  rw [bodyEq] at bodyPre
  simp only [fullSsaCcTrans, produced, bodyEq]
  simp only [preAllocConventionsHOL, everyStackVarHOL, callArgConventionHOL,
    Bool.and_eq_true] at bodyPre ⊢
  have movePre := setup.2.2.1
  simp only [preAllocConventionsHOL, Bool.and_eq_true] at movePre
  exact ⟨⟨movePre.1, bodyPre.1⟩, movePre.2, bodyPre.2⟩

end Flapjack.WordAlloc
