import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.ProgramInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.FullSSA
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LimitVar.Properties

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Original complete full SSA instruction-validity theorem. Source limit and
setup properties discharge the recursive theorem hypotheses. Only the original
source instruction-validity premise remains; no target property is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fullSsaCcTrans_fullInstOkLess {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (count : Nat) (program : WordLangProgHOL (BitVec width))
    (source : fullInstOkLessExact config program = true) :
    fullInstOkLessExact config (fullSsaCcTrans count program) = true := by
  have limitProps := limitVarProps program (limitVar program) rfl
  have setup := setupSSAProps2 (limitVar program) count program limitProps.1
  generalize produced : setupSSA (outputWidth := width) count (limitVar program) program = result
  rcases result with ⟨move, ssa, next⟩
  rw [produced] at setup
  have bound : everyVarHOL (fun x => decide (x < next)) program = true := by
    apply everyVarMono _ program _
    refine ⟨?_, limitProps.2⟩
    intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    have increase := setup.2.2.2
    omega
  have bodyValid := ssaCcTrans_fullInstOkLess config program ssa next []
    ⟨bound, setup.2.1, setup.1, source⟩
  have moveValid : fullInstOkLessExact config move = true := by
    unfold setupSSA at produced
    generalize listNextVarRename (evenList count) .ln (limitVar program) = renamed at produced
    rcases renamed with ⟨names, tree, counter⟩
    cases produced
    rfl
  generalize bodyEq : ssaCcTrans program ssa next [] = bodyResult
  rcases bodyResult with ⟨body, finalMap, finalNext⟩
  rw [bodyEq] at bodyValid
  simp only [fullSsaCcTrans, produced, bodyEq, fullInstOkLessExactSeq, moveValid, bodyValid]
  rfl

end Flapjack.WordAlloc
