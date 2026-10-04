import Flapjack.Compiler.Backend.WordAlloc.WordAllocDef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SelectRegAllocCorrect
import Flapjack.Compiler.Backend.WordAlloc.Proofs.GetForced
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashOccurrences
import Flapjack.Compiler.Backend.WordAlloc.Proofs.OracleConventions
import Flapjack.Pancake.WordConvs.StackOccurrences

namespace Flapjack.WordAlloc
open Flapjack Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm
attribute [local instance] Classical.propDecidable

/-- Original allocator pre/post convention theorem, with only the original
source pre-convention premise. Native allocator success, occurrence support,
physical fixation and stack bounds are proved from the original algorithms. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem prePostConventions_wordAlloc {width : Nat} [NeZero width]
    (fc : Nat) (c : AsmConfigExact width) (alg : Nat)
    (prog : WordLangProgHOL (BitVec width)) (k : Nat) (colOpt : Option (Spt Nat)) :
    preAllocConventionsHOL prog = true →
      postAllocConventionsHOL k (wordAlloc fc c alg k prog colOpt) = true := by
  intro pre
  cases oracle : oracleColourOk k colOpt (getClashTree prog []) prog (getForced c prog []) with
  | some output =>
      simp only [wordAlloc, oracle]
      exact oracleColourOk_conventions prog k colOpt [] (getForced c prog []) output ⟨pre, oracle⟩
  | none =>
      obtain ⟨colour, liveIn, fullLiveIn, selected, _checked, conventions, _support, _forced⟩ :=
        selectRegAllocCorrect alg (getHeuristics alg fc prog).2 k
          (getHeuristics alg fc prog).1 (getClashTree prog []) (getForced c prog [])
          (getStackOnly prog) (getForcedInGetClashTree prog [] c)
      simp only [wordAlloc, oracle, selected]
      simp only [preAllocConventionsHOL, Bool.and_eq_true] at pre
      have occurrences := everyVar_inGetClashTree prog []
      simp only [postAllocConventionsHOL, Bool.and_eq_true]
      refine ⟨everyVar_isPhyVar_totalColour colour prog, ?_, ?_⟩
      · apply everyStackVar_applyColour
          (fun x => decide (inClashTree (getClashTree prog []) x) && isStackVar x)
          prog (fun x => decide (2 * k ≤ x)) (totalColour colour)
        refine ⟨(everyStackVarConj _ prog _).mp
          ⟨everyVarImpEveryStackVar _ prog occurrences, pre.1⟩, ?_⟩
        intro x hx
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
        have bound := (conventions x hx.1).2
        have notPhysical : isPhyVar x = false := by
          simp [isPhyVar, isStackVar] at hx ⊢
          omega
        simp only [notPhysical, Bool.false_eq_true, if_false, hx.2, if_true] at bound
        rw [totalColourAlt]
        simp only [Function.comp_apply]
        omega
      · apply callArgConvention_preservation
        refine ⟨everyVarMono _ prog _ ⟨?_, occurrences⟩, pre.2⟩
        intro x hx
        simp only [decide_eq_true_eq] at hx
        by_cases physical : isPhyVar x = true
        · have fixed := (conventions x hx).2
          simp only [physical, if_true] at fixed
          simp only [physical, Bool.not_true, Bool.false_or, beq_iff_eq]
          rw [totalColourAlt]
          simp only [Function.comp_apply, fixed]
          simp [isPhyVar] at physical
          omega
        · simp [physical]

end Flapjack.WordAlloc
