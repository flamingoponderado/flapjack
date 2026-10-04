import Flapjack.Pancake.LoopToWord.Proofs.NoFP
import Flapjack.Pancake.WordConvs

namespace Flapjack

/-- Flapjack proof helper combining the two source label-threading invariants.
HOL states the components separately; this conjunction has no separate original. -/
private theorem compHOLLabelBounds {width : Nat} [NeZero width] (context : Spt Nat)
    (source : HolLoopProg width) (labels : Nat × Nat) :
    (LoopToWord.compHOL context source labels).2.1 = labels.1 ∧
      labels.2 ≤ (LoopToWord.compHOL context source labels).2.2 := by
  fun_induction LoopToWord.compHOL context source labels <;> simp_all
  case case14 => omega
  case case15 => omega
  case case27 =>
    rename_i target arguments labels values live newLabels name first second handlerLive
      wordFirst firstLabels hfirst wordSecond secondLabels hsecond ihFirst ihSecond
    dsimp [newLabels] at hfirst ihFirst ihSecond
    simp_all
    omega

/-- The original compiler preserves the function-label component for every
source program and initial label pair, including both Call continuations. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordCompLInvariant {width : Nat} [NeZero width]
    (context : Spt Nat) (source : HolLoopProg width) (labels : Nat × Nat)
    (compiled : WordLangProgHOL (BitVec width)) (finalLabels : Nat × Nat)
    (h : LoopToWord.compHOL context source labels = (compiled, finalLabels)) :
    finalLabels.1 = labels.1 := by
  have bounds := compHOLLabelBounds context source labels
  rw [h] at bounds
  exact bounds.1

/-- The original compiler never decreases the next-label component. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordCompSndLE {width : Nat} [NeZero width]
    (context : Spt Nat) (source : HolLoopProg width) (labels : Nat × Nat)
    (compiled : WordLangProgHOL (BitVec width)) (finalLabels : Nat × Nat)
    (h : LoopToWord.compHOL context source labels = (compiled, finalLabels)) :
    labels.2 ≤ finalLabels.2 := by
  have bounds := compHOLLabelBounds context source labels
  rw [h] at bounds
  exact bounds.2

/-- Every compiled handler belongs to the original function-label component.
There is no premise restricting the source program or its handler bodies. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordGoodHandlersComp {width : Nat} [NeZero width]
    (context : Spt Nat) (source : HolLoopProg width) (labels : Nat × Nat) :
    goodHandlersHOL labels.1 (LoopToWord.compHOL context source labels).1 = true := by
  fun_induction LoopToWord.compHOL context source labels <;>
    simp_all [goodHandlersHOL]
  case case14 =>
    rename_i first second labels wordFirst firstLabels hfirst wordSecond secondLabels hsecond ihFirst ihSecond
    have sameFirst := loopToWordCompLInvariant context first labels wordFirst firstLabels hfirst
    simp_all
  case case15 =>
    rename_i operator condition right first second live labels wordFirst firstLabels hfirst wordSecond secondLabels hsecond ihFirst ihSecond
    have sameFirst := loopToWordCompLInvariant context first labels wordFirst firstLabels hfirst
    simp_all
  case case27 =>
    rename_i target arguments labels values live newLabels name first second handlerLive
      wordFirst firstLabels hfirst wordSecond secondLabels hsecond ihFirst ihSecond
    have sameFirst := loopToWordCompLInvariant context first newLabels wordFirst firstLabels hfirst
    have sameSecond := loopToWordCompLInvariant context second firstLabels wordSecond secondLabels hsecond
    rcases labels with ⟨functionName, nextLabel⟩
    rcases firstLabels with ⟨firstFunction, firstNext⟩
    rcases secondLabels with ⟨secondFunction, secondNext⟩
    dsimp [newLabels] at hfirst sameFirst ihFirst
    simp_all

/-- The full compiled program list satisfies the original per-function
handler-ownership invariant, with precisely HOL's compile_prog equality premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem loopToWordGoodHandlers {width : Nat} [NeZero width]
    (source : List (Nat × List Nat × HolLoopProg width))
    (compiled : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : loopToWordCompileProgHOL source = compiled) :
    compiled.all (fun row => goodHandlersHOL row.1 row.2.2) = true := by
  subst compiled
  simp only [loopToWordCompileProgHOL, List.all_map, List.all_eq_true]
  intro row _
  simp only [Function.comp_apply, loopToWordCompFuncHOL]
  exact loopToWordGoodHandlersComp (width := width) _ row.2.2 (row.1, 2)

end Flapjack
