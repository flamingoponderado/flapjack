import Flapjack.Pancake.LoopToWord.CompFuncExact

namespace Flapjack

/-- Flapjack-specific structural compiler image: every `Inst` is Arith or
Mem, including both Call continuations. No HOL original declares this property. -/
def wordProgHOLArithMemOnly {α : Type} : WordLangProgHOL α → Prop
  | .inst (.arith _) | .inst (.mem _ _ _) => True
  | .inst _ => False
  | .mustTerminate body => wordProgHOLArithMemOnly body
  | .seq first second => wordProgHOLArithMemOnly first ∧ wordProgHOLArithMemOnly second
  | .ite _ _ _ first second => wordProgHOLArithMemOnly first ∧ wordProgHOLArithMemOnly second
  | .loop _ body _ => wordProgHOLArithMemOnly body
  | .call returns _ _ handler =>
      (match returns with
       | none => True
       | some (_, _, body, _, _) => wordProgHOLArithMemOnly body) ∧
      (match handler with
       | none => True
       | some (_, body, _, _) => wordProgHOLArithMemOnly body)
  | _ => True
termination_by program => sizeOf program

/-- Untagged structural image of HOL comp_def: its only emitted instructions
are Arith and Mem. No source-program or successful-compilation premise. -/
theorem compHOL_arithMemOnly {width : Nat} [NeZero width] (context : Spt Nat)
    (source : HolLoopProg width) (labels : Nat × Nat) :
    wordProgHOLArithMemOnly (LoopToWord.compHOL context source labels).1 := by
  fun_induction LoopToWord.compHOL context source labels <;>
    simp_all [wordProgHOLArithMemOnly]
  case case26 =>
    rename_i target arguments labels values live
    rcases labels with ⟨functionName, nextLabel⟩
    simp [wordProgHOLArithMemOnly]
  case case27 =>
    rename_i target arguments labels values live newLabels name first second handlerLive
      wordFirst firstLabels hfirst wordSecond secondLabels hsecond ihFirst ihSecond
    rcases labels with ⟨functionName, nextLabel⟩
    rcases firstLabels with ⟨firstFunction, firstNext⟩
    rcases secondLabels with ⟨secondFunction, secondNext⟩
    simp only [newLabels] at hfirst
    simp [hfirst, hsecond, wordProgHOLArithMemOnly, ihFirst, ihSecond]

/-- Untagged full instruction-image property for comp_func, with no premise. -/
theorem loopToWordCompFuncHOL_arithMemOnly {width : Nat} [NeZero width]
    (name : Nat) (params : List Nat) (body : HolLoopProg width) :
    wordProgHOLArithMemOnly (loopToWordCompFuncHOL name params body) := by
  unfold loopToWordCompFuncHOL
  exact compHOL_arithMemOnly _ _ _

/-- Flapjack-specific structural absence of `Inst (FP _)`, including both
Call continuations. There is no corresponding HOL declaration to tag. -/
def wordProgHOLNoFP {α : Type} : WordLangProgHOL α → Prop
  | .inst (.fp _) => False
  | .mustTerminate body => wordProgHOLNoFP body
  | .seq first second => wordProgHOLNoFP first ∧ wordProgHOLNoFP second
  | .ite _ _ _ first second => wordProgHOLNoFP first ∧ wordProgHOLNoFP second
  | .loop _ body _ => wordProgHOLNoFP body
  | .call returns _ _ handler =>
      (match returns with
       | none => True
       | some (_, _, body, _, _) => wordProgHOLNoFP body) ∧
      (match handler with
       | none => True
       | some (_, body, _, _) => wordProgHOLNoFP body)
  | _ => True
termination_by program => sizeOf program

end Flapjack
