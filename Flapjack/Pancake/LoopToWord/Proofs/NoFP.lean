import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.CompHOLImage
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

/-- Untagged carrier fact: successful projection excludes FP instructions at
every nested program position, since the instruction codec rejects FP. -/
theorem wordProgHOLNoFP_of_projection {width : Nat}
    (program : WordLangProgHOL (BitVec width))
    (accepted : wordLangProgFromHOL program ≠ none) : wordProgHOLNoFP program := by
  cases program with
  | inst instruction =>
      cases instruction <;> simp_all [wordProgHOLNoFP, wordLangProgFromHOL,
        wordLangInstFromHOL]
  | mustTerminate body =>
      simp only [wordProgHOLNoFP]
      exact wordProgHOLNoFP_of_projection body (by
        intro h; simp [wordLangProgFromHOL, h] at accepted)
  | seq first second =>
      simp only [wordProgHOLNoFP]
      refine ⟨wordProgHOLNoFP_of_projection first ?_,
        wordProgHOLNoFP_of_projection second ?_⟩
      · intro h; simp [wordLangProgFromHOL, h] at accepted
      · intro h; cases wordLangProgFromHOL first <;>
          simp [wordLangProgFromHOL, h] at accepted
  | ite _ _ _ first second =>
      simp only [wordProgHOLNoFP]
      refine ⟨wordProgHOLNoFP_of_projection first ?_,
        wordProgHOLNoFP_of_projection second ?_⟩
      · intro h; simp [wordLangProgFromHOL, h] at accepted
      · intro h; cases wordLangProgFromHOL first <;>
          simp [wordLangProgFromHOL, h] at accepted
  | loop _ body _ =>
      simp only [wordProgHOLNoFP]
      exact wordProgHOLNoFP_of_projection body (by
        intro h; simp [wordLangProgFromHOL, h] at accepted)
  | call returns target arguments handler =>
      cases returns with
      | none =>
          cases handler with
          | none => simp [wordProgHOLNoFP]
          | some entry =>
              rcases hentry : entry with ⟨exception, body, firstLabel, secondLabel⟩
              simp only [wordProgHOLNoFP]
              exact ⟨trivial, wordProgHOLNoFP_of_projection body (by
                intro h; simp [wordLangProgFromHOL, hentry, h] at accepted)⟩
      | some entry =>
          rcases hreturnEntry : entry with ⟨values, sets, body, firstLabel, secondLabel⟩
          have hbody : wordLangProgFromHOL body ≠ none := by
            intro h; simp [wordLangProgFromHOL, hreturnEntry, h] at accepted
          cases handler with
          | none =>
              simp only [wordProgHOLNoFP]
              exact ⟨wordProgHOLNoFP_of_projection body hbody, trivial⟩
          | some entry =>
              rcases hhandlerEntry : entry with
                ⟨exception, handlerBody, handlerFirst, handlerSecond⟩
              simp only [wordProgHOLNoFP]
              refine ⟨wordProgHOLNoFP_of_projection body hbody,
                wordProgHOLNoFP_of_projection handlerBody ?_⟩
              intro h
              cases wordLangProgFromHOL body <;>
                simp [wordLangProgFromHOL, hreturnEntry, hhandlerEntry, h] at accepted
  | _ => simp [wordProgHOLNoFP]
termination_by sizeOf program
decreasing_by
  all_goals simp_all
  all_goals subst_vars
  all_goals simp_all
  all_goals subst_vars
  all_goals decreasing_trivial

/-- Flapjack-specific consequence of the reviewed compiler and its total
carrier projection: `compHOL` emits no FP instruction, including nested
Call return and exception continuations. Source comparison: HOL
`loop_to_wordScript.sml:56-150` emits Inst only with Arith or Mem. This
structural fact alone does not establish evaluator equivalence. -/
theorem compHOL_noFP {width : Nat} [NeZero width] (context : Spt Nat)
    (source : HolLoopProg width) (labels : Nat × Nat) :
    wordProgHOLNoFP (LoopToWord.compHOL context source labels).1 :=
  wordProgHOLNoFP_of_projection _ (wordLangProgFromHOL_compHOL_ne_none context source labels)

/-- Untagged `comp_func` consequence of `compHOL_noFP`; no extra premise on
the source program, variable context, or label state is needed. -/
theorem loopToWordCompFuncHOL_noFP {width : Nat} [NeZero width]
    (name : Nat) (params : List Nat) (body : HolLoopProg width) :
    wordProgHOLNoFP (loopToWordCompFuncHOL name params body) := by
  unfold loopToWordCompFuncHOL
  exact compHOL_noFP _ _ _

end Flapjack
