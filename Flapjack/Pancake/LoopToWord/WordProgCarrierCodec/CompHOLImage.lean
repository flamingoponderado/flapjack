import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec


/-!
# Image of the exact Loop-to-Word compiler in the executable carrier

This module proves a Flapjack-specific bridge fact: every exact HOL-shaped
`compHOL` output is accepted by the partial projection into the separate
production `WordProg` carrier. The theorem is untagged because there is no HOL
declaration relating these two Lean carrier instances. It rules out production
projection failures caused by `Inst Skip`, FP instructions, or add/sub overflow
instructions in exact compiler output. It does not state that the production
compiler calls `compHOL`; that executed-path migration remains tracked by the
parent routing bead.
-/

namespace Flapjack

private theorem option_ne_none_exists {α : Type} {value : Option α}
    (h : value ≠ none) : ∃ someValue, value = some someValue := by
  cases value with
  | none => exact False.elim (h rfl)
  | some someValue => exact ⟨someValue, rfl⟩

/-- Every exact `compHOL` output projects to the executed Word program carrier.
This is an untagged Flapjack-only image theorem, not a port of a HOL theorem:
it connects HOL-shaped output to the distinct production carrier. In
particular it proves that the HOL compiler does not emit any of the unsupported
instruction constructors rejected by `wordLangProgFromHOL`. -/
theorem wordLangProgFromHOL_compHOL_ne_none
    {width : Nat} [NeZero width] (context : Spt Nat)
    (source : HolLoopProg width) (labels : Nat × Nat) :
    wordLangProgFromHOL (LoopToWord.compHOL context source labels).1 ≠ none := by
  let mProg : HolLoopProg width → Prop := fun program =>
    ∀ labels, wordLangProgFromHOL
      (LoopToWord.compHOL context program labels).1 ≠ none
  let mPair : HolLoopProg width × NumSet → Prop := fun pair => mProg pair.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun triple => mProg triple.1 ∧ mProg triple.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun quad => mTriple quad.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg source := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
    case refine_3 =>
      intro destinations operator arguments labels
      cases operator
      case addCarry =>
        cases destinations with
        | nil => simp [LoopToWord.compHOL.eq_4, wordLangProgFromHOL]
        | cons result rest =>
          cases rest with
          | nil => simp [LoopToWord.compHOL.eq_4, wordLangProgFromHOL]
          | cons carry extra =>
            cases extra with
            | nil =>
              cases arguments with
              | nil => simp [LoopToWord.compHOL.eq_4, wordLangProgFromHOL]
              | cons left rest =>
                cases rest with
                | nil => simp [LoopToWord.compHOL.eq_4, wordLangProgFromHOL]
                | cons right rest =>
                  cases rest with
                  | nil => simp [LoopToWord.compHOL.eq_4, wordLangProgFromHOL]
                  | cons carryIn extra =>
                    cases extra with
                    | nil =>
                        simp [LoopToWord.compHOL.eq_3, wordLangProgFromHOL,
                          wordLangInstFromHOL, wordLangArithFromHOL]
                    | cons _ _ =>
                        simp [LoopToWord.compHOL.eq_4, wordLangProgFromHOL]
            | cons _ _ => simp [LoopToWord.compHOL.eq_4, wordLangProgFromHOL]
    case refine_4 =>
      intro operation labels
      cases operation <;> simp [LoopToWord.compHOL.eq_5, LoopToWord.compHOL.eq_6,
        LoopToWord.compHOL.eq_7, wordLangProgFromHOL,
        wordLangInstFromHOL, wordLangArithFromHOL]
    case refine_11 =>
      intro first second ihFirst ihSecond labels
      have hFirst := ihFirst labels
      rw [LoopToWord.compHOL.eq_14]
      cases hFirstComp : LoopToWord.compHOL context first labels with
      | mk compiledFirst nextLabels =>
          have hFirstAccepted : wordLangProgFromHOL compiledFirst ≠ none := by
            simpa [hFirstComp] using hFirst
          have hSecond := ihSecond nextLabels
          cases hSecondComp : LoopToWord.compHOL context second nextLabels with
          | mk compiledSecond finalLabels =>
              have hSecondAccepted : wordLangProgFromHOL compiledSecond ≠ none := by
                simpa [hSecondComp] using hSecond
              cases hFirstProjection : wordLangProgFromHOL compiledFirst with
              | none => exact False.elim (hFirstAccepted hFirstProjection)
              | some productionFirst =>
                  cases hSecondProjection : wordLangProgFromHOL compiledSecond with
                  | none => exact False.elim (hSecondAccepted hSecondProjection)
                  | some productionSecond =>
                      simp [wordLangProgFromHOL, hSecondComp,
                        hFirstProjection, hSecondProjection]
    case refine_12 =>
      intro operator condition right thenBranch elseBranch live ihThen ihElse labels
      have hThen := ihThen labels
      cases right with
      | imm value =>
          rw [LoopToWord.compHOL.eq_15]
          cases hThenComp : LoopToWord.compHOL context thenBranch labels with
          | mk compiledThen nextLabels =>
              have hThenAccepted : wordLangProgFromHOL compiledThen ≠ none := by
                simpa [hThenComp] using hThen
              have hElse := ihElse nextLabels
              cases hElseComp : LoopToWord.compHOL context elseBranch nextLabels with
              | mk compiledElse finalLabels =>
                  have hElseAccepted : wordLangProgFromHOL compiledElse ≠ none := by
                    simpa [hElseComp] using hElse
                  cases hThenProjection : wordLangProgFromHOL compiledThen with
                  | none => exact False.elim (hThenAccepted hThenProjection)
                  | some productionThen =>
                      cases hElseProjection : wordLangProgFromHOL compiledElse with
                      | none => exact False.elim (hElseAccepted hElseProjection)
                      | some productionElse =>
                          simp [wordLangProgFromHOL, hElseComp,
                            hThenProjection, hElseProjection]
      | reg name =>
          rw [LoopToWord.compHOL.eq_16]
          cases hThenComp : LoopToWord.compHOL context thenBranch labels with
          | mk compiledThen nextLabels =>
              have hThenAccepted : wordLangProgFromHOL compiledThen ≠ none := by
                simpa [hThenComp] using hThen
              have hElse := ihElse nextLabels
              cases hElseComp : LoopToWord.compHOL context elseBranch nextLabels with
              | mk compiledElse finalLabels =>
                  have hElseAccepted : wordLangProgFromHOL compiledElse ≠ none := by
                    simpa [hElseComp] using hElse
                  cases hThenProjection : wordLangProgFromHOL compiledThen with
                  | none => exact False.elim (hThenAccepted hThenProjection)
                  | some productionThen =>
                      cases hElseProjection : wordLangProgFromHOL compiledElse with
                      | none => exact False.elim (hElseAccepted hElseProjection)
                      | some productionElse =>
                          simp [wordLangProgFromHOL, hElseComp,
                            hThenProjection, hElseProjection]
    case refine_13 =>
      intro liveIn body liveOut ihBody labels
      have hBody := ihBody labels
      rw [LoopToWord.compHOL.eq_17]
      cases hBodyComp : LoopToWord.compHOL context body labels with
      | mk compiledBody nextLabels =>
          have hBodyAccepted : wordLangProgFromHOL compiledBody ≠ none := by
            simpa [hBodyComp] using hBody
          cases hBodyProjection : wordLangProgFromHOL compiledBody with
          | none => exact False.elim (hBodyAccepted hBodyProjection)
          | some productionBody =>
              simp [wordLangProgFromHOL, hBodyProjection]
    case refine_23 =>
      intro returns target arguments handler hHandler labels
      cases returns with
      | none =>
          simp [LoopToWord.compHOL.eq_26, wordLangProgFromHOL]
      | some resultLive =>
          rcases resultLive with ⟨returnValues, returnLive⟩
          cases handler with
          | none =>
              simp [LoopToWord.compHOL.eq_27, wordLangProgFromHOL,
                wordCutsetsFromHOL]
          | some entry =>
              rcases entry with ⟨exception, first, second, live⟩
              rcases hHandler with ⟨ihFirst, ihSecond⟩
              let newLabels := (labels.1, labels.2 + 1)
              have hFirst := ihFirst newLabels
              let compiledFirst := LoopToWord.compHOL context first newLabels
              have hSecond := ihSecond compiledFirst.2
              obtain ⟨projectedFirst, hProjectedFirst⟩ :=
                option_ne_none_exists hFirst
              obtain ⟨projectedSecond, hProjectedSecond⟩ :=
                option_ne_none_exists hSecond
              simp [LoopToWord.compHOL.eq_28, wordLangProgFromHOL,
                wordCutsetsFromHOL,
                newLabels, compiledFirst, hProjectedFirst, hProjectedSecond]
    case refine_28 =>
      intro first second hFirst hSecond
      exact ⟨hFirst, hSecond⟩
    all_goals simp [mProg, mPair, mTriple, mQuad, mHandler,
      LoopToWord.compHOL.eq_1, LoopToWord.compHOL.eq_2,
      LoopToWord.compHOL.eq_3, LoopToWord.compHOL.eq_4,
      LoopToWord.compHOL.eq_5, LoopToWord.compHOL.eq_6,
      LoopToWord.compHOL.eq_7, LoopToWord.compHOL.eq_8,
      LoopToWord.compHOL.eq_9, LoopToWord.compHOL.eq_10,
      LoopToWord.compHOL.eq_11, LoopToWord.compHOL.eq_12,
      LoopToWord.compHOL.eq_13, LoopToWord.compHOL.eq_14,
      LoopToWord.compHOL.eq_15, LoopToWord.compHOL.eq_16,
      LoopToWord.compHOL.eq_17, LoopToWord.compHOL.eq_18,
      LoopToWord.compHOL.eq_19, LoopToWord.compHOL.eq_20,
      LoopToWord.compHOL.eq_21, LoopToWord.compHOL.eq_22,
      LoopToWord.compHOL.eq_23, LoopToWord.compHOL.eq_24,
      LoopToWord.compHOL.eq_25, LoopToWord.compHOL.eq_26,
      LoopToWord.compHOL.eq_27, LoopToWord.compHOL.eq_28,
      LoopToWord.compHOL.eq_29, LoopToWord.compHOL.eq_30,
      wordLangProgFromHOL, wordLangInstFromHOL, wordCutsetsFromHOL]
  exact hgeneral labels

end Flapjack
