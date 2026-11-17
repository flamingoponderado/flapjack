module

public import Flapjack.Compiler.Inference.Unify.Walkstar.WorklistDecrease
public import Flapjack.Compiler.Inference.Unify.Walkstar.Computational
public import Flapjack.Misc.OptionLeast.TailRec

@[expose] public section

/-! Agreement of the executed normalization worklist and source tail calls. -/
namespace Flapjack.Compiler.Inference.Unify

/-- On well-formed substitutions, the actual partial worklist has the same
    result as the source step's partial tail recursion for every state. -/
theorem walkStarWorkEqTail (s : Spt InferT) (hw : cwfs s) : ∀ state,
    walkStarWork s state.1 state.2.1 state.2.2 = Flapjack.HOL.tailRecPartial (starWorklistCodeModel s) state := by
  intro state
  induction state using (wfKcwalkstarwlRModel s hw).induction with
  | h state ih =>
    obtain ⟨ready, items, kont⟩ := state
    rw [walkStarWork.eq_def, Flapjack.HOL.tailRecPartial.eq_1]
    cases ready with
    | true =>
      cases kont with
      | nil => simp [starWorklistCodeModel]
      | cons frame rest =>
        cases frame with
        | db n =>
          simp only [↓reduceIte, starWorklistCodeModel]
          apply ih (true, .varDb n :: items, rest)
          exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, rfl⟩
        | app args n =>
          simp only [↓reduceIte, starWorklistCodeModel]
          apply ih (true, .app args n :: items, rest)
          exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, rfl⟩
        | uv n =>
          simp only [↓reduceIte, starWorklistCodeModel]
          apply ih (true, .uvar n :: items, rest)
          exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, rfl⟩
        | cons args n =>
          simp only [↓reduceIte, starWorklistCodeModel]
          apply ih (false, args, .app items n :: rest)
          exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, rfl⟩
    | false =>
      cases items with
      | nil =>
        simp only [Bool.false_eq_true, ↓reduceIte, starWorklistCodeModel]
        apply ih (true, [], kont)
        exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, rfl⟩
      | cons item rest =>
        cases item with
        | varDb n =>
          simp only [Bool.false_eq_true, ↓reduceIte, starWorklistCodeModel]
          apply ih (false, rest, .db n :: kont)
          exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, rfl⟩
        | app args n =>
          simp only [Bool.false_eq_true, ↓reduceIte, starWorklistCodeModel]
          apply ih (false, args, .cons rest n :: kont)
          exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, rfl⟩
        | uvar v =>
          have walk := cvwalkPartialCorrect s hw v
          rw [tcvwalkCorrectModel s v hw] at walk
          simp only [Bool.false_eq_true, ↓reduceIte, starWorklistCodeModel, walk]
          cases found : tcvwalkModel s v with
          | varDb n =>
            apply ih (false, rest, .db n :: kont)
            exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, by simp [starWorklistCodeModel, found]⟩
          | app args n =>
            apply ih (false, args, .cons rest n :: kont)
            exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, by simp [starWorklistCodeModel, found]⟩
          | uvar n =>
            apply ih (false, rest, .uv n :: kont)
            exact kcwalkstarwlEnsuresDecreaseModel s _ _ ⟨hw, by simp [starWorklistCodeModel, found]⟩

/-- The first source tail-recursion phase, using a selected solution. HOL
    leaves divergent-case choices unspecified; correspondence is guarded. -/
noncomputable def tcwalkstarP1Model (s : Spt InferT) (items : List InferT) (kont : List KclKont) :
    List InferT :=
  Flapjack.HOL.tailRecModel (starWorklistCodeModel s) (false, items, kont)

/-- The complete source normalization result, with its original cwfs guard.
    The total head's fallback is unreachable because the proved result is a singleton. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "tcwalkstarwl_correct"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem tcwalkstarwlCorrectModel (s : Spt InferT) (it : InferT) (hw : cwfs s) :
    tWalkstar (Flapjack.HOL.Transfer.Fmsp.sp2fm s) it =
      (tcwalkstarP1Model s [it] []).headD (.uvar 0) := by
  have run := walkStarListCorrect s hw [it]
  change walkStarWork s false [it] [] = some [tWalkstar (Flapjack.HOL.Transfer.Fmsp.sp2fm s) it] at run
  rw [walkStarWorkEqTail s hw (false, [it], [])] at run
  have result : tcwalkstarP1Model s [it] [] = [tWalkstar (Flapjack.HOL.Transfer.Fmsp.sp2fm s) it] :=
    Flapjack.HOL.tailRecModelOfSome _ _ _ run
  simp [result]

end Flapjack.Compiler.Inference.Unify
