module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk
public import Flapjack.Compiler.Inference.Unify.Walkstar.Induction

@[expose] public section

/-! Normalization worklist correctness on well-formed substitutions. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Encode a normalized result as a continuation frame. -/
private def resultFrame (t : InferT) : KclKont := match t with
  | .varDb n => .db n
  | .app args n => .app args n
  | .uvar n => .uv n

private theorem normStep (s : Spt InferT) (hw : cwfs s) (t : InferT) (ts : List InferT) (k : List KclKont) :
    walkStarWork s false (t :: ts) k = match tWalk (sp2fm s) t with
      | .varDb n => walkStarWork s false ts (.db n :: k)
      | .uvar n => walkStarWork s false ts (.uv n :: k)
      | .app xs n => walkStarWork s false xs (.cons ts n :: k) := by
  cases t with
  | varDb n =>
    rw [walkStarWork.eq_def]
    simp [tWalkEqn.2.2]
  | app xs n =>
    rw [walkStarWork.eq_def]
    simp [tWalkEqn.2.1]
  | uvar n =>
    rw [walkStarWork.eq_def]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [cvwalkPartialCorrect s hw n, tWalkEqn.1]
    cases h : tVwalk (sp2fm s) n <;> simp [cvwalkModel, h]

private theorem normHead (s : Spt InferT) (hw : cwfs s) :
    ∀ t ts k, walkStarWork s false (t :: ts) k =
      walkStarWork s false ts (resultFrame (tWalkstar (sp2fm s) t) :: k) := by
  have hws : tWfs (sp2fm s) := by
    change WellFounded (vR ((sp2fm s).map2 (fun p => encodeInferT p.2)))
    exact wfCvwalkR s 0 hw
  apply tWalkstarInd (sp2fm s) hws
  intro t ih ts k
  rw [normStep s hw t ts k, walkstarEqn (sp2fm s) hws t]
  cases hit : tWalk (sp2fm s) t with
  | varDb n => rfl
  | uvar u => rfl
  | app args n =>
    have listLoop : ∀ xs : List InferT,
        (∀ a ∈ xs, ∀ tail k, walkStarWork s false (a :: tail) k =
          walkStarWork s false tail (resultFrame (tWalkstar (sp2fm s) a) :: k)) →
        ∀ k, walkStarWork s false xs k = walkStarWork s true (xs.map (tWalkstar (sp2fm s))) k := by
      intro xs
      induction xs with
      | nil =>
        intro h k
        rw [walkStarWork.eq_def]
        rfl
      | cons a xs rec =>
        intro h k
        have ha := h a (by simp)
        have hr := rec (by intro q hq; exact h q (by simp [hq]))
        rw [ha xs k, hr (resultFrame (tWalkstar (sp2fm s) a) :: k)]
        simp only [List.map_cons]
        cases hv : tWalkstar (sp2fm s) a with
        | varDb n => rw [walkStarWork.eq_def]; rfl
        | app xs n => rw [walkStarWork.eq_def]; rfl
        | uvar u => rw [walkStarWork.eq_def]; rfl
    have hall : ∀ a ∈ args, ∀ tail k, walkStarWork s false (a :: tail) k =
        walkStarWork s false tail (resultFrame (tWalkstar (sp2fm s) a) :: k) := by
      intro a ha
      exact ih args n a ⟨hit, ha⟩
    change walkStarWork s false args (.cons ts n :: k) =
      walkStarWork s false ts (.app (args.map (tWalkstar (sp2fm s))) n :: k)
    rw [listLoop args hall (.cons ts n :: k), walkStarWork.eq_def]
    rfl

private theorem normList (s : Spt InferT) (hw : cwfs s) :
    ∀ ts k, walkStarWork s false ts k = walkStarWork s true (ts.map (tWalkstar (sp2fm s))) k := by
  intro ts
  induction ts with
  | nil =>
    intro k
    rw [walkStarWork.eq_def]
    rfl
  | cons t ts ih =>
    intro k
    rw [normHead s hw t ts k, ih (resultFrame (tWalkstar (sp2fm s) t) :: k)]
    simp only [List.map_cons]
    cases hv : tWalkstar (sp2fm s) t with
    | varDb n => rw [walkStarWork.eq_def]; rfl
    | app xs n => rw [walkStarWork.eq_def]; rfl
    | uvar u => rw [walkStarWork.eq_def]; rfl


/-- The executable worklist terminates on a well-formed substitution and
    normalizes each input type. This is a proof bridge for the partial `Option`
    implementation, not a claim about HOL behavior outside well-formedness. -/
theorem walkStarListCorrect (s : Spt InferT) (hw : cwfs s) (ts : List InferT) :
    walkStarList s ts = some (ts.map (tWalkstar (sp2fm s))) := by
  unfold walkStarList
  rw [normList s hw ts [], walkStarWork.eq_def]
  rfl

end Flapjack.Compiler.Inference.Unify
