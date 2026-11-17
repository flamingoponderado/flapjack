module

public import Flapjack.Compiler.Inference.Unify.Source.Equation
public import Flapjack.Compiler.Inference.Unify.WorklistTotal

@[expose] public section

/-! Continuation and tail-recursive correctness for the source unifier. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Source-shaped continuation; untagged because the underlying selected
    list unifier has not been identified outside the well-formedness guard. -/
noncomputable def applyCunifkModel : List (List InferT × List InferT) → Option (Spt InferT) → Option (Spt InferT)
  | [], x => x
  | (_, _) :: rest, none => applyCunifkModel rest none
  | (xs, ys) :: rest, some s => applyCunifkModel rest (cunifylModel s xs ys)

@[hol "cakeml/compiler/inference/unifyScript.sml" "apply_cunif_NONE"]
theorem applyCunifNoneModel (k : List (List InferT × List InferT)) : applyCunifkModel k none = none := by
  induction k with
  | nil => rfl
  | cons p rest ih => cases p; exact ih

/-- Source-shaped continuation entry point, with the same guarded choice
    limitation as the underlying list unifier. -/
noncomputable def kcunifywlModel (s : Spt InferT) (k : List (List InferT × List InferT)) : Option (Spt InferT) :=
  applyCunifkModel k (some s)

private theorem kontBind (k : List (List InferT × List InferT)) (x : Option (Spt InferT)) :
    applyCunifkModel k x = x.bind (fun s => kcunifywlModel s k) := by
  cases x with
  | none => simp [applyCunifNoneModel]
  | some s => rfl

private theorem kontDirect (k : List (List InferT × List InferT)) (x : Option (Spt InferT)) :
    x.bind (fun s => applyCunifkModel k (some s)) = applyCunifkModel k x := by
  cases x with
  | none => exact (applyCunifNoneModel k).symm
  | some s => rfl

private theorem kontCons (rest : List (List InferT × List InferT)) (xs ys : List InferT)
    (x : Option (Spt InferT)) :
    applyCunifkModel ((xs, ys) :: rest) x = x.bind (fun s =>
      (cunifylModel s xs ys).bind (fun s' => applyCunifkModel rest (some s'))) := by
  cases x with
  | none => exact applyCunifNoneModel rest
  | some s => exact (kontDirect rest _).symm

@[hol "cakeml/compiler/inference/unifyScript.sml" "kcunifywl_tcallish"]
theorem kcunifywlTcallishModel (p : Spt InferT × List (List InferT × List InferT)) (hw : cwfs p.1) :
    kcunifywlModel p.1 p.2 = Flapjack.HOL.tailCall cunifyCodeModel (fun q => kcunifywlModel q.1 q.2) p := by
  classical
  rcases p with ⟨s, work⟩
  cases work with
  | nil => rfl
  | cons pair rest =>
    obtain ⟨xs, ys⟩ := pair
    rw [kcunifywlModel, applyCunifkModel, cunifylThmModel s xs ys hw]
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [kcunifywlModel, Flapjack.HOL.tailCall, cunifyCodeModel]
      | cons b bs => simp [applyCunifNoneModel, Flapjack.HOL.tailCall, cunifyCodeModel]
    | cons a as' =>
      cases ys with
      | nil => simp [applyCunifNoneModel, Flapjack.HOL.tailCall, cunifyCodeModel]
      | cons b bs =>
        simp only
        rw [kontBind]
        have heq := cunifyThmModel s a b hw
        rw [tcwalkCorrectModel s a hw, tcwalkCorrectModel s b hw] at heq
        have occurs : ∀ ts v, (∃ t ∈ ts, cocModel s t v) ↔ tcocwlModel s v [ts] = true := by
          intro ts v
          exact (coclExists s ts v).symm.trans (tcocwlCorrectModel s ts v hw)
        cases ha : tcwalkModel s a <;> cases hb : tcwalkModel s b <;>
          simp only [ha, hb] at heq
        all_goals rw [heq]
        all_goals simp [Flapjack.HOL.tailCall, cunifyCodeModel, ha, hb, occurs,
          kcunifywlModel, applyCunifkModel, Option.bind_assoc]
        all_goals try (split <;> simp_all [applyCunifkModel])
        all_goals first | exact kontDirect _ _ | exact (kontCons _ _ _ _).symm

@[hol "cakeml/compiler/inference/unifyScript.sml" "kcunifywl_cleaned"]
theorem kcunifywlCleanedModel (p : Spt InferT × List (List InferT × List InferT)) (hw : cwfs p.1) :
    kcunifywlModel p.1 p.2 = Flapjack.HOL.tailRecModel cunifyCodeModel p := by
  have wf : WellFounded worklistR := wfKcunifywlR
  induction p using wf.induction with
  | h p ih =>
    rw [kcunifywlTcallishModel p hw, Flapjack.HOL.tailRecModelEq]
    cases step : cunifyCodeModel p with
    | inl next =>
      simp only [Flapjack.HOL.tailCall, step]
      apply ih next (kcunifywlEnsuresDecreaseModel next p ⟨hw, step⟩)
      exact kcunifywlPreservesPrecondModel p next ⟨hw, step⟩
    | inr result => simp [Flapjack.HOL.tailCall, step]

/-- Selected tail-recursive solution. Its behavior on nonterminating inputs
    is not identified with HOL's choice, so the definition is untagged. -/
noncomputable def tcunifyModel (s : Spt InferT) (work : List (List InferT × List InferT)) :
    Option (Spt InferT) := Flapjack.HOL.tailRecModel cunifyCodeModel (s, work)

@[hol "cakeml/compiler/inference/unifyScript.sml" "tcunify_correct"]
theorem tcunifyCorrectModel (s : Spt InferT) (a b : InferT) (hw : cwfs s) :
    cunifyModel s a b = tcunifyModel s [([a], [b])] := by
  change cunifyModel s a b = Flapjack.HOL.tailRecModel cunifyCodeModel (s, [([a], [b])])
  rw [← kcunifywlCleanedModel (s, [([a], [b])]) hw]
  unfold kcunifywlModel
  simp only [applyCunifkModel]
  rw [cunifylThmModel s [a] [b] hw]
  cases result : cunifyModel s a b with
  | none => simp [result]
  | some mid =>
    have hm := (cunifyUnifierModel s a b mid ⟨hw, result⟩).1
    simp only [result, Option.bind]
    rw [cunifylThmModel mid [] [] hm]

/-- The executed partial operation terminates and returns the source-shaped
    result on the original guard. The outer option is Lean execution
    infrastructure and is absent from the HOL theorem. -/
theorem unifyPartialMatchesSource (s : Spt InferT) (a b : InferT) (hw : cwfs s) :
    unifyPartial s a b = some (cunifyModel s a b) := by
  unfold unifyPartial
  rw [unifyWorkPartialMatchesTail (s, [([a], [b])]) hw]
  rw [tcunifyCorrectModel s a b hw]
  rfl

end Flapjack.Compiler.Inference.Unify
