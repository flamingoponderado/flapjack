module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.SourceEval.Proofs.ValueRelationSimps
public import Flapjack.SemanticPrimitivesHOL.Conversions
public import Mathlib.Data.List.Forall2

@[expose] public section
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- List encoding preserves and reflects the source value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel_list_to_v"]
theorem vRelListToValue (es : EvalOracleState) :
    ∀ xs ys, ValueRel es (listToValue xs) (listToValue ys) ↔ List.Forall₂ (ValueRel es) xs ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys
    cases ys with
    | nil =>
      constructor <;> intro _
      · exact .nil
      · exact .con .nil
    | cons y ys =>
      constructor
      · intro rel
        simp only [listToValue] at rel
        cases rel
      · intro rel; cases rel
  | cons x xs ih =>
    intro ys
    cases ys with
    | nil =>
      constructor
      · intro rel
        simp only [listToValue] at rel
        cases rel
      · intro rel; cases rel
    | cons y ys =>
      simp only [listToValue]
      constructor
      · intro rel
        cases rel with
        | con fields =>
          cases fields with
          | cons head tail =>
            cases tail with
            | cons last tail =>
              exact .cons head ((ih ys).mp last)
      · intro rel
        cases rel with
        | cons head tail =>
          exact .con (.cons head (.cons ((ih ys).mpr tail) .nil))

/-- Successful list decoding is preserved by the source value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_to_list"]
theorem valueToList_related (es : EvalOracleState) :
    ∀ x y xs, valueToList x = some xs ∧ ValueRel es x y →
      ∃ ys, valueToList y = some ys ∧ List.Forall₂ (ValueRel es) xs ys := by
  intro x y xs ⟨decoded, related⟩
  induction x using valueToList.induct generalizing y xs with
  | case1 =>
    simp only [valueToList, ite_true, Option.some.injEq] at decoded
    subst xs
    cases related with
    | con fields =>
      cases fields
      exact ⟨[], by simp [valueToList], .nil⟩
  | case2 stamp ne => simp [valueToList, ne] at decoded
  | case3 head tail ih =>
    simp only [valueToList, ite_true] at decoded
    cases related with
    | con fields =>
      cases fields with
      | cons headRel rest =>
        cases rest with
        | cons tailRel nilRel =>
          cases nilRel
          cases hv : valueToList tail with
          | none => simp [hv] at decoded
          | some rest =>
            simp [hv] at decoded
            subst xs
            obtain ⟨ys, target, paired⟩ := ih _ _ hv tailRel
            exact ⟨_ :: ys, by simp [valueToList, target], .cons headRel paired⟩
  | case4 stamp head tail ne => simp [valueToList, ne] at decoded
  | case5 x hnil hcons => simp [valueToList] at decoded

/-- Character-list decoding is unchanged for related source values. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_to_char_list"]
theorem valueToCharList_related (es : EvalOracleState) :
    ∀ x y xs, valueToCharList x = some xs ∧ ValueRel es x y → valueToCharList y = some xs := by
  intro x y xs ⟨decoded, related⟩
  induction x using valueToCharList.induct generalizing y xs with
  | case1 =>
    simp [valueToCharList] at decoded
    subst xs
    cases related with
    | con fields =>
      cases fields
      simp [valueToCharList]
  | case2 stamp ne => simp [valueToCharList, ne] at decoded
  | case3 head tail ih =>
    simp only [valueToCharList, ite_true] at decoded
    cases related with
    | con fields =>
      cases fields with
      | cons headRel rest =>
        cases rest with
        | cons tailRel nilRel =>
          cases nilRel
          cases headRel
          cases hv : valueToCharList tail with
          | none => simp [hv] at decoded
          | some rest =>
            simp [hv] at decoded
            subst xs
            have hy := ih _ _ hv tailRel
            simp [valueToCharList, hy]
  | case4 stamp head tail ne => simp [valueToCharList, ne] at decoded
  | case5 x hnil hcons => simp [valueToCharList] at decoded

/-- String decoding is unchanged for pointwise related source values. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "vs_to_string"]
theorem valuesToString_related (es : EvalOracleState) :
    ∀ xs ys s, valuesToString xs = some s ∧ List.Forall₂ (ValueRel es) xs ys →
      valuesToString ys = some s := by
  intro xs ys s ⟨decoded, related⟩
  induction related generalizing s with
  | nil => simpa using decoded
  | @cons x y xs ys head tail ih =>
    cases head with
    | lit l =>
      cases l with
      | strLit str =>
        cases result : valuesToString xs with
        | none => simp [valuesToString, result] at decoded
        | some suffix =>
          have preserved := ih suffix result
          simpa [valuesToString, result, preserved] using decoded
      | _ => simp [valuesToString] at decoded
    | _ => simp [valuesToString] at decoded

end Flapjack.Compiler.Backend.SourceEval.Proofs
