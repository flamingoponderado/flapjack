module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.SourceEval.Proofs.ValueRelation
public import Flapjack.SemanticPrimitivesHOL.Primitives

@[expose] public section
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Related values have the same primitive type test and literal destructor. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel_check_type"]
theorem valueRel_checkType (x : EvalOracleState) (v1 v2 : Value) (ty : PrimType)
    (related : ValueRel x v1 v2) :
    checkType ty v1 = checkType ty v2 ∧ destLitv v1 = destLitv v2 := by
  cases related with
  | env decoded _ _ =>
    rw [valueToEnvId_some _ _ decoded]
    cases ty <;> simp [checkType, destLitv]
  | vector _ => cases ty <;> simp [checkType, destLitv]
  | con values =>
    cases values with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ _ => cases ty <;> simp [checkType, destLitv]
  | closure _ => cases ty <;> simp [checkType, destLitv]
  | recclosure _ => cases ty <;> simp [checkType, destLitv]
  | lit _ => exact ⟨rfl, rfl⟩
  | loc _ _ => exact ⟨rfl, rfl⟩

/-- Pointwise related values agree on universal primitive type tests. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "LIST_REL_v_rel_check_type"]
theorem valueRel_listCheckType (x : EvalOracleState) (vs1 vs2 : List Value) (ty : PrimType)
    (related : List.Forall₂ (ValueRel x) vs1 vs2) :
    vs1.all (checkType ty) = vs2.all (checkType ty) := by
  induction related with
  | nil => rfl
  | cons head _ ih => simp only [List.all_cons, (valueRel_checkType _ _ _ _ head).1, ih]

end Flapjack.Compiler.Backend.SourceEval.Proofs
