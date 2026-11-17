module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.TypeSystemHOL.Environments

@[expose] public section

/-! Substitution and shift cancellation for inference and semantic types. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.TypeSystemHOL

mutual
/-- Structural induction for cancellation of an inference-type shift. -/
private theorem dbSubstIncIdType (inst : List InferT) (t : InferT) :
    inferDeBruijnSubst inst (inferDeBruijnInc inst.length t) = t := by
  cases t with
  | uvar v => simp [inferDeBruijnInc, inferDeBruijnSubst]
  | varDb v => simp [inferDeBruijnInc, inferDeBruijnSubst]
  | app ts tc =>
    simp [inferDeBruijnInc, inferDeBruijnSubst, dbSubstIncIdList inst ts]
termination_by sizeOf t

/-- List induction for cancellation of an inference-type shift. -/
private theorem dbSubstIncIdList (inst : List InferT) (ts : List InferT) :
    inferDeBruijnSubstList inst (inferDeBruijnIncList inst.length ts) = ts := by
  cases ts with
  | nil => simp [inferDeBruijnIncList, inferDeBruijnSubstList]
  | cons t ts =>
    simp [inferDeBruijnIncList, inferDeBruijnSubstList,
      dbSubstIncIdType inst t, dbSubstIncIdList inst ts]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "db_subst_inc_id"]
theorem dbSubstIncId (inst : List InferT) (t : InferT) :
    inferDeBruijnSubst inst (inferDeBruijnInc inst.length t) = t :=
  dbSubstIncIdType inst t

mutual
/-- Structural induction for the source empty declarative substitution. -/
private theorem deBruijnSubstNothingType (t : SemanticT) : deBruijnSubst 0 [] t = t := by
  cases t with
  | var name => simp [deBruijnSubst]
  | varDb n => simp [deBruijnSubst]
  | app ts tc => simp [deBruijnSubst, deBruijnSubstNothingList ts]
termination_by sizeOf t

/-- List induction for the source empty declarative substitution. -/
private theorem deBruijnSubstNothingList (ts : List SemanticT) : deBruijnSubstList 0 [] ts = ts := by
  cases ts with
  | nil => simp [deBruijnSubstList]
  | cons t ts => simp [deBruijnSubstList, deBruijnSubstNothingType t, deBruijnSubstNothingList ts]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "deBruijn_subst_nothing"]
theorem deBruijnSubstNothing :
    (∀ t : SemanticT, deBruijnSubst 0 [] t = t) ∧
    (∀ ts : List SemanticT, ts.map (deBruijnSubst 0 []) = ts) := by
  constructor
  · exact deBruijnSubstNothingType
  · intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih => simp [deBruijnSubstNothingType t, ih]

end Flapjack.Compiler.Inference.InferProps
