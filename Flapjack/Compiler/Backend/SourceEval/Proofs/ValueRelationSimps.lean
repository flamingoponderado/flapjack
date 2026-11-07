import Flapjack.Compiler.Backend.SourceEval.Proofs.ValueRelation

/-! Source-shaped simplifications for the recorded value relation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- All seven left-constructor cases of the value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel_l_simps"]
theorem valueRel_leftSimps :
    (∀ (v : Value) (l : Lit) (es : EvalOracleState), ValueRel es (.litv l) v ↔ v = .litv l) ∧
    (∀ (vs : List Value) (v : Value) (es : EvalOracleState) (cn : Option Stamp),
      ValueRel es (.conv cn vs) v ↔ ∃ ys, v = .conv cn ys ∧ List.Forall₂ (ValueRel es) vs ys) ∧
    (∀ (v : Value) (l : Nat) (es : EvalOracleState) (b : Bool), ValueRel es (.loc b l) v ↔ v = .loc b l) ∧
    (∀ (vs : List Value) (v : Value) (es : EvalOracleState),
      ValueRel es (.vectorv vs) v ↔ ∃ ys, v = .vectorv ys ∧ List.Forall₂ (ValueRel es) vs ys) ∧
    (∀ (v : Value) (id : Nat × Nat) (es : EvalOracleState) (env : SemEnv Value),
      ValueRel es (.env env id) v ↔ ∃ env', valueToEnvId v = some id ∧
        lookupEnv es id = some env' ∧ envRel (ValueRel es) env env') ∧
    (∀ (v : Value) (name : VarN) (funs : List (VarN × VarN × AstHOL.Exp))
      (es : EvalOracleState) (env : SemEnv Value),
      ValueRel es (.recclosure env funs name) v ↔ ∃ env', v = .recclosure env' funs name ∧
        envRel (ValueRel es) env env') ∧
    (∀ (body : AstHOL.Exp) (v : Value) (name : VarN) (es : EvalOracleState) (env : SemEnv Value),
      ValueRel es (.closure env name body) v ↔ ∃ env', v = .closure env' name body ∧
        envRel (ValueRel es) env env') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v l es
    constructor
    · intro h; cases h; rfl
    · intro h; subst v; exact .lit l
  · intro vs v es cn
    constructor
    · intro h; cases h with | con values => exact ⟨_, rfl, values⟩
    · rintro ⟨ys, rfl, related⟩; exact .con related
  · intro v l es b
    constructor
    · intro h; cases h; rfl
    · intro h; subst v; exact .loc b l
  · intro vs v es
    constructor
    · intro h; cases h with | vector values => exact ⟨_, rfl, values⟩
    · rintro ⟨ys, rfl, related⟩; exact .vector related
  · intro v id es env
    constructor
    · intro h; cases h with | env decoded lookup related =>
        exact ⟨_, decoded, lookup, (valueEnvRel_iff _ _ _).mp related⟩
    · rintro ⟨env', decoded, lookup, related⟩
      exact .env decoded lookup ((valueEnvRel_iff _ _ _).mpr related)
  · intro v name funs es env
    constructor
    · intro h; cases h with | recclosure related =>
        exact ⟨_, rfl, (valueEnvRel_iff _ _ _).mp related⟩
    · rintro ⟨env', rfl, related⟩; exact .recclosure ((valueEnvRel_iff _ _ _).mpr related)
  · intro body v name es env
    constructor
    · intro h; cases h with | closure related =>
        exact ⟨_, rfl, (valueEnvRel_iff _ _ _).mp related⟩
    · rintro ⟨env', rfl, related⟩; exact .closure ((valueEnvRel_iff _ _ _).mpr related)

/-- A Boolean value relates only to itself. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "v_rel_Boolv"]
theorem valueRel_bool (es : EvalOracleState) (b : Bool) (v : Value) :
    ValueRel es (boolValue b) v ↔ v = boolValue b := by
  constructor
  · intro related
    unfold boolValue at related ⊢
    cases related with
    | con values => cases values; rfl
  · intro equal
    subst v
    exact .con .nil
end Flapjack.Compiler.Backend.SourceEval.Proofs
