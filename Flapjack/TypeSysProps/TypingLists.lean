module

public import Flapjack.TypeSystemHOL.Expressions
public import Batteries.Data.List.Basic

@[expose] public section

/-! Source typing preserves the shape of function and expression lists. -/
namespace Flapjack.TypeSysProps
open Flapjack.Basis.Pure.MlString Flapjack.TypeSystemHOL Flapjack.AstHOL

/-- The names in a typed function list equal those in its output bindings. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_funs_MAP_FST"]
theorem typeFunsMapFst (funs : List (MlString × MlString × Flapjack.AstHOL.Exp)) (env : TypeEnv)
    (localEnv : TenvValExp) (bindings : List (MlString × SemanticT)) :
    TypeFuns env localEnv funs bindings → funs.map Prod.fst = bindings.map Prod.fst := by
  induction funs generalizing env localEnv bindings with
  | nil =>
    intro typed
    cases typed
    rfl
  | cons fn funs ih =>
    intro typed
    cases typed <;> simp_all <;> apply ih <;> assumption

/-- A typed expression list and its type list have equal lengths. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_es_length"]
theorem typeEsLength (env : TypeEnv) (localEnv : TenvValExp) (es : List Flapjack.AstHOL.Exp)
    (types : List SemanticT) : TypeEs env localEnv es types → es.length = types.length := by
  induction es generalizing env localEnv types with
  | nil => intro typed; cases typed; rfl
  | cons e es ih =>
    intro typed
    cases typed <;> simp_all <;> apply ih <;> assumption

/-- The source `type_pes` definition: every pattern/expression pair in the
list binds distinct names, types its pattern at the first type and its
expression at the second type under the extended local environment. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_pes_def"]
def typePes (tvs tvs' : Nat) (env : TypeEnv) (localEnv : TenvValExp)
    (pes : List (Pat × Flapjack.AstHOL.Exp)) (t₁ t₂ : SemanticT) : Prop :=
  ∀ (p : Pat) (e : Flapjack.AstHOL.Exp), (p, e) ∈ pes →
    ∃ bindings : List (MlString × SemanticT),
      (patBindings p).Nodup ∧ TypeP tvs env p t₁ bindings ∧
        TypeE env (bindVarList tvs' bindings localEnv) e t₂

/-- The inductive expression-list judgment is exactly HOL's `LIST_REL` of the
single-expression judgment. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_es_list_rel"]
theorem typeEsListRel (es : List Flapjack.AstHOL.Exp) (types : List SemanticT) (env : TypeEnv)
    (localEnv : TenvValExp) :
    TypeEs env localEnv es types ↔ List.Forall₂ (TypeE env localEnv) es types := by
  induction es generalizing types env localEnv with
  | nil =>
    cases types with
    | nil => exact ⟨fun _ => List.Forall₂.nil, fun _ => TypeEs.nil env localEnv⟩
    | cons t ts =>
      refine ⟨?_, ?_⟩
      · intro h
        cases h
      · intro h
        cases h
  | cons e es ih =>
    cases types with
    | nil =>
      refine ⟨?_, ?_⟩
      · intro h
        cases h
      · intro h
        cases h
    | cons t ts =>
      constructor
      · intro h
        cases h
        exact List.Forall₂.cons ‹TypeE env localEnv e t›
          ((ih ts env localEnv).mp ‹TypeEs env localEnv es ts›)
      · intro h
        cases h with
        | cons head tail =>
          exact TypeEs.cons env localEnv e es t ts head ((ih ts env localEnv).mpr tail)

end Flapjack.TypeSysProps

