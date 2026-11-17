module

public import Flapjack.TypeSystemHOL.Expressions

@[expose] public section

/-! Source typing preserves the shape of function and expression lists. -/
namespace Flapjack.TypeSysProps
open Flapjack.Basis.Pure.MlString Flapjack.TypeSystemHOL

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

end Flapjack.TypeSysProps
