module

public import Flapjack.PrimTypesHOL

@[expose] public section

/-! The primitive source environment used to initialize the semantics. -/
namespace Flapjack.PrimSemEnv
open Flapjack Flapjack.PrimTypesHOL Flapjack.SemanticPrimitivesHOL
  Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString

/-- Evaluating the primitive declarations constructs the original exception,
boolean and list constructors, preserving the supplied FFI state. The evaluator
dependency inherits the real-number model assumption in SOUNDNESS item 8. -/
@[hol "cakeml/semantics/proofs/primSemEnvScript.sml" "prim_sem_env_eq"]
theorem primSemEnvEq {σ : Type} (ffi : HolFfiState σ) :
    primSemEnv ffi = some
      ({ clock := 0, refs := [], ffi := ffi, nextTypeStamp := 2,
         nextExnStamp := 4, evalState := none },
       { v := .bind [] [],
         c := .bind [
           (ofString "::", (2, .typeStamp (ofString "::") 1)),
           (ofString "[]", (0, .typeStamp (ofString "[]") 1)),
           (ofString "True", (0, .typeStamp (ofString "True") 0)),
           (ofString "False", (0, .typeStamp (ofString "False") 0)),
           (ofString "Subscript", (0, .exnStamp 3)),
           (ofString "Div", (0, .exnStamp 2)),
           (ofString "Chr", (0, .exnStamp 1)),
           (ofString "Bind", (0, .exnStamp 0))] [] }) := by
  have boolNames : ofString "False" ≠ ofString "True" := by decide
  have listNames : ofString "[]" ≠ ofString "::" := by decide
  simp [primSemEnv, addToSemEnv, primTypesProgram, EvaluateHOL.evaluateDecs,
    EvaluateHOL.fixClock, extendDecEnv, combineDecResult, checkDupCtors, buildTdefs,
    buildConstrs, nsSing, nsAppend, nsEmpty, alistToNs, boolNames, listNames]

end Flapjack.PrimSemEnv
