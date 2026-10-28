import Flapjack.Compiler.Backend.FlatElim.Reachability
import Flapjack.Compiler.Backend.Semantics.FlatSem

/-! Global dependencies stored in flat-language values. -/
namespace Flapjack.Compiler.Backend.FlatElim

mutual
/-- Global slots referenced by a flat value, including captured environments
and recursive function bodies. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globals_def"]
def findValueGlobals : FlatSem.Value → NumSet
  | .conv _ values => findValuesGlobals values
  | .closure ⟨bindings⟩ _ body => sptUnion (findBindingsGlobals bindings) (findLookups body)
  | .recclosure ⟨bindings⟩ funs _ => sptUnion (findBindingsGlobals bindings) (findGlobalsFuns destGlobalVarLookup funs)
  | .vectorv values => findValuesGlobals values
  | _ => .ln
termination_by value => sizeOf value

/-- List clause of the value-global analysis. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_v_globals_def"]
def findValuesGlobals : List FlatSem.Value → NumSet
  | [] => .ln
  | value :: rest => sptUnion (findValueGlobals value) (findValuesGlobals rest)
termination_by values => sizeOf values

/-- Traverse captured bindings without allocating an intermediate value list. -/
def findBindingsGlobals : List (Flapjack.AstHOL.VarN × FlatSem.Value) → NumSet
  | [] => .ln
  | (_, value) :: rest => sptUnion (findValueGlobals value) (findBindingsGlobals rest)
termination_by bindings => sizeOf bindings
end

/-- Captured-binding traversal agrees with the original mapped value list. -/
theorem findBindingsGlobals_eq_map (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) :
    findBindingsGlobals bindings = findValuesGlobals (bindings.map Prod.snd) := by
  induction bindings with
  | nil => simp [findBindingsGlobals, findValuesGlobals]
  | cons binding rest ih =>
    cases binding
    simp [findBindingsGlobals, findValuesGlobals, ih]

/-- Recursive-function traversal agrees with the original mapped body list. -/
theorem findFunctionGlobals_eq_map (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    findGlobalsFuns destGlobalVarLookup funs =
      findGlobalsList destGlobalVarLookup (funs.map (fun (_, _, body) => body)) := by
  induction funs with
  | nil => simp [findGlobalsFuns, findGlobalsList]
  | cons funSpec rest ih =>
    obtain ⟨_, _, _⟩ := funSpec
    simp [findGlobalsFuns, findGlobalsList, ih]

/-- Global dependencies reachable from all reference-store values. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_refs_globals_def"]
def findRefsGlobals : List (Flapjack.SemanticPrimitivesHOL.StoreValue FlatSem.Value) → NumSet
  | [] => .ln
  | .refv value :: rest => sptUnion (findValueGlobals value) (findRefsGlobals rest)
  | .varray values :: rest => sptUnion (findValuesGlobals values) (findRefsGlobals rest)
  | .thunk _ value :: rest => sptUnion (findValueGlobals value) (findRefsGlobals rest)
  | _ :: rest => findRefsGlobals rest

/-- Global dependencies in a flat local environment. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_env_globals_def"]
def findEnvGlobals (env : FlatSem.Environment FlatSem.Value) : NumSet :=
  findValuesGlobals (env.v.map Prod.snd)

/-- Global dependencies in a raised flat result. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_result_globals_def"]
def findResultGlobals : Option (Flapjack.SemanticPrimitivesHOL.ErrorResult FlatSem.Value) → NumSet
  | some (.raise value) => findValueGlobals value
  | _ => .ln

/-- Global dependencies in a primitive result, including successful values. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "find_sem_prim_res_globals_def"]
def findPrimitiveResultGlobals : Flapjack.SemanticPrimitivesHOL.Result (List FlatSem.Value) FlatSem.Value → NumSet
  | .err error => findResultGlobals (some error)
  | .val values => findValuesGlobals values

mutual
/-- Whether a flat value or a captured value contains dynamic Eval. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "v_has_Eval_def1"]
def valueHasEval : FlatSem.Value → Bool
  | .conv _ values => valuesHaveEval values
  | .closure ⟨bindings⟩ _ body => hasEval body || bindingsHaveEval bindings
  | .recclosure ⟨bindings⟩ funs _ => bindingsHaveEval bindings || hasEvalFuns funs
  | .vectorv values => valuesHaveEval values
  | _ => false
termination_by value => sizeOf value

/-- Existential value-list traversal used by `valueHasEval`. -/
def valuesHaveEval : List FlatSem.Value → Bool
  | [] => false
  | value :: rest => valueHasEval value || valuesHaveEval rest
termination_by values => sizeOf values

/-- Existential captured-binding traversal used by `valueHasEval`. -/
def bindingsHaveEval : List (Flapjack.AstHOL.VarN × FlatSem.Value) → Bool
  | [] => false
  | (_, value) :: rest => valueHasEval value || bindingsHaveEval rest
termination_by bindings => sizeOf bindings
end

/-- The binding helper is the original mapped existential value test. -/
theorem bindingsHaveEval_eq_map (bindings : List (Flapjack.AstHOL.VarN × FlatSem.Value)) :
    bindingsHaveEval bindings = valuesHaveEval (bindings.map Prod.snd) := by
  induction bindings with
  | nil => simp [bindingsHaveEval, valuesHaveEval]
  | cons binding rest ih =>
    cases binding
    simp [bindingsHaveEval, valuesHaveEval, ih]

/-- The recursive-function helper is the original mapped body test. -/
theorem hasEvalFuns_eq_map (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    hasEvalFuns funs = (funs.map (fun (_, _, body) => body)).any hasEval := by
  induction funs with
  | nil => simp [hasEvalFuns]
  | cons funSpec rest ih =>
    obtain ⟨_, _, _⟩ := funSpec
    simp [hasEvalFuns, ih]

end Flapjack.Compiler.Backend.FlatElim
