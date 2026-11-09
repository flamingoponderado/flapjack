import Flapjack.AstHOL.Syntax
import Flapjack.EvaluateHOL.Definition

/-!
# `primTypesScript`: the primitive-types program

Counterpart of `cakeml/semantics/primTypesScript.sml`'s `prim_types_program_def`
(lines 12-22), the declarations in scope before any CakeML program: the
exceptions `Bind`, `Chr`, `Div`, `Subscript` and the datatypes `bool` and
`'a list`. HOL's mlstring literal `«s»` is `MlString.ofString "s"` (ASCII, so the
byte list is exactly HOL's `implode`d character list), `unknown_loc` is
`Misc.Location.unknownLoc` and `Short` is `NamespaceHOL.Ident.short`.
-/

namespace Flapjack.PrimTypesHOL

open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Misc.Location
open Flapjack.Basis.Pure.MlString

/-- Exact HOL `prim_types_program_def` (`primTypesScript.sml:12-22`). -/
@[hol "cakeml/semantics/primTypesScript.sml" "prim_types_program_def"]
def primTypesProgram : List Dec :=
  [.dexn unknownLoc (ofString "Bind") [],
   .dexn unknownLoc (ofString "Chr") [],
   .dexn unknownLoc (ofString "Div") [],
   .dexn unknownLoc (ofString "Subscript") [],
   .dtype unknownLoc [([], ofString "bool",
     [(ofString "False", []), (ofString "True", [])])],
   .dtype unknownLoc
     [([ofString "'a"], ofString "list",
       [(ofString "[]", []),
        (ofString "::", [.atvar (ofString "'a"),
          .atapp [.atvar (ofString "'a")] (.short (ofString "list"))])])]]

/-- Evaluate declarations and extend the semantic environment on success.
The source evaluator and its carriers are pending complete source review. -/
@[hol "cakeml/semantics/primTypesScript.sml" "add_to_sem_env_def"]
noncomputable def addToSemEnv {σ : Type}
    (initial : SemanticPrimitivesHOL.State σ × SemanticPrimitivesHOL.SemEnv SemanticPrimitivesHOL.Value)
    (prog : List Dec) : Option (SemanticPrimitivesHOL.State σ × SemanticPrimitivesHOL.SemEnv SemanticPrimitivesHOL.Value) :=
  match EvaluateHOL.evaluateDecs initial.1 initial.2 prog with
  | (st, .val env) => some (st, SemanticPrimitivesHOL.extendDecEnv env initial.2)
  | (_, .err _) => none

/-- Build the primitive semantic environment from the initial FFI state.
This inherits the evaluator's pending source review and floating-point assumption. -/
@[hol "cakeml/semantics/primTypesScript.sml" "prim_sem_env_def"]
noncomputable def primSemEnv {σ : Type} (ffi : HolFfiState σ) :
    Option (SemanticPrimitivesHOL.State σ × SemanticPrimitivesHOL.SemEnv SemanticPrimitivesHOL.Value) :=
  addToSemEnv ({ clock := 0, refs := [], ffi := ffi, nextTypeStamp := 0, nextExnStamp := 0, evalState := none }, { v := nsEmpty, c := nsEmpty }) primTypesProgram

end Flapjack.PrimTypesHOL
