module

public import Flapjack.AstHOL.Syntax
public import Flapjack.Compiler.Inference.Infer.Duplicates
public import Flapjack.Compiler.Inference.Infer.TypeNameCheck

@[expose] public section

/-! Source checks for mutually recursive type definitions. -/
namespace Flapjack.Compiler.Inference.Infer.TypeDefinitions
open Flapjack.AstHOL Flapjack.TypeSystemHOL Flapjack.Misc.Location
  Flapjack.Basis.Pure.MlString Flapjack.Translator.Monadic.MonadBase
  Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Compiler.Inference.Infer.Duplicates
  Flapjack.Compiler.Inference.Infer.TypeNameCheck

/-- Check the constructor argument types in source order. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "check_ctor_types_def"]
def checkCtorTypes {state : Type} (l : LocErrInfo) (env : TenvAbbrev) (tvs : List MlString) :
    List (MlString × List AstT) → M state Unit (Option Locs × MlString)
  | [] => ret ()
  | (name, ts) :: ctors =>
    ignoreBind (typeNameCheckSubstList l
      (fun tv => MlString.concat [ofString "Unbound type variable ", tv,
        ofString " in type definition with constructor ", name]) env tvs ts)
      (checkCtorTypes l env tvs ctors)

/-- Check the constructors and type parameters in each source definition. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "check_ctors_def"]
def checkCtors {state : Type} (l : LocErrInfo) (env : TenvAbbrev) :
    TypeDef → M state Unit (Option Locs × MlString)
  | [] => ret ()
  | (tvs, name, ctors) :: defs =>
    ignoreBind (checkDupsExec l (fun n => MlString.concat [ofString "Duplicate constructor ", n,
      ofString " in the definition of type ", name]) (ctors.map Prod.fst))
      (ignoreBind (checkDupsExec l (fun n => MlString.concat [ofString "Duplicate type variable binding ", n,
        ofString " in the definition of type ", name]) tvs)
        (ignoreBind (checkCtorTypes l env tvs ctors) (checkCtors l env defs)))

/-- Check duplicate type names before checking the definitions themselves. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "check_type_definition_def"]
def checkTypeDefinition {state : Type} (l : LocErrInfo) (env : TenvAbbrev)
    (defs : TypeDef) : M state Unit (Option Locs × MlString) :=
  ignoreBind (checkDupsExec l (fun n => MlString.concat [ofString "Duplicate type constructor ", n,
    ofString " in a mutually recursive type definition"]) (defs.map (fun (_, n, _) => n)))
    (checkCtors l env defs)

end Flapjack.Compiler.Inference.Infer.TypeDefinitions
