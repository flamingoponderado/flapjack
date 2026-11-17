module

public import Flapjack.Compiler.Inference.Infer.Operations
public import Flapjack.TypeSystemHOL.TypeNames
public import Flapjack.Misc.ASCIInumbers

@[expose] public section

/-! Source inference checks for names in type annotations. -/
namespace Flapjack.Compiler.Inference.Infer.TypeNameCheck
open Flapjack.AstHOL Flapjack.TypeSystemHOL Flapjack.NamespaceHOL
  Flapjack.Basis.Pure.MlString Flapjack.Misc.Location
  Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Compiler.Inference.InferTDisplay
  Flapjack.Translator.Monadic.MonadBase

mutual
/-- Check names in a source type annotation, preserving the first error. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "type_name_check_subst_def"]
def typeNameCheckSubst {state : Type} (l : LocErrInfo) (f : MlString → MlString)
    (env : TenvAbbrev) (fvs : List MlString) : AstT → M state SemanticT (Option Locs × MlString)
  | .atvar tv =>
    ignoreBind (guard (decide (tv ∈ fvs)) l (f tv)) (ret (.var tv))
  | .attup ts => bind (typeNameCheckSubstList l f env fvs ts) (fun ts' => ret (Ttup ts'))
  | .atfun a b => bind (typeNameCheckSubst l f env fvs a) (fun a' =>
      bind (typeNameCheckSubst l f env fvs b) (fun b' => ret (Tfn a' b')))
  | .atapp ts tc => bind (typeNameCheckSubstList l f env fvs ts) (fun ts' =>
      bind (lookupStEx l (ofString "type constructor") tc env) (fun (tvs, body) =>
        ignoreBind (guard (decide (tvs.length = ts.length)) l
          (MlString.concat [ofString "Type constructor ", idToString tc,
            ofString " given ", .implode (Flapjack.holNumToDecString ts.length),
            ofString " arguments, but expected ", .implode (Flapjack.holNumToDecString tvs.length)]))
          (ret (typeSubst (typeSubstMap (tvs.zip ts')) body))))
termination_by t => sizeOf t

/-- List companion for `typeNameCheckSubst`. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "type_name_check_subst_def"]
def typeNameCheckSubstList {state : Type} (l : LocErrInfo) (f : MlString → MlString)
    (env : TenvAbbrev) (fvs : List MlString) : List AstT → M state (List SemanticT) (Option Locs × MlString)
  | [] => ret []
  | t :: ts => bind (typeNameCheckSubst l f env fvs t) (fun t' =>
      bind (typeNameCheckSubstList l f env fvs ts) (fun ts' => ret (t' :: ts')))
termination_by ts => sizeOf ts
end

end Flapjack.Compiler.Inference.Infer.TypeNameCheck
