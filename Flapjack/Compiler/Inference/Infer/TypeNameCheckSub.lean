module

public import Flapjack.Compiler.Inference.Infer.TypeNameCheck

@[expose] public section

/-! Structured-error form of source type-name checking. -/
namespace Flapjack.Compiler.Inference.Infer.TypeNameCheck
open Flapjack.AstHOL Flapjack.TypeSystemHOL Flapjack.NamespaceHOL
  Flapjack.Basis.Pure.MlString Flapjack.Misc.Location
  Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Compiler.Inference.InferTDisplay
  Flapjack.Translator.Monadic.MonadBase

mutual
/-- Check source type names while retaining the unbound variable separately. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "type_name_check_sub_def"]
def typeNameCheckSub {state : Type} (l : LocErrInfo) (env : TenvAbbrev)
    (fvs : List MlString) : AstT → M state SemanticT (Option Locs × Sum MlString MlString)
  | .atvar tv => fun s =>
    if tv ∈ fvs then (.success (.var tv), s) else (.failure (l.loc, .inr tv), s)
  | .attup ts => bind (typeNameCheckSubList l env fvs ts) (fun ts' => ret (Ttup ts'))
  | .atfun a b => bind (typeNameCheckSub l env fvs a) (fun a' =>
      bind (typeNameCheckSub l env fvs b) (fun b' => ret (Tfn a' b')))
  | .atapp ts tc => bind (typeNameCheckSubList l env fvs ts) (fun ts' => fun s =>
    match nsLookup env tc with
    | none => (.failure (l.loc, .inl (MlString.concat [ofString "Undefined ",
        ofString "type constructor", ofString ": ", idToString tc])), s)
    | some (tvs, body) =>
      if tvs.length = ts.length then (.success (typeSubst (typeSubstMap (tvs.zip ts')) body), s)
      else (.failure (l.loc, .inl (MlString.concat [ofString "Type constructor ", idToString tc,
        ofString " given ", .implode (Flapjack.holNumToDecString ts.length),
        ofString " arguments, but expected ", .implode (Flapjack.holNumToDecString tvs.length)])), s))
termination_by t => sizeOf t

/-- List companion to the source structured-error check. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "type_name_check_sub_def"]
def typeNameCheckSubList {state : Type} (l : LocErrInfo) (env : TenvAbbrev)
    (fvs : List MlString) : List AstT → M state (List SemanticT) (Option Locs × Sum MlString MlString)
  | [] => ret []
  | t :: ts => bind (typeNameCheckSub l env fvs t) (fun t' =>
      bind (typeNameCheckSubList l env fvs ts) (fun ts' => ret (t' :: ts')))
termination_by ts => sizeOf ts
end

end Flapjack.Compiler.Inference.Infer.TypeNameCheck
