module

public import Flapjack.AstHOL.Syntax
public import Flapjack.Compiler.Inference.Infer.Constraint
public import Flapjack.Compiler.Inference.Infer.TypeNameCheck

@[expose] public section

/-! Source-shaped pattern inference. -/
namespace Flapjack.Compiler.Inference.Infer.Pattern
open Flapjack.AstHOL Flapjack.TypeSystemHOL Flapjack.NamespaceHOL
  Flapjack.Basis.Pure.MlString Flapjack.Misc.Location
  Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Compiler.Inference.Infer.HOLState
  Flapjack.Compiler.Inference.Infer.Constraint
  Flapjack.Compiler.Inference.Infer.TypeNameCheck
  Flapjack.Compiler.Inference.InferTDisplay
  Flapjack.Translator.Monadic.MonadBase

abbrev PatternBindings := List (MlString × InferT)
abbrev PatternM (α : Type) := M InferState α (Option Locs × MlString)

mutual
/-- The complete source-shaped pattern algorithm, including source errors and
    state threading. This is not tagged as `infer_p_def`: its constraint
    operation still uses unreviewed unifier and normalizer choices for
    ill-formed substitutions, so exact HOL correspondence is not established. -/
noncomputable def inferPatternModel (l : LocErrInfo) (env : Env) :
    Pat → PatternM (InferT × PatternBindings)
  | .pvar name => bind HOLState.freshUvar (fun t => ret (t, [(name, t)]))
  | .pany => bind HOLState.freshUvar (fun t => ret (t, []))
  | .plit (.intLit _) => ret (.app [] 5, [])
  | .plit (.char _) => ret (.app [] 2, [])
  | .plit (.strLit _) => ret (.app [] 8, [])
  | .plit (.word8 _) => ret (.app [] 12, [])
  | .plit (.word64 _) => ret (.app [] 11, [])
  | .plit (.float64 _) => failwith l (ofString "Floats cannot be used in patterns")
  | .pcon none ps => bind (inferPatternsModel l env ps) (fun (ts, bindings) =>
      ret (.app ts 9, bindings))
  | .pcon (some name) ps =>
    bind (lookupStEx l (ofString "constructor") name env.infC) (fun (tvs, expected, tid) =>
      bind (inferPatternsModel l env ps) (fun (actual, bindings) =>
        bind (HOLState.freshUvars tvs.length) (fun fresh =>
          ignoreBind (guard (decide (actual.length = expected.length)) l
            (MlString.concat [ofString "Constructor ", idToString name, ofString " given ",
              .implode (Flapjack.holNumToDecString actual.length), ofString " arguments, but expected ",
              .implode (Flapjack.holNumToDecString expected.length)]))
            (ignoreBind (addConstraintsModel l actual (expected.map (inferTypeSubst (tvs.zip fresh))))
              (ret (.app fresh tid, bindings))))))
  | .pref p => bind (inferPatternModel l env p) (fun (t, bindings) => ret (.app [t] 7, bindings))
  | .pas p name => bind (inferPatternModel l env p) (fun (t, bindings) => ret (t, bindings ++ [(name, t)]))
  | .ptannot p typ => bind (inferPatternModel l env p) (fun (t, bindings) =>
      bind (typeNameCheckSubst l (fun tv => MlString.concat [ofString "Type variable ", tv,
        ofString " found in type annotation. ", ofString "Type variables are not supported in type annotations."])
        env.infT [] typ) (fun typ' =>
          ignoreBind (addConstraintModel l t (inferTypeSubst [] typ')) (ret (t, bindings))))
termination_by p => sizeOf p

/-- Source-shaped list traversal for pattern inference, with the same
    unreviewed constraint-choice limitation as `inferPatternModel`. -/
noncomputable def inferPatternsModel (l : LocErrInfo) (env : Env) :
    List Pat → PatternM (List InferT × PatternBindings)
  | [] => ret ([], [])
  | p :: ps => bind (inferPatternModel l env p) (fun (t, bindings) =>
      bind (inferPatternsModel l env ps) (fun (ts, rest) => ret (t :: ts, rest ++ bindings)))
termination_by ps => sizeOf ps
end

end Flapjack.Compiler.Inference.Infer.Pattern
