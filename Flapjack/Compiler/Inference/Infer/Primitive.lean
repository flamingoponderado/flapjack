module

public import Flapjack.Compiler.Inference.Infer.Constraint

@[expose] public section

/-! Source-shaped primitive constraints for the inference correctness proof. -/
namespace Flapjack.Compiler.Inference.Infer.Primitive
open Flapjack.AstHOL Flapjack.Misc.Location Flapjack.Basis.Pure.MlString
  Flapjack.Compiler.Inference.Infer.Operations
  Flapjack.Compiler.Inference.Infer.HOLState
  Flapjack.Compiler.Inference.Infer.Constraint
  Flapjack.Translator.Monadic.MonadBase

/-- The source primitive case structure and state sequencing. Diagnostic and
    unifier correspondence is not established for ill-formed substitutions:
    the constraint operation uses unreviewed unifier and normalizer choices
    there. This is therefore not tagged as `constrain_op_def`. -/
noncomputable def constrainOpModel (l : LocErrInfo) (op : Op) (ts : List InferT) :
    M InferState InferT (Option Locs × MlString) :=
  let (simple, args, result) := Core.opSimpleConstraints op
  if simple then
    if ts.length != args.length then failwith l (Core.opNArgsMessage op ts.length)
    else ignoreBind (addConstraintsModel l ts args) (ret result)
  else
    match op, ts with
    | .equality, [a, b] =>
      ignoreBind (addConstraintModel l a b) (ret (.app [] 1))
    | .opapp, [f, x] => bind HOLState.freshUvar (fun r =>
      ignoreBind (addConstraintModel l f (.app [x, r] 4)) (ret r))
    | .opassign, [a, b] =>
      ignoreBind (addConstraintModel l a (.app [b] 7)) (ret (.app [] 9))
    | .opref, [a] => ret (.app [a] 7)
    | .opderef, [a] => bind HOLState.freshUvar (fun r =>
      ignoreBind (addConstraintModel l a (.app [r] 7)) (ret r))
    | .vfromList, [a] => bind HOLState.freshUvar (fun r =>
      ignoreBind (addConstraintModel l a (.app [r] 6)) (ret (.app [r] 10)))
    | .vsub, [a, b] => bind HOLState.freshUvar (fun r =>
      ignoreBind (addConstraintModel l a (.app [r] 10))
        (ignoreBind (addConstraintModel l b (.app [] 5)) (ret r)))
    | .vlength, [a] => bind HOLState.freshUvar (fun r =>
      ignoreBind (addConstraintModel l a (.app [r] 10)) (ret (.app [] 5)))
    | .aalloc, [a, b] =>
      ignoreBind (addConstraintModel l a (.app [] 5)) (ret (.app [b] 0))
    | .aallocEmpty, [a] => bind HOLState.freshUvar (fun r =>
      ignoreBind (addConstraintModel l a (.app [] 9)) (ret (.app [r] 0)))
    | .asub, [a, b] => bind HOLState.freshUvar (fun r =>
      ignoreBind (addConstraintModel l a (.app [r] 0))
        (ignoreBind (addConstraintModel l b (.app [] 5)) (ret r)))
    | .alength, [a] => bind HOLState.freshUvar (fun r =>
      ignoreBind (addConstraintModel l a (.app [r] 0)) (ret (.app [] 5)))
    | .aupdate, [a, b, c] =>
      ignoreBind (addConstraintModel l a (.app [c] 0))
        (ignoreBind (addConstraintModel l b (.app [] 5)) (ret (.app [] 9)))
    | .listAppend, [a, b] => bind HOLState.freshUvar (fun r =>
      ignoreBind (addConstraintModel l a (.app [r] 6))
        (ignoreBind (addConstraintModel l b (.app [r] 6)) (ret (.app [r] 6))))
    | .vsubUnsafe, _ | .asubUnsafe, _ | .aupdateUnsafe, _ | .aw8subUnsafe, _
    | .aw8updateUnsafe, _ | .xorAw8StrUnsafe, _ | .aallocFixed, _ | .eval, _ | .envId, _ =>
      failwith l (ofString "Unsafe ops do not have a type")
    | .thunkOp _, _ => failwith l (ofString "Thunk ops do not have a type")
    | .arith _ _, _ | .fromTo _ _, _ | .test _ _, _ => failwith l (ofString "Type mismatch")
    | _, _ => failwith l (Core.opNArgsMessage op ts.length)

end Flapjack.Compiler.Inference.Infer.Primitive
