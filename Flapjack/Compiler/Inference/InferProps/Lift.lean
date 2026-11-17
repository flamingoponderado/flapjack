module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.NamespaceProps.LiftLookup

@[expose] public section

/-! Well-formed inference environments remain so when lifted into a module. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference.Infer Flapjack.NamespaceHOL
  Flapjack.TypeSoundInvariants Flapjack.Basis.Pure.MlString

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "ienv_ok_lift"]
theorem ienvOkLift (mn : MlString) (ienv : Env) (n : Nat → Prop)
    (h : ienvOk n ienv) : ienvOk n (liftIenv mn ienv) := by
  simpa [ienvOk, liftIenv, ienvValOk, tenvCtorOk, tenvAbbrevOk, nsAll_nsLift] using h

end Flapjack.Compiler.Inference.InferProps
