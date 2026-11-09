module

public import Flapjack.SemanticPrimitivesHOL.ConversionCorrespondence
public import Flapjack.SemanticPrimitivesHOL.ArithmeticCorrespondence

@[expose] public section

/-! Source primitive application dispatcher. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Source primitive application. The `doAppBasic` and numeric cases together
cover the original dispatch; `opapp` and `eval` are handled by the evaluator
and return `none` here, as in HOL. Floating-point behavior inherits the
rational-cut assumption used by `doArith` and `doTest`. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_app_def"]
noncomputable def doApp {σ : Type} (state : Store Value × HolFfiState σ) (op : Op)
    (values : List Value) : Option (BasicAppResult σ) :=
  match op with
  | .arith action typ =>
    if values.all (checkType typ) then
      (doArith action typ values).map (fun result =>
        match result with
        | .inl error => (state, .err (.raise error))
        | .inr value => (state, .val value))
    else none
  | .fromTo source target => match values with
    | [v] =>
      if checkType source v then
        (doConversion v source target).map (fun result =>
          match result with
          | .inl error => (state, .err (.raise error))
          | .inr value => (state, .val value))
      else none
    | _ => none
  | .test test typ => match values with
    | [first, second] => match doTest test typ first second with
      | .typeError => none
      | .val b => some (state, .val (boolValue b))
    | _ => none
  | _ => match doAppNumericCore state op values with
    | some result => result
    | none => (doAppBasic state op values).getD none

/-- Guarded HOL arithmetic agrees with the computable non-float dispatcher;
the float case retains the HOL expression. This Flapjack correspondence lemma
has no separate HOL declaration. -/
theorem doApp_arith_core {σ : Type} (state : Store Value × HolFfiState σ)
    (action : Arith) (typ : PrimType) (values : List Value) :
    doApp state (.arith action typ) values =
      (match typ with
       | .float64T =>
         if values.all (checkType .float64T) then
           (doArith action .float64T values).map (fun result =>
             match result with
             | .inl error => (state, .err (.raise error))
             | .inr value => (state, .val value))
         else none
       | _ => (doAppNumericCore state (.arith action typ) values).getD none) := by
  exact doAppArithCore state action typ values

/-- The guarded HOL conversion agrees with the executable dispatcher. This
Flapjack correspondence lemma has no separate HOL declaration. -/
theorem doApp_fromTo_core {σ : Type} (state : Store Value × HolFfiState σ)
    (source target : PrimType) (values : List Value) :
    doApp state (.fromTo source target) values =
      (doAppNumericCore state (.fromTo source target) values).getD none := by
  cases values with
  | nil =>
    cases source <;> cases target <;> simp [doApp, doAppNumericCore]
  | cons v rest =>
    cases rest with
    | nil =>
      rw [doAppNumericCore_fromTo]
      rfl
    | cons second rest =>
      cases source <;> cases target <;> simp [doApp, doAppNumericCore]

end Flapjack.SemanticPrimitivesHOL
