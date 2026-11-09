import Flapjack.SemanticPrimitivesHOL.ApplyNumericCore
import Flapjack.SemanticPrimitivesHOL.ConversionCorrespondence

/-! Source primitive floating arithmetic and the assembled application dispatcher. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Floating arithmetic dispatcher used by `doApp`; this helper is not a
separate HOL declaration. -/
noncomputable def floatArith (action : Arith) (values : List Value) : Option Value :=
  match action, values with
  | .abs, [.litv (.float64 x)] => some (.litv (.float64 (fpSemFpUopComp .abs x)))
  | .neg, [.litv (.float64 x)] => some (.litv (.float64 (fpSemFpUopComp .neg x)))
  | .sqrt, [.litv (.float64 x)] => some (.litv (.float64 (fpSemFpUopComp .sqrt x)))
  | .add, [.litv (.float64 x), .litv (.float64 y)] => some (.litv (.float64 (fpSemFpBopComp .add x y)))
  | .sub, [.litv (.float64 x), .litv (.float64 y)] => some (.litv (.float64 (fpSemFpBopComp .sub x y)))
  | .mul, [.litv (.float64 x), .litv (.float64 y)] => some (.litv (.float64 (fpSemFpBopComp .mul x y)))
  | .div, [.litv (.float64 x), .litv (.float64 y)] => some (.litv (.float64 (fpSemFpBopComp .div x y)))
  | .fma, [.litv (.float64 x), .litv (.float64 y), .litv (.float64 z)] => some (.litv (.float64 (fpSemFpfma x y z)))
  | _, _ => none

/-- Source primitive application. The `doAppBasic` and numeric cases together
cover the original dispatch; `opapp` and `eval` are handled by the evaluator
and return `none` here, as in HOL. Floating-point behavior inherits the
rational-cut assumption used by
`fpSemFpUopComp`, `fpSemFpBopComp`, `fpSemFpfma`, and `doTest`. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_app_def"]
noncomputable def doApp {σ : Type} (state : Store Value × HolFfiState σ) (op : Op)
    (values : List Value) : Option (BasicAppResult σ) :=
  match op with
  | .arith action .float64T => (floatArith action values).map (fun result => (state, .val result))
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
