import Flapjack.SemanticPrimitivesHOL.Apply
import Flapjack.SemanticPrimitivesHOL.Test

/-! Source primitive arithmetic and the assembled application dispatcher.
The dispatcher uses the existing rational-cut floating-point model. The
complete declaration is pending full source and carrier review. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Executable helper for the word arithmetic clauses of source application. -/
def wordArith {width : Nat} (op : Arith) (a b : BitVec width) : Option (BitVec width) :=
  match op with
  | .add => some (a + b)
  | .sub => some (a - b)
  | .and => some (a &&& b)
  | .or => some (a ||| b)
  | .xor => some (a ^^^ b)
  | _ => none

/-- Computable integer, boolean, word and conversion cases. Outer `none`
indicates a case that requires the floating-point or comparison dispatcher. -/
def doAppNumericCore {σ : Type} (state : Store Value × HolFfiState σ) (op : Op)
    (values : List Value) : Option (Option (BasicAppResult σ)) :=
  let value (v : Value) : Option (BasicAppResult σ) := some (state, .val v)
  let raised (v : Value) : Option (BasicAppResult σ) := some (state, .err (.raise v))
  match op with
  | .arith _ .float64T => none
  | .arith action typ => some <| match typ, action, values with
    | .intT, action, [.litv (.intLit a), .litv (.intLit b)] =>
      match action with
      | .add => value (.litv (.intLit (a + b)))
      | .sub => value (.litv (.intLit (a - b)))
      | .mul => value (.litv (.intLit (a * b)))
      | .div => if b = 0 then raised divExnV else value (.litv (.intLit (a.fdiv b)))
      | .mod => if b = 0 then raised divExnV else value (.litv (.intLit (a.fmod b)))
      | _ => none
    | .wordT .w8, action, [.litv (.word8 a), .litv (.word8 b)] => do
      let result ← wordArith action a b
      value (.litv (.word8 result))
    | .wordT .w64, action, [.litv (.word64 a), .litv (.word64 b)] => do
      let result ← wordArith action a b
      value (.litv (.word64 result))
    | .boolT, .not, [v@(.conv (some (.typeStamp name 0)) [])] =>
      if checkType .boolT v then value (boolValue (name != ofString "True")) else none
    | _, _, _ => none
  | .fromTo source target => some <| match source, target, values with
    | .wordT .w8, .intT, [.litv (.word8 w)] => value (.litv (.intLit w.toNat))
    | .wordT .w64, .intT, [.litv (.word64 w)] => value (.litv (.intLit w.toNat))
    | .intT, .wordT .w8, [.litv (.intLit i)] => value (.litv (.word8 (BitVec.ofInt 8 i)))
    | .intT, .wordT .w64, [.litv (.intLit i)] => value (.litv (.word64 (BitVec.ofInt 64 i)))
    | .charT, .intT, [.litv (.char c)] => value (.litv (.intLit c.toNat))
    | .intT, .charT, [.litv (.intLit i)] =>
      if i < 0 ∨ i > 255 then raised chrExnV else value (.litv (.char (BitVec.ofNat 8 i.toNat)))
    | .charT, .wordT .w8, [.litv (.char c)] => value (.litv (.word8 c))
    | .wordT .w8, .charT, [.litv (.word8 w)] => value (.litv (.char w))
    | .float64T, .wordT .w64, [.litv (.float64 w)] => value (.litv (.word64 w))
    | .wordT .w64, .float64T, [.litv (.word64 w)] => value (.litv (.float64 w))
    | _, _, _ => none
  | _ => none

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
and return `none` here, as in HOL. The full clause and carrier review is
pending. Floating-point behavior inherits the rational-cut assumption used by
`fpSemFpUopComp`, `fpSemFpBopComp`, `fpSemFpfma`, and `doTest`. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_app_def"]
noncomputable def doApp {σ : Type} (state : Store Value × HolFfiState σ) (op : Op)
    (values : List Value) : Option (BasicAppResult σ) :=
  match op with
  | .arith action .float64T => (floatArith action values).map (fun result => (state, .val result))
  | .test test typ => match values with
    | [first, second] => match doTest test typ first second with
      | .typeError => none
      | .val b => some (state, .val (boolValue b))
    | _ => none
  | _ => match doAppNumericCore state op values with
    | some result => result
    | none => (doAppBasic state op values).getD none

end Flapjack.SemanticPrimitivesHOL
