module

public import Flapjack.SemanticPrimitivesHOL.Apply
public import Flapjack.SemanticPrimitivesHOL.Test

@[expose] public section

/-! Computable source primitive arithmetic and conversion dispatcher. -/
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

/-- Computable integer, boolean, word and conversion cases. The conversion
cases fuse HOL's type guard and conversion into executable pattern matching;
`doAppNumericCore_fromTo` proves their correspondence with that HOL form.
Outer `none` indicates a case requiring floating-point or comparison dispatch. -/
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


end Flapjack.SemanticPrimitivesHOL
