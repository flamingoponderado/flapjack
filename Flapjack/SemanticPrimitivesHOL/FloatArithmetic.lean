import Flapjack.SemanticPrimitivesHOL.ApplyNumericCore

/-! Floating arithmetic dispatcher for source primitives. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL

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

end Flapjack.SemanticPrimitivesHOL
