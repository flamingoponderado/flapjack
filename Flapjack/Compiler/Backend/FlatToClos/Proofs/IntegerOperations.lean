import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Int
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyNumeric

/-! Integer primitive correspondence over the proof-side relations. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- The arithmetic operations directly emitted by flat-to-closure agree on
integer operands, provided division and remainder have a nonzero divisor.
This is a proof-side lemma; neither dispatcher is yet fully reviewed. -/
theorem intArith_related {C F : Type} (state : FlatSem.State C F)
    (action : Arith) (left right : Int)
    (supported : action = .add ∨ action = .sub ∨ action = .mul ∨ action = .div ∨ action = .mod)
    (nonzero : right ≠ 0) :
    ∃ flatValue targetValue,
      FlatSem.doAppNumeric state (.arith action .intT)
        [.litv (.intLit left), .litv (.intLit right)] = some (some (state, .val flatValue)) ∧
      ClosSem.doIntApp (match action with
        | .add => .add | .sub => .sub | .mul => .mult | .div => .div | .mod => .mod
        | _ => .const 0) [.number left, .number right] = some targetValue ∧
      ValueRel flatValue targetValue := by
  rcases supported with rfl | rfl | rfl | rfl | rfl <;>
    simp [FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue,
      FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore,
      ClosSem.doIntApp, nonzero]
  all_goals exact ValueRel.int _

/-- A zero divisor raises the flat Div exception while the raw closure
integer operation rejects it; the lowering inserts the matching raise. -/
theorem intDiv_zero {C F : Type} (state : FlatSem.State C F) (left : Int) :
    FlatSem.doAppNumeric state (.arith .div .intT) [.litv (.intLit left), .litv (.intLit 0)] =
        some (some (state, .err (.raise FlatSem.divExnV))) ∧
      ClosSem.doIntApp .div [.number left, .number 0] = none ∧
      ValueRel FlatSem.divExnV (.block 2 []) := by
  simp [FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue,
    SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doIntApp]
  exact ValueRel.con .nil

/-- Remainder by zero has the same explicit Div-exception lowering. -/
theorem intMod_zero {C F : Type} (state : FlatSem.State C F) (left : Int) :
    FlatSem.doAppNumeric state (.arith .mod .intT) [.litv (.intLit left), .litv (.intLit 0)] =
        some (some (state, .err (.raise FlatSem.divExnV))) ∧
      ClosSem.doIntApp .mod [.number left, .number 0] = none ∧
      ValueRel FlatSem.divExnV (.block 2 []) := by
  simp [FlatSem.doAppNumeric, FlatSem.applyNumericProjection, FlatSem.flatToValue,
    SemanticPrimitivesHOL.doApp, SemanticPrimitivesHOL.doAppNumericCore, ClosSem.doIntApp]
  exact ValueRel.con .nil

end Flapjack.Compiler.Backend.FlatToClos
