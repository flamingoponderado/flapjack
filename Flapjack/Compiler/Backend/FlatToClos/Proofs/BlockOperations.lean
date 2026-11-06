import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyFlat
import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic

/-! Block primitive cases for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos

/-- The two semantic Boolean representations are related. -/
theorem boolValue_related (value : Bool) : ValueRel (FlatSem.boolValue value) (ClosSem.boolValue value) := by
  cases value <;> exact .con .nil


end Flapjack.Compiler.Backend.FlatToClos
