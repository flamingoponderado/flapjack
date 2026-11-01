import Flapjack.HolRef

/-! Generation state from the combined garbage collector. -/
namespace Flapjack.Compiler.Backend.GcCombined

/-- Current generation index and generation start offsets. -/
@[hol "cakeml/compiler/backend/gc/gc_combinedScript.sml" "gen_state"]
inductive GenState where
  | genState : Nat → List Nat → GenState
  deriving DecidableEq, Repr

end Flapjack.Compiler.Backend.GcCombined
