import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyClock

/-! Local-environment preservation for data primitives. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- All successful primitive operations preserve locals, stack, handler,
local frame size and clock. Installation intentionally resets frame-size
metadata, so this theorem excludes that field. -/
theorem doApp_control {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp op args state = .val (value, next)) :
    next.locals = state.locals ∧ next.stack = state.stack ∧ next.handler = state.handler ∧
      next.localsSize = state.localsSize ∧ next.clock = state.clock := by
  have frame := doApp_controlFrame op args state next value run
  exact ⟨frame.1, frame.2.1, frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.2⟩

end Flapjack.Compiler.Backend.DataSem
