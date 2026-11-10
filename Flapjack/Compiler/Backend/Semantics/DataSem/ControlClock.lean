module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control

@[expose] public section

/-! Clock properties of data-language control operations. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack

/-- Setting variables leaves the clock unchanged. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "set_vars_clock"]
theorem setVars_clock {C F : Type} (names : List Nat) (values : List Value)
    (state : State C F) : (setVars names values state).clock = state.clock := by
  rfl

end Flapjack.Compiler.Backend.DataSem
