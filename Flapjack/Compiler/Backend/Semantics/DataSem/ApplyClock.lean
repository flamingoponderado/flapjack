module

public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame

@[expose] public section

/-! Clock preservation for data-language primitive applications. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A successful primitive application cannot increase the clock. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_app_clock"]
theorem doApp_clock_le {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) (next : State C F)
    (run : doApp op args state = .val (value, next)) : next.clock ≤ state.clock :=
  Nat.le_of_eq (doApp_controlFrame op args state next value run).2.2.2.2.2

end Flapjack.Compiler.Backend.DataSem
