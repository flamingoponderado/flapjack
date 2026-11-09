module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyClock

@[expose] public section

/-! I/O-event preservation for flat primitive application. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Successful primitive application extends the FFI event trace. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "do_app_io_events_mono"]
theorem doApp_ioEventsMono {C F : Type} (state : State C F) (op : FlatLang.Op)
    (values : List Value) (next : State C F) (result : Result Value Value)
    (run : doApp state op values = some (next, result)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents :=
  (doApp_stableAndIo state next op values result run).2.2

end Flapjack.Compiler.Backend.FlatProps
