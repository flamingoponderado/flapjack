module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Events
public import Flapjack.HolRef

@[expose] public section

/-! Event-trace and timeout properties of closure primitive dispatch. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL

namespace EventTracePort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EventTracePort

/-- A successful primitive application extends the event trace. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_io_events_mono"
  (fmap_as_finite_support := [refs, code])]
theorem doApp_ioEvents_mono {C F : Type} (op : ClosLang.Op) (vs : List ClosSem.Value)
    (s : ClosSem.State C F) (v : ClosSem.Value) (s' : ClosSem.State C F)
    (run : ClosSem.doApp op vs s = .val (v, s')) :
    s.ffi.ioEvents <+: s'.ffi.ioEvents :=
  ClosSem.doApp_ioEvents_prefix op vs s s' v run

/-- Primitive dispatch never produces a timeout. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_never_timesout"
  (fmap_as_finite_support := [refs, code])]
theorem doApp_never_timesout {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (s : ClosSem.State C F) :
    ClosSem.doApp op args s ≠ .err (.abort .timeoutError) :=
  ClosSem.doApp_not_timeout op args s

end Flapjack.Compiler.Backend.ClosProps
