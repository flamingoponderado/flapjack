module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Events
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsFull
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateEventsClockFull
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

/-- An evaluation run extends the event trace. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_io_events_mono_imp"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_ioEvents_mono_imp {C F : Type} (es : List ClosLang.Exp)
    (env : List ClosSem.Value) (s : ClosSem.State C F)
    (r : Result (List ClosSem.Value) ClosSem.Value) (s' : ClosSem.State C F)
    (h : ClosSem.evaluate es env s = (r, s')) :
    s.ffi.ioEvents <+: s'.ffi.ioEvents :=
  ClosSem.evaluate_ioEvents_prefix.1 es env s s' r h

/-- Evaluation and closure application extend the event trace. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_io_events_mono"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_ioEvents_mono {C F : Type} :
    (∀ (p : List ClosLang.Exp × List ClosSem.Value × ClosSem.State C F),
      (Prod.snd (Prod.snd p)).ffi.ioEvents <+:
        (Prod.snd (ClosSem.evaluate p.1 p.2.1 p.2.2)).ffi.ioEvents) ∧
    (∀ (loc_opt : Option Nat) (v : ClosSem.Value) (rest : List ClosSem.Value)
      (s : ClosSem.State C F),
      s.ffi.ioEvents <+:
        (Prod.snd (ClosSem.evaluateApp loc_opt v rest s)).ffi.ioEvents) := by
  constructor
  · intro p
    obtain ⟨es, env, s⟩ := p
    exact ClosSem.evaluate_ioEvents_prefix.1 es env s (ClosSem.evaluate es env s).2
      (ClosSem.evaluate es env s).1 rfl
  · intro loc_opt v rest s
    exact ClosSem.evaluate_ioEvents_prefix.2 loc_opt v rest s
      (ClosSem.evaluateApp loc_opt v rest s).2
      (ClosSem.evaluateApp loc_opt v rest s).1 rfl

/-- Adding clock to evaluation or application extends its event trace. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_add_to_clock_io_events_mono"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_add_to_clock_ioEvents_mono {C F : Type} (extra : Nat) :
    (∀ (p : List ClosLang.Exp × List ClosSem.Value × ClosSem.State C F)
      (es : List ClosLang.Exp) (env : List ClosSem.Value) (s : ClosSem.State C F),
      p = (es, env, s) →
        (Prod.snd (ClosSem.evaluate p.1 p.2.1 p.2.2)).ffi.ioEvents <+:
          (Prod.snd (ClosSem.evaluate es env { s with clock := s.clock + extra })).ffi.ioEvents) ∧
    (∀ (l : Option Nat) (v : ClosSem.Value) (r : List ClosSem.Value)
      (s : ClosSem.State C F),
      (Prod.snd (ClosSem.evaluateApp l v r s)).ffi.ioEvents <+:
        (Prod.snd (ClosSem.evaluateApp l v r
          { s with clock := s.clock + extra })).ffi.ioEvents) := by
  constructor
  · intro p es env s hp
    subst hp
    exact ClosSem.evaluate_addClock_ioEvents_prefix.1 es env s extra
  · intro l v r s
    exact ClosSem.evaluate_addClock_ioEvents_prefix.2 l v r s extra

end Flapjack.Compiler.Backend.ClosProps
