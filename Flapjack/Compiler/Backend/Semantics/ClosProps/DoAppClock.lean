module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyClockShift
public import Flapjack.SemanticPrimitivesProps.ResultMap
public import Flapjack.HolRef

@[expose] public section

/-! Clock shifting through the closure primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL
open Flapjack.HolRef

namespace DoAppClockPort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end DoAppClockPort

/-- Primitive application commutes with an added clock allowance, shifting the
returned state's clock as in the source. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "do_app_add_to_clock"
  (fmap_as_finite_support := [refs, code])]
theorem doApp_add_to_clock {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (extra : Nat) :
    ClosSem.doApp op args { state with clock := state.clock + extra } =
      SemanticPrimitivesProps.mapResult (fun (value, next) =>
        (value, { next with clock := next.clock + extra })) id (ClosSem.doApp op args state) := by
  rw [ClosSem.doApp_addClock]
  cases run : ClosSem.doApp op args state with
  | val pair =>
    obtain ⟨value, next⟩ := pair
    simp only [ClosSem.addClockResult, SemanticPrimitivesProps.mapResult]
  | err error =>
    simp only [ClosSem.addClockResult, SemanticPrimitivesProps.mapResult,
      SemanticPrimitivesProps.mapErrorResult_id]

end Flapjack.Compiler.Backend.ClosProps
