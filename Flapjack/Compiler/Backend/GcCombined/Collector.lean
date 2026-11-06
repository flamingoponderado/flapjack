import Flapjack.Compiler.Backend.GcCombined
import Flapjack.Compiler.Backend.GenGc
import Flapjack.Compiler.Backend.GenGcPartial
import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.CopyingGc
import Flapjack.Misc.ListEl

/-! The combined abstract collector. -/
namespace Flapjack.Compiler.Backend.GcCombined
open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- Construct minor collector bounds from the stored generation starts. -/
@[hol "cakeml/compiler/backend/gc/gc_combinedScript.sml" "make_partial_conf_def"]
noncomputable def makePartialConf {β : Type} (conf : GenGc.Config β) (gens : GenState) (refsStart : Nat) :
    GenGcPartial.Config β :=
  match gens with
  | .genState _ starts => ⟨conf.limit, conf.isRef, holHd starts, refsStart⟩

/-- Run the collector selected by the data-to-word configuration. -/
@[hol "cakeml/compiler/backend/gc/gc_combinedScript.sml" "gc_combined_def"]
noncomputable def gcCombined {α β : Type} (conf : GenGc.Config β) (kind : GcKind)
    (input : List (HeapAddress α) × List (HeapElement α β) × GenState × Nat × Bool) :
    List (HeapAddress α) × List (HeapElement α β) × Nat × Nat × GenState × Bool :=
  let (roots, heap, gens, refsStart, doPartial) := input
  match kind with
  | .none => (roots, heap, 0, 0, gens, true)
  | .simple =>
    let (roots1, heap1, a, ok) := CopyingGc.fullGc (roots, heap, conf.limit)
    (roots1, heap1 ++ heapExpand (conf.limit - a), a, conf.limit - a, gens, ok)
  | .generational limits =>
    if doPartial then
      let (roots1, state) := GenGcPartial.partialGc (makePartialConf conf gens refsStart) (roots, heap)
      (roots1, state.old ++ state.h1 ++ heapExpand state.n ++ state.r1,
        state.a, state.n, .genState 0 (limits.map fun _ => state.a), state.ok)
    else
      let (roots1, state) := GenGc.genGc conf (roots, heap)
      (roots1, state.h1 ++ heapExpand state.n ++ state.r1,
        state.a, state.n, .genState 0 (limits.map fun _ => state.a), state.ok)

end Flapjack.Compiler.Backend.GcCombined
