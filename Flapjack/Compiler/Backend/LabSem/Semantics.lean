import Flapjack.Compiler.Backend.LabSem.Evaluate
import Flapjack.Misc.LprefixLub

namespace Flapjack.Compiler.Backend.LabSem
open Flapjack

/-- Full HOL behavior, with existential clocks, HOL's optional choice of a
terminating behavior, and the lazy-list LUB of every clock-indexed trace.
The word dimension and inherited FP real-number translation are those of
the reviewed native evaluator (docs/SOUNDNESS.md item 8). -/
@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "semantics_def"
  (words_as_type_indexed_bitvec)]
noncomputable def semantics {width : Nat} [NeZero width] {C F : Type}
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) : HolBehaviour :=
  open Classical in
  if ∃ clock, (evaluate { state with clock := clock }).1 = .error then .fail
  else
    match holOptionSome (fun result => ∃ clock next outcome,
        evaluate { state with clock := clock } = (.halt outcome, next) ∧
        result = HolBehaviour.terminate outcome next.ffi.ioEvents) with
    | some result => result
    | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluate { state with clock := clock }).2.ffi.ioEvents))

end Flapjack.Compiler.Backend.LabSem
