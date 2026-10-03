import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.BackendCommon

/-- Complete source-origin trace carrier used by source-to-flat variable names.
The constructor order and every recursive/numeric payload match the source. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "tra"]
inductive Tra where
  | sourceLoc : Nat → Nat → Nat → Nat → Tra
  | cons : Tra → Nat → Tra
  | union : Tra → Tra → Tra
  | none : Tra
  deriving DecidableEq, Repr

/-- The actual source definition is this location sentinel; its preceding
historical comment describing four `Cons` nodes does not match the definition. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "orphan_trace_def"]
def orphanTrace : Tra := .sourceLoc 2 2 1 1

/-- Preserve disabled tracing; otherwise append the source's numbered node. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "mk_cons_def"]
def mkCons (tr : Tra) (n : Nat) : Tra :=
  match tr with
  | .none => .none
  | _ => .cons tr n

end Flapjack.Compiler.Backend.BackendCommon
