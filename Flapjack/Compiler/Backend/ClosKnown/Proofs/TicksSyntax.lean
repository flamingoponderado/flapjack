module

public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! Syntax invariants preserved by known-function tick insertion. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps

/-- Tick insertion preserves the absence of label operations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "no_Labels_mk_Ticks"]
theorem ticks_noLabels (trace : BackendCommon.Tra) (index n : Nat) (e : Exp)
    (h : noLabels e) : noLabels (ticks trace index n e) := by
  induction n generalizing index e with
  | zero => exact h
  | succ n ih =>
    apply ih
    simpa [noLabels] using h

/-- Tick insertion preserves any given application-arity bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "obeys_max_app_mk_Ticks"]
theorem ticks_obeysMaxApp (limit : Nat) (trace : BackendCommon.Tra) (index n : Nat) (e : Exp)
    (h : obeysMaxApp limit e) : obeysMaxApp limit (ticks trace index n e) := by
  induction n generalizing index e with
  | zero => exact h
  | succ n ih =>
    apply ih
    simpa [obeysMaxApp] using h

end Flapjack.Compiler.Backend.ClosKnown
