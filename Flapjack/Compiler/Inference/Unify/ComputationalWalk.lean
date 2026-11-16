module

public import Flapjack.Compiler.Inference.Unify.ComputationalWf
public import Flapjack.Compiler.Inference.Unify.Walk.Term

@[expose] public section

/-! Sparse-tree walker equations on the original well-formedness premises. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Proof model of the sparse-tree variable walker. Its behavior outside the
    original well-formedness premises inherits the model choice in `vwalk`, so
    this definition is not claimed as an unconditional port of `cvwalk_def`. -/
noncomputable def cvwalkModel (s : Spt InferT) (n : Nat) : InferT :=
  tVwalk (sp2fm s) n

/-- Proof model of the sparse-tree term walker; its behavior outside the
    original well-formedness premise inherits the model choice in `vwalk`. -/
noncomputable def cwalkModel (s : Spt InferT) (t : InferT) : InferT :=
  tWalk (sp2fm s) t

@[hol "cakeml/compiler/inference/unifyScript.sml" "cvwalk_thm"]
theorem cvwalkThm (s : Spt InferT) (n : Nat)
    (htree : sptWf (sptMap encodeInferT s) = true)
    (hsub : swfs (sptMap encodeInferT s)) :
    cvwalkModel s n = match sptLookup n s with
      | none => .uvar n
      | some (.varDb v) => .varDb v
      | some (.app l tc) => .app l tc
      | some (.uvar u) => cvwalkModel s u := by
  have heq : sp2fm (sptMap encodeInferT s) =
      (sp2fm s).map2 (fun p => encodeInferT p.2) := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    exact sptLookup_sptMap encodeInferT s key
  have hw : tWfs (sp2fm s) := by
    change WellFounded (vR ((sp2fm s).map2 (fun p => encodeInferT p.2)))
    rw [← heq]
    exact hsub
  have _ := htree
  have he := tVwalkEq (sp2fm s) hw n
  cases found : sptLookup n s with
  | none => simpa [cvwalkModel, sp2fm, found] using he
  | some t => cases t <;> simpa [cvwalkModel, sp2fm, found] using he

@[hol "cakeml/compiler/inference/unifyScript.sml" "cwalk_thm"]
theorem cwalkThm (s : Spt InferT) (it : InferT) (h : cwfs s) :
    cwalkModel s it = match it with
      | .varDb v => .varDb v
      | .app l tc => .app l tc
      | .uvar v => cvwalkModel s v := by
  have _ := h
  cases it with
  | varDb n => exact tWalkEqn.2.2 (sp2fm s) n
  | app ts tc => exact tWalkEqn.2.1 (sp2fm s) ts tc
  | uvar u => exact tWalkEqn.1 (sp2fm s) u

end Flapjack.Compiler.Inference.Unify
