module

public import Flapjack.Compiler.Inference.Unify.Walkstar.Computational

@[expose] public section

/-! Source normalization and its computational worklist agree under `cwfs`. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- The encoded source normalizer. Its off-`cwfs` behavior inherits the
    explicit model choice of the first-order normalizer. -/
noncomputable def cwalkstarModel (s : Spt InferT) (t : InferT) : InferT :=
  tWalkstar (sp2fm s) t

/-- A total proof model of the partial computational worklist. The default
    for nontermination is not claimed to match HOL outside `cwfs`. -/
def tcwalkstarP1Model (s : Spt InferT) (ts : List InferT) (k : List KclKont) : List InferT :=
  (walkStarWork s false ts k).getD []

@[hol "cakeml/compiler/inference/unifyScript.sml" "tcwalkstarwl_correct"]
theorem tcwalkstarwlCorrect (s : Spt InferT) (t : InferT) (hw : cwfs s) :
    cwalkstarModel s t = (tcwalkstarP1Model s [t] []).headD (.varDb 0) := by
  have h := walkStarListCorrect s hw [t]
  change walkStarWork s false [t] [] = some [tWalkstar (sp2fm s) t] at h
  simp [cwalkstarModel, tcwalkstarP1Model, h]

end Flapjack.Compiler.Inference.Unify
