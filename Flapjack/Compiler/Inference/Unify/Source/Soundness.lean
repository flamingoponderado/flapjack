module

public import Flapjack.Compiler.Inference.Unify.Source
public import Flapjack.Misc.Sptree.Subspt

@[expose] public section

/-! Source unifier soundness for sparse-tree substitutions. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- Source-shaped normalization, untagged because the chosen walker is
    only identified with HOL under the well-formedness guard. -/
noncomputable def cwalkstarModel (s : Spt InferT) (t : InferT) : InferT :=
  decodeInferT (walkstar ((sp2fm s).map2 (fun p => encodeInferT p.2)) (encodeInferT t))

@[hol "cakeml/compiler/inference/unifyScript.sml" "cunify_unifier"]
theorem cunifyUnifierModel (s : Spt InferT) (t1 t2 : InferT) (sx : Spt InferT)
    (h : cwfs s ∧ cunifyModel s t1 t2 = some sx) :
    cwfs sx ∧ sptSubspt s sx ∧ cwalkstarModel sx t1 = cwalkstarModel sx t2 := by
  have he : tUnifyModel (sp2fm s) t1 t2 = some (sp2fm sx) := by
    rw [← cunifyModelMap s t1 t2, h.2]
    rfl
  have hws : tWfs (sp2fm s) := by
    change wfs (encodeSubst (sp2fm s))
    rw [← sparseEncode]
    exact h.1.1
  have sound := tUnifyModelSound (sp2fm s) t1 t2 (sp2fm sx) ⟨hws, he⟩
  have original : cwfs sx := by
    constructor
    · change wfs (sp2fm (sptMap encodeInferT sx))
      rw [sparseEncode]
      exact sound.1
    · exact cunifyModelTreeWf s sx t1 t2 h.2
  refine ⟨original, ?_, ?_⟩
  · apply (sptSubsptLookup s sx).2
    intro key val found
    exact sound.2.1 key val found
  · unfold cwalkstarModel
    exact sound.2.2

end Flapjack.Compiler.Inference.Unify
