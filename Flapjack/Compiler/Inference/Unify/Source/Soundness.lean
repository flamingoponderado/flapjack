module

public import Flapjack.Compiler.Inference.Unify.Source.Continuation
public import Flapjack.HOL.Unification.UnifProps.Soundness
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
  have original := cunifyPreservesCwfsModel s t1 t2 sx h
  have he : tUnifyModel (sp2fm s) t1 t2 = some (sp2fm sx) := by
    rw [← cunifyModelMap s t1 t2 h.1, h.2]
    rfl
  have hws : tWfs (sp2fm s) := by
    change wfs (encodeSubst (sp2fm s))
    rw [← sparseEncode]
    exact h.1.1
  have aux := encodeUnifyModelAll 0 (encodeSubst (sp2fm s)) (encodeInferT t1) (encodeInferT t2)
    (sp2fm s) t1 t2 ⟨rfl, Or.inl ⟨rfl, rfl⟩, hws⟩
  rw [he] at aux
  simp only [Option.map_some] at aux
  have sound := tunifyAuxSound _ _ _ _ ⟨hws, aux⟩
  refine ⟨original, ?_, ?_⟩
  · apply (sptSubsptLookup s sx).2
    intro key val found
    have encoded : (encodeSubst (sp2fm s)).lookup key = some (encodeInferT val) := by
      simp [encodeSubst, HolFiniteMapExact.lookup_map2, sp2fm, found]
    have mapped := sound.2.1 key (encodeInferT val) encoded
    cases target : sptLookup key sx with
    | none => simp [encodeSubst, HolFiniteMapExact.lookup_map2, sp2fm, target] at mapped
    | some value =>
      simp only [encodeSubst, HolFiniteMapExact.lookup_map2, sp2fm, target,
        Option.map_some, Option.some.injEq] at mapped
      have same := congrArg decodeInferT mapped
      simpa [decodeLeftInverse.1] using same
  · unfold cwalkstarModel
    exact congrArg decodeInferT sound.2.2

end Flapjack.Compiler.Inference.Unify
