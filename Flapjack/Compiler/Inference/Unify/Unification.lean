module

public import Flapjack.Compiler.Inference.Unify.Encoding
public import Flapjack.HOL.Unification.UnifDef.Choice
public import Flapjack.HOL.Unification.UnifDef.OptionCodec

@[expose] public section

/-! Proof-side inference unification through the first-order encoding. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Encode every value of an inference substitution, preserving its keys. -/
def encodeSubst (s : HolFiniteMapExact Nat InferT) : HolFiniteMapExact Nat (Term Atom) :=
  s.map2 (fun p => encodeInferT p.2)

/-- Decode every value of a first-order substitution, preserving its keys. -/
def decodeSubst (s : HolFiniteMapExact Nat (Term Atom)) : HolFiniteMapExact Nat InferT :=
  s.map2 (fun p => decodeInferT p.2)

/-- The source type encoding is a left inverse on the entire substitution. -/
theorem decodeEncodeSubst (s : HolFiniteMapExact Nat InferT) :
    decodeSubst (encodeSubst s) = s := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [decodeSubst, encodeSubst, HolFiniteMapExact.lookup_map2]
  cases s.lookup key <;> simp [decodeLeftInverse.1]

/-- Re-encoding a decoded substitution is exact precisely when every stored
    term is the encoding of an inference type. This is map infrastructure for
    the source unifier's encoding argument, not a separate HOL port. -/
theorem encodeDecodeSubstIff (s : HolFiniteMapExact Nat (Term Atom)) :
    encodeSubst (decodeSubst s) = s ↔
      ∀ key t, s.lookup key = some t → ∃ it, t = encodeInferT it := by
  constructor
  · intro eq key t found
    have h := congrArg (fun map => map.lookup key) eq
    simp only [encodeSubst, decodeSubst, HolFiniteMapExact.lookup_map2, found,
      Option.map_some, Option.some.injEq] at h
    exact ⟨decodeInferT t, h.symm⟩
  · intro image
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp only [encodeSubst, decodeSubst, HolFiniteMapExact.lookup_map2]
    cases h : s.lookup key with
    | none => rfl
    | some t =>
      obtain ⟨it, rfl⟩ := image key t h
      simp [decodeLeftInverse.1]

/-- Decode the selected first-order unifier, as in the source definition.
    This remains untagged pending source-choice review and a qualifier for the
    option-valued finite-map result. -/
noncomputable def tUnifyModel (s : HolFiniteMapExact Nat InferT) (t1 t2 : InferT) :
    Option (HolFiniteMapExact Nat InferT) :=
  (specifiedUnify (encodeSubst s) (encodeInferT t1) (encodeInferT t2)).map decodeSubst

/-- The input substitution survives the canonical finite-map codec. This
    representation witness is infrastructure for the source unifier port. -/
theorem holFmapAsFiniteSupportParamWitness_tUnifyModel_s
    (s : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).lookup key = s.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s)).finiteSupport = s.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s) = s := by
  cases s
  exact ⟨rfl, rfl, rfl⟩

/-- The optional output survives the map codec, and its lookup is the
    source-shaped option-map of the decoded first-order lookup. The theorem
    has no HOL original: it witnesses the carrier boundary only. The
    `specifiedUnify` on the right is Lean's choice, whose guarded agreement
    with the HOL-selected unifier remains to be reviewed. -/
theorem holFmapAsFiniteSupportOptionResultWitness_tUnifyModel
    (s : HolFiniteMapExact Nat InferT) (t1 t2 : InferT) (key : Nat) :
    ((tUnifyModel s t1 t2).map FiniteMapBroad.toBroad).map FiniteMapBroad.ofBroad =
        tUnifyModel s t1 t2 ∧
      (tUnifyModel s t1 t2).map (fun result => result.lookup key) =
        (specifiedUnify (encodeSubst s) (encodeInferT t1) (encodeInferT t2)).map
          (fun result => (result.lookup key).map decodeInferT) := by
  constructor
  · exact optionSubstCodecRoundtrip _
  · cases found : specifiedUnify (encodeSubst s) (encodeInferT t1) (encodeInferT t2) with
    | none => simp [tUnifyModel, found]
    | some result => simp [tUnifyModel, found, decodeSubst]

end Flapjack.Compiler.Inference.Unify
