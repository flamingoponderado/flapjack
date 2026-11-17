import Flapjack.Compiler.Inference.Infer.Generalise
import Flapjack.HolRef.GeneraliseMapAudit

/-! Positive and negative tests for the prospective generalization map audit.
These checks do not enable a HOL qualifier. -/
open Lean Meta Flapjack Flapjack.HOL.Transfer.Fmsp
  Flapjack.Compiler.Inference
  Flapjack.Compiler.Inference.Infer
  Flapjack.Compiler.Inference.Infer.Generalise

set_option linter.unusedVariables false in
private def rawInput (_ _ : Nat) (subst : Nat → Option Nat) (_ : InferT) :
    Nat × HolFiniteMapExact Nat Nat × InferT := (0, HolFiniteMapExact.empty, .uvar 0)

private def wrongResult (_ _ : Nat) (subst : HolFiniteMapExact Nat Nat) (_ : InferT) :
    Nat × InferT × HolFiniteMapExact Nat Nat := (0, .uvar 0, subst)

private def extraInput (_ _ : Nat) (s : HolFiniteMapExact Nat Nat) (t : InferT) (_ : True) :
    Nat × HolFiniteMapExact Nat Nat × InferT := (0, s, t)

private def wrongMapTypes (_ _ : Nat) (subst : HolFiniteMapExact Nat Bool) (t : InferT) :
    Nat × HolFiniteMapExact Nat Bool × InferT := (0, subst, t)

private def wrongMapKey (_ _ : Nat) (subst : HolFiniteMapExact Bool Nat) (t : InferT) :
    Nat × HolFiniteMapExact Bool Nat × InferT := (0, subst, t)

private def wrongMapPosition (_ : Nat) (s : HolFiniteMapExact Nat Nat) (_ : Nat) (t : InferT) :
    Nat × HolFiniteMapExact Nat Nat × InferT := (0, s, t)

private def extraMap (_ _ : Nat) (s : HolFiniteMapExact Nat Nat) (_ : HolFiniteMapExact Nat Nat)
    (t : InferT) : Nat × HolFiniteMapExact Nat Nat × InferT := (0, s, t)

private def wrongLeaf (_ _ : Nat) (subst : HolFiniteMapExact Nat Nat) (_ : InferT) :
    Nat × HolFiniteMapExact Nat Nat × Nat := (0, subst, 0)

private def renamedMap (_ _ : Nat) (other : HolFiniteMapExact Nat Nat) (t : InferT) :
    Nat × HolFiniteMapExact Nat Nat × InferT := (0, other, t)

private def sameSignature (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat) (t : InferT) :
    Nat × HolFiniteMapExact Nat Nat × InferT := generaliseMap minimum next subst t

private theorem vacuousWitness (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat)
    (t : InferT) (key : Nat) :
    subst.lookup key = subst.lookup key ∧
      (generaliseMap minimum next subst t).2.1.lookup key =
        (generaliseMap minimum next subst t).2.1.lookup key := ⟨rfl, rfl⟩

private theorem extraPremiseWitness (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat)
    (t : InferT) (key : Nat) (_ : True) :
    (sp2fm (fm2sp subst)).lookup key = subst.lookup key ∧
      (generaliseMap minimum next subst t).2.1.lookup key =
        sptLookup key (generalise minimum next (fm2sp subst) t).2.1 :=
  holFmapAsFiniteSupportParameterTupleResultWitness_generaliseMap minimum next subst t key

private theorem wrongKeyWitness (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat)
    (t : InferT) (key : Nat) :
    (sp2fm (fm2sp subst)).lookup (key + 1) = subst.lookup (key + 1) ∧
      (generaliseMap minimum next subst t).2.1.lookup (key + 1) =
        sptLookup (key + 1) (generalise minimum next (fm2sp subst) t).2.1 :=
  holFmapAsFiniteSupportParameterTupleResultWitness_generaliseMap minimum next subst t (key + 1)

private theorem implicitKeyWitness (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat)
    (t : InferT) {key : Nat} :
    (sp2fm (fm2sp subst)).lookup key = subst.lookup key ∧
      (generaliseMap minimum next subst t).2.1.lookup key =
        sptLookup key (generalise minimum next (fm2sp subst) t).2.1 :=
  holFmapAsFiniteSupportParameterTupleResultWitness_generaliseMap minimum next subst t key

private theorem renamedMapWitness (minimum next : Nat) (other : HolFiniteMapExact Nat Nat)
    (t : InferT) (key : Nat) :
    (sp2fm (fm2sp other)).lookup key = other.lookup key ∧
      (generaliseMap minimum next other t).2.1.lookup key =
        sptLookup key (generalise minimum next (fm2sp other) t).2.1 :=
  holFmapAsFiniteSupportParameterTupleResultWitness_generaliseMap minimum next other t key

private theorem swappedInputsWitness (minimum next : Nat) (subst : HolFiniteMapExact Nat Nat)
    (t : InferT) (key : Nat) :
    (sp2fm (fm2sp subst)).lookup key = subst.lookup key ∧
      (generaliseMap next minimum subst t).2.1.lookup key =
        sptLookup key (generalise next minimum (fm2sp subst) t).2.1 :=
  holFmapAsFiniteSupportParameterTupleResultWitness_generaliseMap next minimum subst t key

run_meta do
  for (name, isList) in [(``generaliseMap, false), (``generaliseListMap, true)] do
    let qualified ← generaliseMapQualifiedProblems name
      "cakeml/compiler/inference/inferScript.sml" "generalise_def" none "subst" "component_2" false
    unless qualified.isEmpty do throwError "valid prospective qualifier {name} rejected: {qualified}"
    for (path, holName, line, parameter, component, other) in [
        ("cakeml/compiler/inference/inferScript.sml", "generalise_def", some 151, "subst", "component_2", false),
        ("cakeml/compiler/inference/inferScript.sml", "wrong", none, "subst", "component_2", false),
        ("other", "generalise_def", none, "subst", "component_2", false),
        ("cakeml/compiler/inference/inferScript.sml", "generalise_def", none, "other", "component_2", false),
        ("cakeml/compiler/inference/inferScript.sml", "generalise_def", none, "subst", "component_1", false),
        ("cakeml/compiler/inference/inferScript.sml", "generalise_def", none, "subst", "component_2", true)] do
      let bad := generaliseMapMetadataProblems name path holName line parameter component other
      if bad.isEmpty then throwError "invalid prospective qualifier metadata accepted"
    let bundleErrors ← generaliseMapBundleProblems name
    unless bundleErrors.isEmpty do throwError "valid bundle {name} rejected: {bundleErrors}"
    let info ← getConstInfo name
    let errors ← generaliseMapSignatureProblems info.type isList
    unless errors.isEmpty do throwError "valid operation {name} rejected: {errors}"
    let wrongVariant ← generaliseMapSignatureProblems info.type (!isList)
    if wrongVariant.isEmpty then throwError "wrong operation variant {name} accepted"
  for name in [``rawInput, ``wrongResult, ``extraInput, ``wrongMapTypes, ``wrongMapKey,
      ``wrongMapPosition, ``extraMap, ``wrongLeaf, ``renamedMap] do
    let info ← getConstInfo name
    let errors ← generaliseMapSignatureProblems info.type false
    if errors.isEmpty then throwError "invalid operation {name} accepted"
  let same ← getConstInfo ``sameSignature
  let sameShape ← generaliseMapSignatureProblems same.type false
  unless sameShape.isEmpty do throwError "same-signature fixture should pass the shape check"
  let sameBundle ← generaliseMapBundleProblems ``sameSignature
  if sameBundle.isEmpty then throwError "unapproved same-signature declaration accepted"
  let sameQualified ← generaliseMapQualifiedProblems ``sameSignature
    "cakeml/compiler/inference/inferScript.sml" "generalise_def" none "subst" "component_2" false
  if sameQualified.isEmpty then throwError "unapproved same-signature qualifier accepted"
  for (name, isList) in [
      (``holFmapAsFiniteSupportParameterTupleResultWitness_generaliseMap, false),
      (``holFmapAsFiniteSupportParameterTupleResultWitness_generaliseListMap, true)] do
    let info ← getConstInfo name
    let errors ← generaliseMapWitnessProblems info.type isList
    unless errors.isEmpty do throwError "valid witness {name} rejected: {errors}"
    let wrongVariant ← generaliseMapWitnessProblems info.type (!isList)
    if wrongVariant.isEmpty then throwError "wrong witness variant {name} accepted"
  for name in [``vacuousWitness, ``extraPremiseWitness, ``wrongKeyWitness,
      ``implicitKeyWitness, ``renamedMapWitness, ``swappedInputsWitness] do
    let info ← getConstInfo name
    let errors ← generaliseMapWitnessProblems info.type false
    if errors.isEmpty then throwError "invalid witness {name} accepted"
