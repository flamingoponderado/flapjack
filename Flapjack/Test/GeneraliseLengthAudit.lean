import Flapjack.HolRef.GeneraliseLengthAudit
import Flapjack.Compiler.Inference.InferProps.Generalise

open Lean Meta Flapjack Flapjack.Compiler.Inference Flapjack.Compiler.Inference.Infer.Generalise
  Flapjack.Compiler.Inference.InferProps.Generalise

private abbrev producerAlias := generaliseListMap

run_meta do
  let target := ``generaliseListLength
  let path := "cakeml/compiler/inference/inferPropsScript.sml"
  let name := "generalise_list_length"
  let producer := "Flapjack.Compiler.Inference.Infer.Generalise.generaliseListMap"
  let qualified ← generaliseLengthQualifiedProblems target path name none #["subst", "out"]
    producer "component_2" false
  unless qualified.isEmpty do throwError "qualified length audit rejected: {qualified}"
  if (← generaliseLengthQualifiedProblems target path name none #["subst", "out"]
      producer "component_1" false).isEmpty then
    throwError "qualified length audit accepted incorrect tuple metadata"
  if (← generaliseLengthQualifiedProblems target path name none #["subst", "out"]
      producer "component_2" true).isEmpty then
    throwError "qualified length audit accepted another qualifier"
  let invalid := #[
    generaliseLengthMetadataProblems ``producerAlias path name none #["subst", "out"] producer "component_2" false,
    generaliseLengthMetadataProblems target "other" name none #["subst", "out"] producer "component_2" false,
    generaliseLengthMetadataProblems target path "other" none #["subst", "out"] producer "component_2" false,
    generaliseLengthMetadataProblems target path name (some 198) #["subst", "out"] producer "component_2" false,
    generaliseLengthMetadataProblems target path name none #["out", "subst"] producer "component_2" false,
    generaliseLengthMetadataProblems target path name none #["subst", "subst"] producer "component_2" false,
    generaliseLengthMetadataProblems target path name none #["subst", "out"] "generaliseListMap" "component_2" false,
    generaliseLengthMetadataProblems target path name none #["subst", "out"] producer "component_1" false,
    generaliseLengthMetadataProblems target path name none #["subst", "out"] producer "component_2" true]
  for problems in invalid do
    if problems.isEmpty then throwError "generalization length audit accepted invalid metadata"
  let producerRef : HolRef := {
    path := "cakeml/compiler/inference/inferScript.sml", name := "generalise_def",
    fmapAsFiniteSupportParameterTupleResult := #["subst", "component_2"] }
  let actualRef := HolRef.get? (← getEnv) ``generaliseListMap
  unless (generaliseLengthProducerRefProblems actualRef).isEmpty do
    throwError "generalization length audit rejected the real producer reference"
  for bad in #[none, some { producerRef with line? := some 151 },
      some { producerRef with name := "generalise_list_length" },
      some { producerRef with fmapAsFiniteSupportParameterTupleResult := #[] },
      some { producerRef with fmapAsFiniteSupportParameters := #["subst"] },
      some { producerRef with fmapAsFiniteSupportParameterTupleResult := #["subst", "component_1"] }] do
    if (generaliseLengthProducerRefProblems bad).isEmpty then
      throwError "generalization length audit accepted altered producer metadata"
  let qualifiedBundle ← generaliseLengthProducerBundleProblems ``generaliseListLength
  unless qualifiedBundle.isEmpty do throwError "qualified generalization bundle rejected: {qualifiedBundle}"
  let bundle ← generaliseLengthBundleProblems ``generaliseListLength
  unless bundle.isEmpty do throwError "generalization length bundle rejected: {bundle}"
  if (← generaliseLengthBundleProblems ``producerAlias).isEmpty then
    throwError "generalization length bundle accepted the wrong target"
  for (name, binder) in #[(
      ``holFmapAsFiniteSupportParamWitness_generaliseListLength_subst, `subst),
      (``holFmapAsFiniteSupportParamWitness_generaliseListLength_out, `out)] do
    let witness ← getConstInfo name
    let problems ← generaliseLengthWitnessProblems witness.type binder
    unless problems.isEmpty do throwError "generalization map witness rejected: {problems}"
    if (← generaliseLengthWitnessProblems witness.type `wrong).isEmpty then
      throwError "generalization map witness audit accepted the wrong binder name"
    forallTelescope witness.type fun args result => do
      let broad ← mkAppM ``FiniteMapBroad.toBroad #[args[0]!]
      let roundtrip ← mkAppM ``FiniteMapBroad.ofBroad #[broad]
      let vacuous := result.replace fun expr => if expr == roundtrip then some args[0]! else none
      if vacuous == result then throwError "vacuous witness mutation did not change the statement"
      let fake ← mkForallFVars args vacuous
      if (← generaliseLengthWitnessProblems fake binder).isEmpty then
        throwError "generalization map witness audit accepted a vacuous roundtrip"
      withLocalDeclD `extra (mkConst ``True) fun extra => do
        let conditional ← mkForallFVars (args.push extra) result
        if (← generaliseLengthWitnessProblems conditional binder).isEmpty then
          throwError "generalization map witness audit accepted an extra premise"
  let expected ← getConstInfo ``generaliseListLength
  let problems ← generaliseLengthStatementProblems expected.type
  unless problems.isEmpty do throwError "generalization length statement rejected: {problems}"
  forallTelescope expected.type fun args conclusion => do
    let inputLength ← mkAppM ``List.length #[args[3]!]
    let resultLength ← mkAppM ``List.length #[args[6]!]
    let reversed ← mkForallFVars args (← mkEq inputLength resultLength)
    if (← generaliseLengthStatementProblems reversed).isEmpty then
      throwError "generalization length audit accepted a reversed conclusion"
    withLocalDeclD `extra (mkConst ``True) fun extra => do
      let more ← mkForallFVars (args.push extra) conclusion
      if (← generaliseLengthStatementProblems more).isEmpty then
        throwError "generalization length audit accepted an extra premise"
    for swapped in #[true, false] do
      let call ← mkAppM ``generaliseListMap
        (if swapped then #[args[1]!, args[0]!, args[2]!, args[3]!]
         else #[args[0]!, args[1]!, args[2]!, args[3]!])
      let tail ← mkAppM ``Prod.mk #[if swapped then args[5]! else args[2]!, args[6]!]
      let triple ← mkAppM ``Prod.mk #[args[4]!, tail]
      let premise ← mkEq call triple
      withLocalDeclD `h premise fun h => do
        let changed ← mkForallFVars ((args.extract 0 7).push h) conclusion
        if (← generaliseLengthStatementProblems changed).isEmpty then
          throwError "generalization length audit accepted a changed premise"
    let tail ← mkAppM ``Prod.mk #[args[5]!, args[6]!]
    let triple ← mkAppM ``Prod.mk #[args[4]!, tail]
    let alias ← mkAppM ``producerAlias #[args[0]!, args[1]!, args[2]!, args[3]!]
    let direct ← mkAppM ``generaliseListMap #[args[0]!, args[1]!, args[2]!, args[3]!]
    let wrapped ← mkAppM ``id #[direct]
    for producer in #[alias, wrapped] do
      withLocalDeclD `h (← mkEq producer triple) fun h => do
        let changed ← mkForallFVars ((args.extract 0 7).push h) conclusion
        if (← generaliseLengthStatementProblems changed).isEmpty then
          throwError "generalization length audit accepted an indirect producer"
