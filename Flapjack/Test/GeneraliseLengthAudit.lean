import Flapjack.HolRef.GeneraliseLengthAudit
import Flapjack.Compiler.Inference.InferProps.Generalise

open Lean Meta Flapjack Flapjack.Compiler.Inference Flapjack.Compiler.Inference.Infer.Generalise
  Flapjack.Compiler.Inference.InferProps.Generalise

private abbrev producerAlias := generaliseListMap

run_meta do
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
