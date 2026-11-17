module

public meta import Flapjack.HolRef.GeneraliseLengthAudit
public import Flapjack.Compiler.Inference.InferProps.Generalise

@[expose] public section

open Lean Meta Flapjack Flapjack.Compiler.Inference Flapjack.Compiler.Inference.Infer.Generalise
  Flapjack.Compiler.Inference.InferProps.Generalise

private abbrev producerAlias := generaliseListMap

run_meta do
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
