import Flapjack.HolRef.JoinEnvLocalsAudit
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JoinEnvLocals

open Lean Meta Flapjack
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

private partial def changeBinder (e : Expr) (index : Nat)
    (change : Name → Expr → BinderInfo → Name × Expr × BinderInfo) : Expr :=
  match e with
  | .forallE name domain body bi =>
    if index == 0 then
      let (newName, newDomain, newInfo) := change name domain bi
      .forallE newName newDomain body newInfo
    else .forallE name domain (changeBinder body (index - 1) change) bi
  | .mdata md inner => .mdata md (changeBinder inner index change)
  | _ => e

run_meta do
  let targets := #[``joinEnvLocals, ``joinEnvLocals_insertOdd, ``joinEnvLocals_insertDestOdd]
  for target in targets do
    let problems ← joinEnvLocalsBundleProblems target
    unless problems.isEmpty do throwError "joined-local audit rejected {target}: {problems}"
  if (← joinEnvLocalsBundleProblems ``joinEnv).isEmpty then
    throwError "joined-local audit accepted the producer as a target"
  let .defnInfo definition ← getConstInfo ``joinEnvLocals
    | throwError "missing joined-local definition"
  lambdaTelescope definition.value fun args body => do
    let pair := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) args[1]!
    let empty := mkApp (mkConst ``List.nil [0]) pair
    let wrongBody ← mkAppM ``joinEnv #[args[3]!, empty]
    let wrongValue ← mkLambdaFVars args wrongBody
    if (← joinEnvLocalsWrapperProblems { definition with value := wrongValue }).isEmpty then
      throwError "joined-local audit accepted a wrapper that discards the word locals"
    let emptySource := mkApp (mkConst `Flapjack.Spt.ln) args[0]!
    let wrongSourceBody ← mkAppM ``joinEnv #[emptySource, body.getAppArgs.back!]
    let wrongSourceValue ← mkLambdaFVars args wrongSourceBody
    if (← joinEnvLocalsWrapperProblems { definition with value := wrongSourceValue }).isEmpty then
      throwError "joined-local audit accepted a wrapper that discards the source locals"
  for (name, destination) in #[(``joinEnvLocals_insertOdd, false),
      (``joinEnvLocals_insertDestOdd, true)] do
    let info ← getConstInfo name
    unless (← joinEnvLocalsTheoremProblems info.type destination).isEmpty do
      throwError "joined-local audit rejected the actual theorem {name}"
    let wrongInstance := changeBinder info.type 2 fun n _ b =>
      (n, mkApp (mkConst ``Nonempty [1]) (.bvar 0), b)
    let wrongOdd := changeBinder info.type (if destination then 9 else 7) fun n _ b =>
      (n, mkConst ``True, b)
    let wrongPayload := changeBinder info.type 1 fun n _ b => (n, .sort .zero, b)
    for altered in #[wrongInstance, wrongOdd, wrongPayload] do
      if (← joinEnvLocalsTheoremProblems altered destination).isEmpty then
        throwError "joined-local audit accepted a changed theorem binder"
    forallTelescope info.type fun args result => do
      let weakened ← mkForallFVars args (mkConst ``True)
      if (← joinEnvLocalsTheoremProblems weakened destination).isEmpty then
        throwError "joined-local audit accepted a weakened conclusion"
      withLocalDeclD `extra (mkConst ``True) fun extra => do
        let conditional ← mkForallFVars (args.push extra) result
        if (← joinEnvLocalsTheoremProblems conditional destination).isEmpty then
          throwError "joined-local audit accepted an added premise"
