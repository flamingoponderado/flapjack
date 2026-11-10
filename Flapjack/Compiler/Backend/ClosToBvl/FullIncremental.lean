module

public import Flapjack.Compiler.Backend.ClosToBvl.Config
public import Flapjack.Compiler.Backend.ClosToBvl.SourceInc
public import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
public import Flapjack.Compiler.Backend.ClosNumber
public import Flapjack.Compiler.Backend.ClosKnown.Compile
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Compiler.Backend.ClosAnnotate.Original
public import Flapjack.Compiler.Backend.ClosAnnotate.Shift


@[expose] public section

/-! Source-shaped incremental composition of the closure-to-BVL passes. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Thread the closure configuration through the original incremental passes. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "clos_to_bvl_compile_inc_def"]
noncomputable def closToBvlCompileInc (config : Config)
    (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    Config × List (Nat × Nat × Bvl.Exp) :=
  let program := ClosMti.condCompileInc config.doMti config.maxApp program
  let (next, program) := ClosNumber.ignoreTable ClosNumber.compileInc config.nextLoc program
  let config := { config with nextLoc := next }
  let approximations := ClosKnown.optionValApproxSpt config.knownConf
  let (approximations, program) :=
    ClosKnown.knownCompileIncSource (ClosKnown.knownStaticConf config.knownConf) approximations program
  let config := { config with knownConf := ClosKnown.optionUpdValSpt approximations config.knownConf }
  let (known, program) := ClosCall.condCallCompileInc config.doCall config.callState.1 program
  let config := { config with callState := (known, []) }
  let program := ClosAnnotate.compileIncSource program
  let program := compileInc config.maxApp program
  (config, program)

end Flapjack.Compiler.Backend.ClosToBvl
