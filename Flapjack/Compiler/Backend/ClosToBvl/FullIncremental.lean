import Flapjack.Compiler.Backend.ClosToBvl.Config
import Flapjack.Compiler.Backend.ClosToBvl.SourceInc
import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
import Flapjack.Compiler.Backend.ClosNumber
import Flapjack.Compiler.Backend.ClosKnown.Compile
import Flapjack.Compiler.Backend.ClosCall.Compile
import Flapjack.Compiler.Backend.ClosAnnotate.Shift

/-! Source-shaped incremental composition of the closure-to-BVL passes. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Thread the closure configuration through every original incremental pass. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "clos_to_bvl_compile_inc_def"]
noncomputable def closToBvlCompileInc (config : Config)
    (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    Config × List (Nat × Nat × Bvl.Exp) :=
  let program := ClosMti.condCompileInc config.doMti config.maxApp program
  let (next, program) := ClosNumber.ignoreTable ClosNumber.compileInc config.nextLoc program
  let config := { config with nextLoc := next }
  let approximations := ClosKnown.optionValApproxSpt config.knownConf
  let (approximations, program) :=
    ClosKnown.knownCompileInc (ClosKnown.knownStaticConf config.knownConf) approximations program
  let config := { config with knownConf := ClosKnown.optionUpdValSpt approximations config.knownConf }
  let (known, program) := ClosCall.condCallCompileInc config.doCall config.callState.1 program
  let config := { config with callState := (known, []) }
  let program := ClosAnnotate.compileInc program
  let program := compileInc config.maxApp program
  (config, program)

end Flapjack.Compiler.Backend.ClosToBvl
