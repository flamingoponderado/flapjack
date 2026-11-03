import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileProduction
import Flapjack.Compiler.Backend.ClosFvs.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosTicks.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosLetop.Proofs.CodeLocations

/-! Location accounting through the executed closure optimizer. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps

/-- The executed bounded cleanup stages retain exactly the locations emitted
by known-function traversal. This is Lean-side pass composition. -/
theorem ticksLetop_bounded_codeLocations (fuel : Nat) (program output : List ClosLang.Exp)
    (run : (program.mapM fun e => do
      let e ← ClosTicks.removeBounded fuel e
      ClosLetop.compileBounded fuel e) = some output) :
    codeLocations output = codeLocations program := by
  have same := Option.some.inj ((ticks_letop_bounded fuel program).symm.trans run)
  rw [← same, ClosLetop.compileList_codeLocations, ClosTicks.removeList_codeLocations]

/-- With optimization enabled, the executable driver retains the exact
location sequence emitted by the source-shaped known traversal. This is
Lean-side production composition, not a separate HOL declaration. -/
theorem known_compileFuel_codeLocations (fuel : Nat) (config : Config) (program : List ClosLang.Exp)
    (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (outputConfig : Option Config) (output : List ClosLang.Exp)
    (knownRun : knownListTotal config (ClosFvs.compile program) [] .ln = (optimized, globals))
    (run : compileFuel fuel (some config) program = some (outputConfig, output)) :
    codeLocations output = codeLocations (optimized.map Prod.fst) := by
  have same := Option.some.inj ((known_compileFuel_eq fuel config program optimized globals knownRun).symm.trans run)
  cases same
  rw [ClosLetop.compileList_codeLocations, ClosTicks.removeList_codeLocations]

end Flapjack.Compiler.Backend.ClosKnown
