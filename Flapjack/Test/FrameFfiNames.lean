import Flapjack.RiscV.LabToTargetRoute

namespace Flapjack.Test.FrameFfiNames

open Flapjack.RiscV Flapjack.Compiler.Backend

private def external (name : String) : HolFfiName :=
  .extCall (Basis.Pure.MlString.ofString name)

-- Kernel proof of the frame/code ordinal boundary, including arbitrary names.
example (config : LabToTarget.Config) (names : List String)
    (accepted : frameFfiNamesAgree config names = true) :
    ∃ actual, config.ffiNames = some actual ∧
      actual.take names.length = names.map external ∧
      (actual.drop names.length).all (fun name => match name with
        | .sharedMem _ => true
        | .extCall _ => false) = true := by
  cases h : config.ffiNames with
  | none => simp [frameFfiNamesAgree, h] at accepted
  | some actual =>
      simp only [frameFfiNamesAgree, h, Bool.and_eq_true, beq_iff_eq] at accepted
      exact ⟨actual, rfl, accepted.1, accepted.2⟩

example : frameFfiNamesAgree {riscvLabConf with ffiNames := some [external "write", external "read"]} ["write", "read"] = true := rfl
example : frameFfiNamesAgree {riscvLabConf with ffiNames := some [external "read", external "write"]} ["write", "read"] = false := rfl
example : frameFfiNamesAgree {riscvLabConf with ffiNames := some [external "write", external "read"]} ["write"] = false := rfl
example : frameFfiNamesAgree {riscvLabConf with ffiNames := some [external "write"]} ["write", "read"] = false := rfl
example : frameFfiNamesAgree riscvLabConf [] = false := rfl
example : frameFfiNamesAgree {riscvLabConf with ffiNames := some []} [] = true := rfl
example : frameFfiNamesAgree {riscvLabConf with ffiNames := some [external "write", .sharedMem .mappedRead]} ["write"] = true := rfl
example : frameFfiNamesAgree {riscvLabConf with ffiNames := some [.sharedMem .mappedRead, external "write"]} ["write"] = false := rfl

end Flapjack.Test.FrameFfiNames
