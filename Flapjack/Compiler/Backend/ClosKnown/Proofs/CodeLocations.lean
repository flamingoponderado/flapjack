import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileProduction
import Flapjack.Compiler.Backend.ClosKnown.Proofs.TraversalCodeBagTotal
import Flapjack.Compiler.Backend.ClosFvs.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosTicks.Proofs.CodeLocations
import Flapjack.Compiler.Backend.ClosLetop.Proofs.CodeLocations

/-! Location accounting through the executed closure optimizer. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps

/-- Source optimization cannot increase the multiplicity of any closure label. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "compile_code_locs_bag"]
theorem compile_codeLocationsBag (config outputConfig : Option Config) (program output : List ClosLang.Exp)
    (run : compile config program = (outputConfig, output)) :
    ∀ label, (codeLocations output).count label ≤ (codeLocations program).count label := by
  cases config with
  | none =>
    simp [compile] at run
    rcases run with ⟨rfl, rfl⟩
    intro label
    exact Nat.le_refl _
  | some c =>
    cases known : knownListTotal c (ClosFvs.compile program) [] .ln with
    | mk optimized globals =>
      simp [compile, known] at run
      rcases run with ⟨rfl, rfl⟩
      intro label
      have bound := TraversalCodeBag.knownCodeLocationsBag c (ClosFvs.compile program) [] .ln
        optimized globals known label
      simpa [ClosLetop.compileList_codeLocations, ClosTicks.removeList_codeLocations,
        ClosFvs.compile, ClosFvs.removeList_codeLocations] using bound

/-- The bounded executable optimizer inherits the source label-multiset bound. -/
theorem compileFuel_codeLocationsBag (fuel : Nat) (config outputConfig : Option Config)
    (program output : List ClosLang.Exp) (run : compileFuel fuel config program = some (outputConfig, output)) :
    ∀ label, (codeLocations output).count label ≤ (codeLocations program).count label := by
  have source := compileFuel_eq_source fuel config program
  rw [run] at source
  exact compile_codeLocationsBag config outputConfig program output (Option.some.inj source.symm)

end Flapjack.Compiler.Backend.ClosKnown
