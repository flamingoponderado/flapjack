module

public import Flapjack.Compiler.Backend.ClosKnown.Compile

@[expose] public section

/-! Length preservation for the complete known-function pass. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- The complete known-function compiler preserves program length. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "compile_LENGTH"]
theorem compile_length (config : Option Config) (input : List Exp)
    (next : Option Config) (output : List Exp)
    (run : compile config input = (next, output)) : output.length = input.length := by
  cases config with
  | none =>
    simp [compile] at run
    obtain ⟨_, rfl⟩ := run
    rfl
  | some c =>
    cases h : knownListTotal c (ClosFvs.compile input) [] .ln with
    | mk result globals =>
      have length := knownListTotal_length_eq c (ClosFvs.compile input) [] .ln result globals h
      simp only [compile, h, Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      simpa [ClosLetop.compileList_length, ClosTicks.removeList_length,
        ClosFvs.compile, ClosFvs.removeList_length] using length

end Flapjack.Compiler.Backend.ClosKnown
