import Flapjack.Compiler.Backend.ClosKnown.Compile

/-! Agreement with the previous incremental optimizer interface. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- The source incremental traversal produces exactly the same checked result
as the previous executable composition, for any fuel and program. This is
Flapjack-specific production-path agreement, not a separate HOL theorem. -/
theorem compileIncFuel_eq_previous (fuel : Nat) (config : Option Config)
    (program : List Exp × List (Nat × Nat × Exp)) :
    compileIncFuel fuel config program = (do
      let previousGlobals := optionValApproxSpt config
      match config with
      | none => pure (none, program)
      | some c =>
        let es ← program.1.mapM (ClosFvs.removeBounded fuel 0)
        let static := { resetInlineFactor c with valApproxSpt := .ln }
        let (es, globals) ← knownListBounded fuel static es [] previousGlobals
        let es ← es.mapM fun (e, _) => do
          let e ← ClosTicks.removeBounded fuel e
          ClosLetop.compileBounded fuel e
        pure (optionUpdValSpt globals config, (es, []))) := by
  cases config with
  | none => rfl
  | some c =>
    simp only [compileIncFuel, knownListBounded, compileInc, resetInlineFactor,
      optionValApproxSpt, optionUpdValSpt]
    simp [List.mapM_map, Function.comp_def]

end Flapjack.Compiler.Backend.ClosKnown
