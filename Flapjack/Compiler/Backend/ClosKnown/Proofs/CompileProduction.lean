import Flapjack.Compiler.Backend.ClosKnown.Compile
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Production
import Flapjack.Compiler.Backend.ClosTicks.Proofs.Production
import Flapjack.Compiler.Backend.ClosLetop.Proofs.Production

/-! Executable agreement for the source closure optimizer. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open Flapjack.Compiler.Backend

/-- The executable combined tick and let-operation traversal has the same
result as the two source-shaped traversals in sequence. This Lean-side
composition has no standalone HOL declaration. -/
theorem ticks_letop_bounded (fuel : Nat) (program : List ClosLang.Exp) :
    (program.mapM fun e => do
      let e ← ClosTicks.removeBounded fuel e
      ClosLetop.compileBounded fuel e) =
      some (ClosLetop.compileList (ClosTicks.removeList program)) := by
  induction program with
  | nil => rfl
  | cons head tail ih =>
    simp only [ClosTicks.removeBounded_eq_source, ClosLetop.compileBounded_eq_source, bind, Option.bind] at ih
    simp only [List.mapM_cons]
    rw [ClosTicks.removeBounded_eq_source]
    simp only [bind, Option.bind, ClosLetop.compileBounded_eq_source]
    simp only [ClosTicks.removeBounded_eq_source]
    rw [ih]
    rfl

/-- The enabled executable known-function pipeline returns exactly the
source-shaped free-variable, known, tick and let-operation outputs. This
Lean-side production agreement has no standalone HOL declaration. -/
theorem known_compileFuel_eq (fuel : Nat) (config : ClosKnown.Config) (program : List ClosLang.Exp)
    (optimized : List (ClosLang.Exp × ValApprox)) (globals : Spt ValApprox)
    (knownRun : ClosKnown.knownListTotal config (ClosFvs.compile program) [] .ln = (optimized, globals)) :
    ClosKnown.compileFuel fuel (some config) program =
      some (some { config with valApproxSpt := globals },
        ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) := by
  simp only [ClosKnown.compileFuel, ClosFvs.compileBounded_eq_source, ClosKnown.knownListBounded,
    knownRun, bind, Option.bind]
  have mapEq : (optimized.mapM fun entry => do
      let e ← ClosTicks.removeBounded fuel entry.1
      ClosLetop.compileBounded fuel e) =
      some (ClosLetop.compileList (ClosTicks.removeList (optimized.map Prod.fst))) := by
    simpa only [List.mapM_map, Function.comp_def] using ticks_letop_bounded fuel (optimized.map Prod.fst)
  simp only [bind, Option.bind] at mapEq
  rw [mapEq]
  rfl

/-- For every fuel and both configuration branches, the executed optimizer
returns the source traversal. This Lean-side production agreement has no
standalone HOL declaration. -/
theorem compileFuel_eq_source (fuel : Nat) (config : Option Config) (program : List ClosLang.Exp) :
    compileFuel fuel config program = some (compile config program) := by
  cases config with
  | none => rfl
  | some c =>
    cases run : knownListTotal c (ClosFvs.compile program) [] .ln with
    | mk optimized globals =>
      simpa [compile, run] using known_compileFuel_eq fuel c program optimized globals run

/-- For every fuel and incremental input, the executed driver agrees with
the source optimizer after applying the source static-configuration and
configuration-update operations. This is Lean-side production agreement. -/
theorem compileIncFuel_eq_source (fuel : Nat) (config : Option Config)
    (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    compileIncFuel fuel config program = some
      ((fun pair => (optionUpdValSpt pair.1 config, pair.2))
        (knownCompileInc (knownStaticConf config) (optionValApproxSpt config) program)) := by
  cases config with
  | none => rfl
  | some c =>
    simp only [compileIncFuel, knownStaticConf, knownCompileInc, ClosFvs.compileInc,
      compileInc, ClosTicks.compileInc, ClosLetop.compileInc,
      ClosFvs.compileBounded_eq_source, bind, Option.bind]
    cases run : knownListTotal (resetInlineFactor { resetInlineFactor c with valApproxSpt := .ln })
        (ClosFvs.compile program.1) [] (optionValApproxSpt (some c)) with
    | mk eas globals =>
      have mapEq := ticks_letop_bounded fuel (eas.map Prod.fst)
      simp only [bind, Option.bind] at mapEq
      rw [mapEq]
      rfl

end Flapjack.Compiler.Backend.ClosKnown
