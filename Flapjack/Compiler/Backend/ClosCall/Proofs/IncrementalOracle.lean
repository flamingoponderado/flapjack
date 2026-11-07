import Flapjack.Compiler.Backend.ClosCall.Proofs.Total
import Flapjack.Compiler.Backend.BackendProps.StateCompiler
import Flapjack.Compiler.Backend.Semantics.ClosSem.State

/-! Incremental direct-call compiler and oracle adapters. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosSem BackendProps

/-- A total view of the executed incremental direct-call step. The fallback
is unreachable by `compileIncFuel_succeeds`. This bounded Lean definition
is not tagged as HOL's unbounded `compile_inc`. -/
def compileIncFuelTotal (fuel : Nat) (known : NumSet) (program : ClosSem.Program) :
    NumSet × ClosSem.Program :=
  (compileIncFuel? fuel known program).getD (known, program)

/-- The total view returns exactly the production adapter's result. -/
theorem compileIncFuel_eq_total (fuel : Nat) (known : NumSet) (program : ClosSem.Program) :
    compileIncFuel? fuel known program = some (compileIncFuelTotal fuel known program) := by
  obtain ⟨result, run⟩ := compileIncFuel_succeeds fuel known program
  simp [compileIncFuelTotal, run]

/-- The transformed oracle uses the same incremental step as production and
retains the downstream configuration in every entry. -/
def compileIncFuelOracle {C : Type} (fuel : Nat) (oracle : ClosSem.CompileOracle (NumSet × C)) :
    ClosSem.CompileOracle C :=
  stateCo (compileIncFuelTotal fuel) oracle

/-- The transformed callback runs the same incremental step before the
downstream compiler and threads its updated known-location set. -/
def compileIncFuelCallback {C : Type} (fuel : Nat) (compiler : ClosSem.Compiler C) :
    ClosSem.Compiler (NumSet × C) :=
  stateCc (compileIncFuelTotal fuel) compiler

/-- Each transformed oracle entry agrees with a successful production
incremental pass over the corresponding source entry. -/
theorem compileIncFuelOracle_entry {C : Type} (fuel : Nat) (oracle : ClosSem.CompileOracle (NumSet × C))
    (index : Nat) :
    ∃ nextKnown,
      compileIncFuel? fuel (oracle index).1.1 (oracle index).2 =
        some (nextKnown, (compileIncFuelOracle fuel oracle index).2) ∧
      (compileIncFuelOracle fuel oracle index).1 = (oracle index).1.2 := by
  refine ⟨(compileIncFuelTotal fuel (oracle index).1.1 (oracle index).2).1, ?_, rfl⟩
  simpa [compileIncFuelOracle, stateCo] using compileIncFuel_eq_total fuel (oracle index).1.1 (oracle index).2

/-- Consuming oracle entries commutes with the incremental transformation. -/
theorem compileIncFuelOracle_shift {C : Type} (fuel offset : Nat)
    (oracle : ClosSem.CompileOracle (NumSet × C)) :
    compileIncFuelOracle fuel (fun index => oracle (index + offset)) =
      fun index => compileIncFuelOracle fuel oracle (index + offset) := by
  rfl

/-- A successful source callback exposes the matching target compilation and
the new direct-call state computed by the production adapter. -/
theorem compileIncFuelCallback_success {C : Type} (fuel : Nat) (compiler : ClosSem.Compiler C)
    (known : NumSet) (config : C) (program : ClosSem.Program)
    (bytes : List (BitVec 8)) (data : List (BitVec 64)) (nextKnown : NumSet) (nextConfig : C)
    (run : compileIncFuelCallback fuel compiler (known, config) program =
      some (bytes, data, (nextKnown, nextConfig))) :
    ∃ converted,
      compileIncFuel? fuel known program = some (nextKnown, converted) ∧
      compiler config converted = some (bytes, data, nextConfig) := by
  have inc := compileIncFuel_eq_total fuel known program
  cases h : compileIncFuelTotal fuel known program with
  | mk computed converted =>
    simp only [h] at inc
    unfold compileIncFuelCallback stateCc at run
    simp only [h] at run
    cases compiled : compiler config converted with
    | none => simp [compiled] at run
    | some result =>
      rcases result with ⟨actualBytes, actualData, actualConfig⟩
      simp only [compiled, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl, rfl⟩ := run
      exact ⟨converted, inc, compiled⟩

/-- When the source callback's next configuration agrees with the next
source oracle entry, the corresponding target callback succeeds on the
transformed oracle entry and agrees with the next target configuration.
This is callback coherence only; code freshness and evaluation simulation
remain separate obligations. -/
theorem compileIncFuelOracle_callback_head {C : Type} (fuel : Nat) (compiler : ClosSem.Compiler C)
    (oracle : ClosSem.CompileOracle (NumSet × C)) (index : Nat)
    (bytes : List (BitVec 8)) (data : List (BitVec 64)) (nextKnown : NumSet) (nextConfig : C)
    (run : compileIncFuelCallback fuel compiler (oracle index).1 (oracle index).2 =
      some (bytes, data, (nextKnown, nextConfig)))
    (next : (oracle (index + 1)).1 = (nextKnown, nextConfig)) :
    compiler (compileIncFuelOracle fuel oracle index).1 (compileIncFuelOracle fuel oracle index).2 =
      some (bytes, data, (compileIncFuelOracle fuel oracle (index + 1)).1) ∧
    ∃ converted, compileIncFuel? fuel (oracle index).1.1 (oracle index).2 = some (nextKnown, converted) ∧
      converted = (compileIncFuelOracle fuel oracle index).2 := by
  have run' : compileIncFuelCallback fuel compiler ((oracle index).1.1, (oracle index).1.2)
      (oracle index).2 = some (bytes, data, (nextKnown, nextConfig)) := by simpa using run
  obtain ⟨converted, inc, compiled⟩ := compileIncFuelCallback_success fuel compiler
    (oracle index).1.1 (oracle index).1.2 (oracle index).2 bytes data nextKnown nextConfig run'
  obtain ⟨expectedKnown, oracleRun, configEq⟩ := compileIncFuelOracle_entry fuel oracle index
  rw [inc] at oracleRun
  have convertedEq : converted = (compileIncFuelOracle fuel oracle index).2 := by
    exact (Prod.mk.inj (Option.some.inj oracleRun)).2
  refine ⟨?_, converted, inc, convertedEq⟩
  rw [configEq, ← convertedEq]
  have nextConfigEq : (compileIncFuelOracle fuel oracle (index + 1)).1 = nextConfig := by
    simp [compileIncFuelOracle, stateCo, next]
  rw [nextConfigEq]
  exact compiled

end Flapjack.Compiler.Backend.ClosCall
