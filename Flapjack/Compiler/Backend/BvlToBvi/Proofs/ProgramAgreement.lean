import Flapjack.Compiler.Backend.BvlToBvi.SourceProgram
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.SourceAgreement

/-! Agreement of incremental compilation with the source auxiliary tree. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

/-- A labeled executable conversion is the flattening of source conversion. -/
theorem compileSingleFuel_eq_flattened (fuel optFuel n : Nat) (program : Nat × Nat × Bvl.Exp) :
    compileSingleFuel fuel optFuel n program =
      some (appListAppend (compileSingleSource n program).1, (compileSingleSource n program).2) := by
  rcases program with ⟨name, args, body⟩
  rcases h : compileSingSource n body with ⟨converted, aux, next⟩
  have run := compileSingleFuel_eq_source_all fuel optFuel n name args body
  simp only [h] at run
  simp only [compileSingleSource, h, appListAppend_smartAppend]
  simpa [appListAppend, appendAux] using run

/-- Executed labeled-program traversal is the flattening of the original
tree and retains the same fresh-name counter for every pair of fuel values. -/
theorem compileProgramsFuel_eq_flattened (fuel optFuel n : Nat)
    (programs : List (Nat × Nat × Bvl.Exp)) :
    compileProgramsFuel fuel optFuel n programs =
      some (appListAppend (compileProgramsSource n programs).1, (compileProgramsSource n programs).2) := by
  induction programs generalizing n with
  | nil => simp [compileProgramsFuel, compileProgramsSource, appListAppend, appendAux]
  | cons program programs ih =>
    rcases h : compileSingleSource n program with ⟨code, next⟩
    rcases rest : compileProgramsSource next programs with ⟨restCode, final⟩
    have firstRun := compileSingleFuel_eq_flattened fuel optFuel n program
    have restRun := ih next
    simp only [h] at firstRun
    simp only [rest] at restRun
    simp [compileProgramsFuel, compileProgramsSource, h, rest, firstRun, restRun,
      appListAppend_smartAppend]

/-- Incremental executable output agrees exactly with the source definition,
including code order and the returned fresh-name counter. -/
theorem compileIncFuel_eq_source (fuel optFuel n : Nat)
    (programs : List (Nat × Nat × Bvl.Exp)) :
    compileIncFuel fuel optFuel n programs = some (compileIncSource n programs) := by
  rcases h : compileProgramsSource n programs with ⟨code, next⟩
  have run := compileProgramsFuel_eq_flattened fuel optFuel n programs
  simp only [h] at run
  simp [compileIncFuel, compileIncSource, h, run]

end Flapjack.Compiler.Backend.BvlToBvi
