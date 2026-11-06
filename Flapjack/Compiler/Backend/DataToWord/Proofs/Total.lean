import Flapjack.Compiler.Backend.DataToWord.Control
import Flapjack.Compiler.Backend.DataToWord.Stubs
import Flapjack.Compiler.Backend.BviToData.Proofs.Total

/-! Totality of the executed 64-bit data-to-word traversal. -/
namespace Flapjack.Compiler.Backend.DataToWord

set_option maxHeartbeats 1200000 in
/-- Every data-language program has a result in the executed 64-bit
traversal, including recursive handlers and both conditional branches.
This Flapjack totality property is not a HOL compiler-equivalence theorem. -/
theorem compileControl64_succeeds (conf : Config) (secn label : Nat) (program : DataLang.Prog) :
    ∃ result, compileControl? (width := 64) conf secn label program = some result := by
  fun_induction compileControl? (width := 64) conf secn label program <;> simp_all <;> repeat' split <;> simp_all
  case case6 l x y ihx ihy =>
    obtain ⟨a, b, hx⟩ := ihx
    obtain ⟨c, d, hy⟩ := ihy b
    simp [hx, hy]
  case case7 l n x y ihx ihy =>
    obtain ⟨a, b, hx⟩ := ihx
    obtain ⟨c, d, hy⟩ := ihy b
    simp [hx, hy]
  case case175 l ns names target args n handler ih =>
    obtain ⟨a, b, h⟩ := ih
    simp [h]

/-- The map used by configured word lowering succeeds for every list of
data-language functions at the 64-bit target width. -/
theorem compilePrograms64_succeeds (conf : Config) (programs : List (Nat × Nat × DataLang.Prog)) :
    ∃ result, (programs.mapM fun (name, args, body) => do
      let (body, _) ← compileControl? (width := 64) conf name 2 body
      pure (name, args + 1, body)) = some result := by
  induction programs with
  | nil => exact ⟨[], rfl⟩
  | cons entry rest ih =>
    obtain ⟨name, args, body⟩ := entry
    obtain ⟨⟨compiled, next⟩, run⟩ := compileControl64_succeeds conf name 2 body
    obtain ⟨tail, tailRun⟩ := ih
    exact ⟨(name, args + 1, compiled) :: tail, by
      simp only [List.mapM_cons, run, tailRun]
      rfl⟩

/-- The combined bounded BVI-to-data and executed data-to-word traversal
used by the configured 64-bit driver always produces its list of functions. -/
theorem compileBviPrograms64_succeeds (fuel : Nat) (conf : Config)
    (programs : List (Nat × Nat × Bvi.Exp)) :
    ∃ result, (programs.mapM fun (name, args, body) => do
      let body ← BviToData.compileExpBounded fuel args body
      let (body, _) ← compileControl? (width := 64) conf name 2 body
      pure (name, args + 1, body)) = some result := by
  induction programs with
  | nil => exact ⟨[], rfl⟩
  | cons entry rest ih =>
    obtain ⟨name, args, body⟩ := entry
    obtain ⟨data, dataRun⟩ := BviToData.compileExpBounded_succeeds fuel args body
    obtain ⟨⟨compiled, next⟩, wordRun⟩ := compileControl64_succeeds conf name 2 data
    obtain ⟨tail, tailRun⟩ := ih
    exact ⟨(name, args + 1, compiled) :: tail, by
      simp only [List.mapM_cons, dataRun, tailRun]
      simp [wordRun]⟩

set_option maxHeartbeats 1200000 in
/-- The fixed runtime-stub prefix is available for every 64-bit data
configuration. This proves totality of the executable lookup, not equality
with the complete HOL stub table. -/
theorem fixedStubs64_succeeds (conf : Config) : ∃ result, fixedStubs? (width := 64) conf = some result := by
  cases h : conf.hasLongdiv <;> simp [h, Flapjack.wordNumStubs, Flapjack.stackNumStubs,
    fixedStubs?, compileConfiguredStub?, compileStub?, fromListLocation, fromList1Location,
    refByteLocation, refArrayLocation, replicateLocation, anyArithLocation, addLocation, subLocation,
    mulLocation, divLocation, modLocation, compare1Location, compareLocation, equal1Location, equalLocation,
    longDiv1Location, longDivLocation, installLocation, installCodeLocation, installDataLocation,
    appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation, unusedLocation,
    stringCmpLoopLocation, memCopyLocation, byteCopyLocation, byteCopyAddLocation, byteCopySubLocation,
    byteCopyNewLocation, dummyLocation] <;> repeat' split <;> simp_all

end Flapjack.Compiler.Backend.DataToWord
