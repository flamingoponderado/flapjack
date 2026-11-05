import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Code

/-! Code-table preservation for the data simulation fragment with calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack DataSem

/-- A successful direct or indirect lookup selects a body from the source code tree. -/
theorem findCode_body_lookup (dest : Option Nat) (values : List DataSem.Value)
    (code : Spt (Nat × DataLang.Prog)) (sizes : Spt Nat)
    (args : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (found : findCode dest values code sizes = some (args, body, size)) :
    ∃ label arity, sptLookup label code = some (arity, body) := by
  cases dest with
  | some label =>
    cases entry : sptLookup label code with
    | none => simp [findCode, entry] at found
    | some pair =>
      obtain ⟨arity, prog⟩ := pair
      by_cases length : values.length = arity
      · simp [findCode, entry, length] at found
        obtain ⟨_, rfl, _⟩ := found
        exact ⟨label, arity, entry⟩
      · simp [findCode, entry, length] at found
  | none =>
    by_cases empty : values.isEmpty
    · simp [findCode, empty] at found
    · cases last : holLast values with
      | number n => simp [findCode, empty, last] at found
      | word64 w => simp [findCode, empty, last] at found
      | block ts tag fields => simp [findCode, empty, last] at found
      | refPtr bit ptr => simp [findCode, empty, last] at found
      | codePtr label =>
        cases entry : sptLookup label code with
        | none => simp [findCode, empty, last, entry] at found
        | some pair =>
          obtain ⟨arity, prog⟩ := pair
          by_cases length : values.length = arity + 1
          · simp [findCode, empty, last, entry, length] at found
            obtain ⟨_, rfl, _⟩ := found
            exact ⟨label, arity, entry⟩
          · simp [findCode, empty, last, entry, length] at found

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
