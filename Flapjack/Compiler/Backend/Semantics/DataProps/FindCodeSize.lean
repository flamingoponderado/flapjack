module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control

@[expose] public section

/-! Independence of `findCode`'s frame-size component from the frame-size map. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack

/-- Replacing the frame-size map only changes the frame size reported by
`findCode`, never the arguments or the body it returns. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "find_code_upto_size"]
theorem findCode_size_upto {α β γ : Type} (dest : Option Nat) (args : List Value)
    (code : Spt (Nat × α)) (sizes : Spt β) (otherSizes : Spt γ)
    (found : Option (List Value × α × Option β))
    (success : findCode dest args code sizes = found) :
    ∃ otherSize : Option γ,
      findCode dest args code otherSizes =
        found.map (fun (args, exp, _size) => (args, exp, otherSize)) := by
  subst success
  cases dest with
  | some label =>
    cases looked : sptLookup label code with
    | none => exact ⟨none, by simp [findCode, looked]⟩
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      by_cases arityOk : args.length = arity
      · exact ⟨sptLookup label otherSizes, by simp [findCode, looked, arityOk]⟩
      · exact ⟨none, by simp [findCode, looked, arityOk]⟩
  | none =>
    by_cases empty : args.isEmpty
    · exact ⟨none, by simp [findCode, empty]⟩
    · cases last : holLast args with
      | codePtr label =>
        cases looked : sptLookup label code with
        | none => exact ⟨none, by simp [findCode, empty, last, looked]⟩
        | some entry =>
          obtain ⟨arity, body⟩ := entry
          by_cases arityOk : args.length = arity + 1
          · exact ⟨sptLookup label otherSizes, by simp [findCode, empty, last, looked, arityOk]⟩
          · exact ⟨none, by simp [findCode, empty, last, looked, arityOk]⟩
      | number _ => exact ⟨none, by simp [findCode, empty, last]⟩
      | word64 _ => exact ⟨none, by simp [findCode, empty, last]⟩
      | block _ _ _ => exact ⟨none, by simp [findCode, empty, last]⟩
      | refPtr _ _ => exact ⟨none, by simp [findCode, empty, last]⟩

end Flapjack.Compiler.Backend.DataSem
