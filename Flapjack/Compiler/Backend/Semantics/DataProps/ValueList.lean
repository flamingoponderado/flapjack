module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Value

@[expose] public section

/-! Shape of a successful list decoding. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.Compiler.Backend.BackendCommon

/-- A successful non-empty decode exposes the cons block it came from. HOL binds
an extra timestamp variable `ts` that occurs in neither the premise nor the
conclusion, so it is omitted here. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "v_to_list_SOME_CONS_IMP"]
theorem valueToList_cons {v x : Value} {xs : List Value}
    (read : valueToList v = some (x :: xs)) :
    ∃ ts ys, v = .block ts BackendCommon.consTag [x, ys] ∧ valueToList ys = some xs := by
  cases v with
  | number n => simp [valueToList] at read
  | word64 w => simp [valueToList] at read
  | codePtr label => simp [valueToList] at read
  | refPtr b n => simp [valueToList] at read
  | block ts tag payload =>
    cases payload with
    | nil => simp [valueToList] at read
    | cons head rest =>
      cases rest with
      | nil => simp [valueToList] at read
      | cons second more =>
        cases more with
        | nil =>
          simp only [valueToList] at read
          split at read
          · rename_i htag
            cases inner : valueToList second with
            | none => simp [inner] at read
            | some ys =>
              simp [inner] at read
              obtain ⟨rfl, rfl⟩ := read
              refine ⟨ts, second, ?_, inner⟩
              rw [htag]
          · simp at read
        | cons _ _ => simp [valueToList] at read

end Flapjack.Compiler.Backend.DataSem
