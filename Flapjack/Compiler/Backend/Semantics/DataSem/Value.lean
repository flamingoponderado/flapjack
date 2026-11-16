module

public import Flapjack.Compiler.Backend.Semantics.BvlSem.Value

@[expose] public section

/-! Runtime values of the data-language semantics. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack.Compiler.Backend.BackendCommon

/-- Data-language values retain the allocation timestamp on blocks. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "v"]
inductive Value where
  | number : Int → Value
  | word64 : BitVec 64 → Value
  | block : Nat → Nat → List Value → Value
  | codePtr : Nat → Value
  | refPtr : Bool → Nat → Value
  deriving BEq, Repr

/-- The source Boolean block, whose timestamp is zero. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "Boolv_def"]
def boolValue (b : Bool) : Value := .block 0 (boolToTag b) []

/-- The source unit block, whose timestamp is zero. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "Unit_def"]
def unitValue : Value := .block 0 0 []

/-- Decode nil and cons blocks, ignoring their timestamps. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "v_to_list_def"]
def valueToList : Value → Option (List Value)
  | .block _ tag [] => if tag = nilTag then some [] else none
  | .block _ tag [head, tail] =>
      if tag = consTag then (valueToList tail).map (head :: ·) else none
  | _ => none
termination_by value => sizeOf value

/-- Exact HOL `v_to_list_SOME_NIL_IFF` (`dataPropsScript.sml:2238-2246`):
    decoding yields the empty list exactly on a nil block, at any timestamp. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "v_to_list_SOME_NIL_IFF"]
theorem valueToList_nil_iff {v : Value} :
    valueToList v = some [] ↔ ∃ ts, v = .block ts nilTag [] := by
  cases v with
  | number _ => simp [valueToList]
  | word64 _ => simp [valueToList]
  | block ts tag elems =>
    cases elems with
    | nil =>
      simp only [valueToList]
      constructor
      · intro h
        by_cases htag : tag = nilTag
        · exact ⟨ts, by simp [htag]⟩
        · simp [htag] at h
      · rintro ⟨ts', heq⟩
        cases heq
        simp
    | cons head tail =>
      cases tail with
      | nil =>
        constructor
        · intro h
          simp [valueToList] at h
        · rintro ⟨ts', heq⟩
          cases heq
      | cons head2 tail2 =>
        cases tail2 with
        | nil =>
          simp only [valueToList]
          constructor
          · intro h
            by_cases htag : tag = consTag
            · rw [if_pos htag] at h
              cases htl : valueToList head2 with
              | none => simp [htl] at h
              | some l => simp [htl] at h
            · rw [if_neg htag] at h
              simp at h
          · rintro ⟨ts', heq⟩
            cases heq
        | cons head3 tail3 =>
          constructor
          · intro h
            simp [valueToList] at h
          · rintro ⟨ts', heq⟩
            cases heq
  | codePtr _ => simp [valueToList]
  | refPtr _ _ => simp [valueToList]

end Flapjack.Compiler.Backend.DataSem
