module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.Compiler.Backend.BackendCommon.BoolTags
public import Flapjack.Compiler.Backend.BackendCommon.ConstructorTags

@[expose] public section

/-! BVL runtime values and their list representation. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.Compiler.Backend.BackendCommon

/-- The original BVL reference-cell carrier, generic in the stored value. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "ref"]
inductive Ref (α : Type) where
  | valueArray : List α → Ref α
  | byteArray : Bool → List (BitVec 8) → Ref α
  | thunk : AstHOL.ThunkMode → α → Ref α
  | mutBlock : Nat → Bool → List α → α → List α → Ref α
  deriving BEq, Repr

/-- The original BVL value carrier. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "v"]
inductive Value where
  | number : Int → Value
  | word64 : BitVec 64 → Value
  | block : Nat → List Value → Value
  | codePtr : Nat → Value
  | refPtr : Bool → Nat → Value
  deriving BEq, Repr

/-- The original Boolean value encoding. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "Boolv_def"]
def boolValue (b : Bool) : Value := .block (boolToTag b) []

/-- The original unit value encoding. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "Unit_def"]
def unitValue : Value := .block 0 []

/-- Decode the original nil and cons block representation of a list. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "v_to_list_def"]
def valueToList : Value → Option (List Value)
  | .block tag [] => if tag = nilTag then some [] else none
  | .block tag [head, tail] =>
      if tag = consTag then (valueToList tail).map (head :: ·) else none
  | _ => none
termination_by value => sizeOf value

/-- Encode a list with the original nil and cons block tags. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "list_to_v_def"]
def listToValue : List Value → Value
  | [] => .block nilTag []
  | v :: vs => .block consTag [v, listToValue vs]

/-- Flapjack helper: decoding a constructed list recovers its elements. -/
theorem valueToList_listToValue (values : List Value) :
    valueToList (listToValue values) = some values := by
  induction values with
  | nil => simp [valueToList, listToValue]
  | cons v vs ih => simp [valueToList, listToValue, ih]

/-- Flapjack inverse used by compiler proofs: successful decoding recovers the
canonical list encoding. HOL unfolds these list functions in those proofs. -/
theorem listToValue_valueToList (value : Value) (values : List Value)
    (decode : valueToList value = some values) : listToValue values = value := by
  cases value with
  | block tag fields =>
    cases fields with
    | nil =>
      simp only [valueToList] at decode
      split at decode
      · rename_i equal
        simp only [Option.some.injEq] at decode
        subst values
        subst tag
        rfl
      · contradiction
    | cons head tail =>
      cases tail with
      | nil => simp [valueToList] at decode
      | cons next rest =>
        cases rest with
        | cons other rest => simp [valueToList] at decode
        | nil =>
          simp only [valueToList] at decode
          split at decode
          · rename_i equal
            cases nextDecode : valueToList next with
            | none => simp [nextDecode] at decode
            | some vs =>
              simp [nextDecode] at decode
              subst values
              have ih := listToValue_valueToList next vs nextDecode
              subst tag
              simp [listToValue, ih]
          · contradiction
  | _ => simp [valueToList] at decode
termination_by sizeOf value

/-- Whether a tagged nonempty block is a full or partial closure. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "isClos_def"]
def isClosure {α : Type} (tag : Nat) (values : List α) : Prop :=
  (tag = 30 ∨ tag = 31) ∧ values ≠ []

end Flapjack.Compiler.Backend.BvlSem
