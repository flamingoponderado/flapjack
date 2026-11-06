import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Compiler.Backend.BackendCommon.BoolTags
import Flapjack.Compiler.Backend.BackendCommon.ConstructorTags

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

/-- Whether a tagged nonempty block is a full or partial closure. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "isClos_def"]
def isClosure {α : Type} (tag : Nat) (values : List α) : Prop :=
  (tag = 30 ∨ tag = 31) ∧ values ≠ []

end Flapjack.Compiler.Backend.BvlSem
