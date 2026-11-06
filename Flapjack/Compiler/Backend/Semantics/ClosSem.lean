import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Compiler.Backend.BackendCommon.BoolTags
import Flapjack.Compiler.Backend.BackendCommon.ConstructorTags
import Flapjack.SemanticPrimitivesHOL.Operations

/-! Value-level operations of the closure-language semantics. Evaluation,
state, and installation are not yet ported in this module. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- The closure-language store payloads. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "ref"]
inductive Ref (α : Type) where
  | valueArray : List α → Ref α
  | byteArray : List (BitVec 8) → Ref α
  | thunk : ThunkMode → α → Ref α

/-- Values of the closure-language evaluator, including their captured
environments and recursive function bundles. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "v"]
inductive Value where
  | number : Int → Value
  | word64 : BitVec 64 → Value
  | block : Nat → List Value → Value
  | byteVector : List (BitVec 8) → Value
  | refPtr : Bool → Nat → Value
  | closure : Option Nat → List Value → List Value → Nat → ClosLang.Exp → Value
  | recclosure : Option Nat → List Value → List Value → List (Nat × ClosLang.Exp) → Nat → Value

/-- Out-of-range global indices are distinct from empty global slots. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "get_global_def"]
def getGlobal {α : Type} (n : Nat) (globals : List α) : Option α :=
  globals[n]?

/-- Closure-language Boolean values use the backend constructor tags. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "Boolv_def"]
def boolValue (b : Bool) : Value := .block (if b then trueTag else falseTag) []

/-- The nullary tuple is the unit value. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "Unit_def"]
def unitValue : Value := .block 0 []

/-- Decode closure-language lists, rejecting malformed blocks. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "v_to_list_def"]
def valueToList : Value → Option (List Value)
  | .block tag [] => if tag = nilTag then some [] else none
  | .block tag [head, tail] =>
    if tag = consTag then (valueToList tail).map (head :: ·) else none
  | _ => none
termination_by value => sizeOf value

/-- Encode a list as closure-language blocks. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "list_to_v_def"]
def listToValue : List Value → Value
  | [] => .block nilTag []
  | head :: tail => .block consTag [head, listToValue tail]

/-- Encoding followed by decoding recovers the original list. This helper
is used to reason about the closure representation of flat lists. -/
theorem valueToList_listToValue (values : List Value) :
    valueToList (listToValue values) = some values := by
  induction values with
  | nil => simp [listToValue, valueToList]
  | cons head tail ih => simp [listToValue, valueToList, ih]

mutual
/-- Compare closure-language values with HOL's closure and type-error cases. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "do_eq_def"]
def doEq (first second : Value) : EqResult :=
  match first, second with
  | .number a, .number b => .val (decide (a = b))
  | .word64 a, .word64 b => .val (decide (a = b))
  | .block a xs, .block b ys =>
    if a = b ∧ xs.length = ys.length then doEqList xs ys else .val false
  | .byteVector a, .byteVector b => .val (decide (a = b))
  | .refPtr a x, .refPtr b y => if a && b then .val (decide (x = y)) else .typeError
  | .closure .., .closure .. | .closure .., .recclosure ..
  | .recclosure .., .closure .. | .recclosure .., .recclosure .. => .val true
  | _, _ => .typeError
termination_by sizeOf first

/-- Compare lists, stopping at the first unequal or ill-typed pair. -/
@[hol "cakeml/compiler/backend/semantics/closSemScript.sml" "do_eq_def"]
def doEqList (first second : List Value) : EqResult :=
  match first, second with
  | [], [] => .val true
  | x :: xs, y :: ys => match doEq x y with
    | .val true => doEqList xs ys
    | result => result
  | _, _ => .val false
termination_by sizeOf first
end

end Flapjack.Compiler.Backend.ClosSem
