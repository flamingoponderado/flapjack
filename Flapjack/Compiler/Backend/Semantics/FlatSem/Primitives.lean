import Flapjack.Compiler.Backend.Semantics.FlatSem
import Flapjack.Compiler.Backend.BackendCommon.BoolTags
import Flapjack.Compiler.Backend.BackendCommon.ConstructorTags
import Flapjack.SemanticPrimitivesHOL.Primitives

/-! Primitive type checks and literal projection in the flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.Compiler.Backend.BackendCommon

/-- The flat representation of the pattern-binding exception. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "bind_exn_v_def"]
def bindExnV : Value := .conv (some (bindTag, none)) []

/-- The flat representation of the character-conversion exception. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "chr_exn_v_def"]
def chrExnV : Value := .conv (some (chrTag, none)) []

/-- The flat representation of the division exception. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "div_exn_v_def"]
def divExnV : Value := .conv (some (divTag, none)) []

/-- The flat representation of the subscript exception. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "subscript_exn_v_def"]
def subscriptExnV : Value := .conv (some (subscriptTag, none)) []

/-- Check the seven primitive types against flat values. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "check_type_def"]
def checkType : PrimType → Value → Bool
  | .boolT, .conv (some (tag, some typeId)) [] =>
    typeId == FlatLang.boolId && (tag == trueTag || tag == falseTag)
  | .intT, .litv (.intLit _) => true
  | .charT, .litv (.char _) => true
  | .strT, .litv (.strLit _) => true
  | .wordT .w8, .litv (.word8 _) => true
  | .wordT .w64, .litv (.word64 _) => true
  | .float64T, .litv (.float64 _) => true
  | _, _ => false

/-- Project a literal from a flat value. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "dest_Litv_def"]
def destLitv : Value → Option Lit
  | .litv lit => some lit
  | _ => none

/-- Convert literals and Booleans to flat values; other values become an empty vector. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "v_to_flat_def"]
def valueToFlat : SemanticPrimitivesHOL.Value → Value
  | .litv lit => .litv lit
  | .conv (some (.typeStamp name 0)) [] =>
    if name == Basis.Pure.MlString.ofString "True" then boolValue true
    else if name == Basis.Pure.MlString.ofString "False" then boolValue false
    else .vectorv []
  | _ => .vectorv []

/-- Convert flat literals and Booleans to source values; other values become an empty vector. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "flat_to_v_def"]
def flatToValue : Value → SemanticPrimitivesHOL.Value
  | .litv lit => .litv lit
  | .conv (some (tag, some typeId)) [] =>
    if typeId == FlatLang.boolId && tag == trueTag then SemanticPrimitivesHOL.boolValue true
    else if typeId == FlatLang.boolId && tag == falseTag then SemanticPrimitivesHOL.boolValue false
    else .vectorv []
  | _ => .vectorv []

/-- Choose the appropriate branch for a flat Boolean value. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_if_def"]
def doIf {α : Type} (value : Value) (yes no : α) : Option α :=
  match value with
  | .conv (some (tag, some typeId)) [] =>
    if typeId == FlatLang.boolId && tag == trueTag then some yes
    else if typeId == FlatLang.boolId && tag == falseTag then some no else none
  | _ => none

/-- A successful conditional selects one of its two branches. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_if_either_or"]
theorem doIf_either_or {α : Type} (value : Value) (yes no result : α)
    (evaluated : doIf value yes no = some result) : result = yes ∨ result = no := by
  cases value <;> simp [doIf] at evaluated
  case conv stamp values =>
    cases stamp with
    | none => simp at evaluated
    | some ctor =>
      obtain ⟨tag, typeId⟩ := ctor
      cases typeId with
      | none => simp at evaluated
      | some typeId =>
        cases values with
        | cons => simp at evaluated
        | nil =>
          simp only at evaluated
          split at evaluated
          · exact Or.inl (Option.some.inj evaluated).symm
          · split at evaluated
            · exact Or.inr (Option.some.inj evaluated).symm
            · contradiction
end Flapjack.Compiler.Backend.FlatSem
