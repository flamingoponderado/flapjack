import Flapjack.Compiler.Backend.BackendCommon.Operators
import Flapjack.Pancake.PanLang

/-! Classify word arithmetic operations for data-to-word lowering. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- Source classification of operations that are bitwise or require carry. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "word_op_type"]
inductive WordOpType where
  | bitwise : BinOp → WordOpType
  | carried : BinOp → WordOpType
  deriving DecidableEq

/-- Map source word operators to their word-language implementation. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "lookup_word_op_def"]
def lookupWordOp : BackendCommon.Opw → WordOpType
  | .andw => .bitwise .and
  | .orw => .bitwise .or
  | .xor => .bitwise .xor
  | .add => .carried .add
  | .sub => .carried .sub

end Flapjack.Compiler.Backend.DataToWord
