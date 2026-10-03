import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.BackendCommon

/-- Complete original word-operation enum, with all five nullary constructors. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "opw"]
inductive Opw where
  | andw
  | orw
  | xor
  | add
  | sub
  deriving DecidableEq, Repr

end Flapjack.Compiler.Backend.BackendCommon
