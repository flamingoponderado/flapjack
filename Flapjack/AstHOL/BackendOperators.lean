import Flapjack.AstHOL

namespace Flapjack.AstHOL

/-- Complete original `word_size` selector carrier; constructor order and payloads retained. -/
@[hol "cakeml/semantics/astScript.sml" "word_size"]
inductive WordSize where
  | w8
  | w64
  deriving DecidableEq, Repr

/-- Complete original `thunk_mode` selector carrier; constructor order and payloads retained. -/
@[hol "cakeml/semantics/astScript.sml" "thunk_mode"]
inductive ThunkMode where
  | evaluated
  | notEvaluated
  deriving DecidableEq, Repr

/-- Complete original `thunk_op` selector carrier; constructor order and payloads retained. -/
@[hol "cakeml/semantics/astScript.sml" "thunk_op"]
inductive ThunkOp where
  | allocThunk : ThunkMode → ThunkOp
  | updateThunk : ThunkMode → ThunkOp
  | forceThunk
  deriving DecidableEq, Repr

/-- Complete original `test` selector carrier; constructor order and payloads retained. -/
@[hol "cakeml/semantics/astScript.sml" "test"]
inductive Test where
  | equal
  | compare : Opb → Test
  | altCompare : Opb → Test
  deriving DecidableEq, Repr

end Flapjack.AstHOL
