import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.WordToStack.Native

/-- Native compiler configuration, matching the source record's two fields.
`stackFrameSize` retains the constructor-for-constructor `num spt` carrier,
including non-well-formed trees; no finite-map or well-formedness premise is
introduced. The source record contains no words or FFI host parameter. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "config"]
structure Config where
  bitmapsLength : Nat
  stackFrameSize : Flapjack.Spt Nat
  deriving DecidableEq, Repr

end Flapjack.Compiler.Backend.WordToStack.Native
