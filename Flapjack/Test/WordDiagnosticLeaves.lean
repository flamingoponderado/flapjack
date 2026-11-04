import Flapjack.RiscV.WordDiagnostics

namespace Flapjack.Test.WordDiagnosticLeaves
open RiscV

private def operators : List WordMemOp :=
  [.load,.store,.load8,.store8,.load16,.store16,.load32,.store32]

end Flapjack.Test.WordDiagnosticLeaves
