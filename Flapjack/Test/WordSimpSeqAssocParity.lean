module

public import Flapjack.RiscV.WordExpressionFlatten

@[expose] public section

/-! Original HOL Seq_assoc clauses and whole output trees captured in
word_simp_seq_assoc_source_probe.out. The earlier alternate Lean traversal
retained trailing Skip and was not an original oracle. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Flapjack.Test.WordSimpSeqAssocParity
open Flapjack RiscV
end Flapjack.Test.WordSimpSeqAssocParity
