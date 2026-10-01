import Flapjack.Compiler.Backend.WordAlloc.ReadsExp

namespace Flapjack.Test.WordAllocReadsExpParity
open WordAlloc

/- Direct original HOL rows: scripts/hol-probes/word_alloc_reads_exp_probe.out.
Regenerate via CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_reads_exp_probeScript.sml scripts/hol-probes/regenerate.sh.
These replay every captured `get_reads_exp` row through the exact polymorphic
`getReadsExpHOL`; they are regression observations, not an independent
cross-language equivalence theorem. -/
-- var_single=[3]
example : getReadsExpHOL (.var 3 : WordLangExpHOL (BitVec 8)) = [3] := by decide +kernel
-- load_var=[3]
example : getReadsExpHOL (.load (.var 3) : WordLangExpHOL (BitVec 8)) = [3] := by decide +kernel
-- op_nested=[3; 5; 3]
example : getReadsExpHOL
    (.op .add [.var 3, .load (.var 5), .var 3] : WordLangExpHOL (BitVec 8)) =
    [3, 5, 3] := by decide +kernel
-- shift_order=[5; 6]
example : getReadsExpHOL
    (.shift .lsl (.var 5) (.var 6) : WordLangExpHOL (BitVec 8)) = [5, 6] := by decide +kernel
-- const_empty=[]
example : getReadsExpHOL (.const 7 : WordLangExpHOL (BitVec 8)) = [] := by decide +kernel
-- lookup_empty=[]
example : getReadsExpHOL (.lookup (.temp 9) : WordLangExpHOL (BitVec 8)) = [] := by decide +kernel
-- mixed_nested=[7; 2; 4]
example : getReadsExpHOL
    (.op .sub [.load (.shift .lsr (.var 7) (.var 2)), .var 4, .const 9] :
      WordLangExpHOL (BitVec 8)) = [7, 2, 4] := by decide +kernel

end Flapjack.Test.WordAllocReadsExpParity
