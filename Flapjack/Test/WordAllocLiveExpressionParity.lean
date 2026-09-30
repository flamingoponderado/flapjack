import Flapjack.Compiler.Backend.WordAlloc.LivenessRoute

namespace Flapjack.WordAlloc

/- Direct original HOL rows: scripts/hol-probes/word_alloc_live_exp_probe.out.
Regenerate via CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_live_exp_probeScript.sml scripts/hol-probes/regenerate.sh.
These check the executed wrapper, including canonical mixed traversal. -/
-- nested=[3; 5; 6]
example : liveExpressionKeys (.op .add [.const 7, .load (.var 3),
    .lookup (.temp 9), .shift .lsl (.var 5) (.var 6)] : WordExp (BitVec 8)) =
    [3,5,6] := by decide +kernel
-- duplicate=[3; 4]
example : liveExpressionKeys (.op .sub [.var 3,.var 3,.var 4] : WordExp (BitVec 8)) =
    [3,4] := by decide +kernel
-- empty=[]
example : liveExpressionKeys (.op .add [] : WordExp (BitVec 8)) = [] := by decide +kernel
-- shift=[1; 0; 8]
example : liveExpressionKeys (.shift .lsr (.var 0)
    (.op .add [.var 8,.var 1,.var 8]) : WordExp (BitVec 8)) = [1,0,8] := by decide +kernel
-- constant=[]
example : liveExpressionKeys (.const 255 : WordExp (BitVec 8)) = [] := by decide +kernel
-- lookup=[]
example : liveExpressionKeys (.lookup (.temp 31) : WordExp (BitVec 8)) = [] := by decide +kernel

/-- The six kernel-replayed direct HOL rows are registered in `lake test`. -/
def runChecks : IO Bool := pure true

end Flapjack.WordAlloc
