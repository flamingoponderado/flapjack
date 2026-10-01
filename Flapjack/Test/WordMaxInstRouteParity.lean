import Flapjack.Compiler.Backend.WordAlloc.ProductionMaxVarInst

namespace Flapjack.Test
open RiscV

-- Original word_max_inst_route_probe.out: same operands, offsets and widths.
example : wordInstCakeMaxVar (.memOffset .load16 7 19 (3 : BitVec 64)) = 0 := by decide +kernel
example : wordInstCakeMaxVar (.memOffset .store16 7 19 (3 : BitVec 64)) = 0 := by decide +kernel
example : wordInstCakeMaxVar (.memOffset .load32 7 19 (3 : BitVec 64)) = 19 := by decide +kernel
example : wordInstCakeMaxVar (.mem .store8 7 19 : WordInst (BitVec 32)) = 19 := by decide +kernel
example : wordSsaLimitVar [] (.inst (.memOffset .load16 7 19 (3 : BitVec 64))) = 5 := by decide +kernel
example : wordSsaLimitVar [] (.inst (.memOffset .store16 7 19 (3 : BitVec 64))) = 5 := by decide +kernel
example : wordSsaLimitVar [] (.inst (.memOffset .load32 7 19 (3 : BitVec 64))) = 21 := by decide +kernel

-- Both zero-offset encodings agree; the unsupported five-register primitive
-- still fails the codec rather than being silently equated with HOL AddCarry.
example : wordInstCakeMaxVar (.mem .load16 7 19 : WordInst (BitVec 64)) = 0 := by decide +kernel
example : wordLangInstToHOL (.arith (.addCarry 1 2 3 4 5) : WordInst (BitVec 64)) = none := by decide +kernel

end Flapjack.Test
