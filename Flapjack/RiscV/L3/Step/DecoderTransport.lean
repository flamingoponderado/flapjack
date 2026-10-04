import Flapjack.RiscV.L3.Step.DecodeAny

/-! Original decoder transport rules used by the symbolic step library. Both
retain the full native instruction carrier and literal decoder equality premise. -/
namespace Flapjack.RiscV.L3.Step
open Flapjack.RiscV.L3

/-- Transport the original full word32 decoder result into the raw Word selector. -/
theorem decode_imp_decodeAny (w : BitVec 32) (i : instruction)
    (h : Decode w = i) : DecodeAny (.Word w) = i := h

/-- Transport the original full word16 decoder result into the raw Half selector. -/
theorem decodeRVC_imp_decodeAny (hword : BitVec 16) (i : instruction)
    (h : DecodeRVC hword = i) : DecodeAny (.Half hword) = i := h

end Flapjack.RiscV.L3.Step
