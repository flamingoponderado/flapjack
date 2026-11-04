import Flapjack.StackAlloc.FrameMachine
import Flapjack.StackAlloc.Runtime

namespace Flapjack.RiscV

def frameCollectorConfig : StackGcConfig :=
  { shiftLength := 11
    smallShiftLength := 9
    lenSize := 32
    wordShift := 3
    wordBits := 64
    bytesInWord := 8
    immediateScratch := 31 }

end Flapjack.RiscV
