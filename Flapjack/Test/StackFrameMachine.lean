module

public import Flapjack.StackAlloc.FrameMachine
public import Flapjack.StackAlloc.Runtime

@[expose] public section

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
