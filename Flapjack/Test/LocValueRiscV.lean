import Flapjack.RiscV.Lab

/-! End-to-end LocValue regression: a StackLang code label is resolved by the
    multi-section Lab linker and materialized as an absolute RISC-V pointer. -/

namespace Flapjack.RiscV

def locValueStackRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

end Flapjack.RiscV
