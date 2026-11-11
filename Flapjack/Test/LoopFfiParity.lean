module

public import Flapjack.Pancake.Semantics.LoopSem
public import Flapjack.HolRef

import all Flapjack.Pancake.Semantics.LoopSem
import all Flapjack.HolRef
public meta import Flapjack.RiscV.PanMemory

@[expose] public section

/-!
# Loop `byte_align` regression

Checks `riscvByteAlignHOL`, the width-generic rendering of HOL `byte_align`
used by the Loop and Word byte operations, at widths 8, 24 and 64, and its
agreement with the reviewed RV64 codec `RiscV.panRiscVByteAlign`.
-/

namespace Flapjack.Test.LoopFfiParity

open Flapjack

def byteAlignGuard : Bool :=
  riscvByteAlignHOL (width := 24) (5 : RiscV.Word 24) == 4 &&
  riscvByteAlignHOL (width := 24) (3 : RiscV.Word 24) == 2 &&
  riscvByteAlignHOL (width := 8) (7 : RiscV.Word 8) == 7 &&
  riscvByteAlignHOL (width := 64) (13 : RiscV.Word 64) == 8 &&
  riscvByteAlignHOL (width := 64) (13 : RiscV.Word 64) ==
      RiscV.panRiscVByteAlign (8 : RiscV.Word 64) 13

#guard byteAlignGuard

def runChecks : IO Bool := do
  if byteAlignGuard then
    IO.println "PASS Loop byte_align at widths 8, 24 and 64"
  else
    IO.println "FAIL Loop byte_align at widths 8, 24 and 64"
  pure byteAlignGuard

end Flapjack.Test.LoopFfiParity
