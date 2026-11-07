import Flapjack.Compiler.Backend.Semantics.DataSem.Word
import Flapjack.Compiler.Backend.Semantics.BvlSem.Word

/-! Regression cases for data-language word operations. -/
namespace Flapjack.Test.DataSemWord
open Flapjack.Compiler.Backend

example : DataSem.doWordApp (.wordTest .w8 (.compare .lt)) [.number 2, .number 3] =
    some (DataSem.boolValue true) := by
  simp [DataSem.doWordApp, DataSem.doWordAppIntegral]

example : DataSem.doWordApp (.wordTest .w8 (.compare .leq)) [.number 255, .number 255] =
    some (DataSem.boolValue true) := by
  simp [DataSem.doWordApp, DataSem.doWordAppIntegral]

example : DataSem.doWordApp (.wordTest .w8 (.compare .gt)) [.number 3, .number 2] = none := by
  simp [DataSem.doWordApp, DataSem.doWordAppIntegral]

example : BvlSem.doWordApp (.wordTest .w8 (.compare .gt)) [.number 3, .number 2] =
    some (BvlSem.boolValue true) := by
  rfl

example : DataSem.doWordApp (.wordTest .w8 .equal) [.number 256, .number 256] = none := by
  simp [DataSem.doWordApp, DataSem.doWordAppIntegral]

example : DataSem.doWordApp (.wordFromWord false) [.number (-1)] = none := by
  simp [DataSem.doWordApp, DataSem.doWordAppIntegral, ClosSem.intToByte]

example : DataSem.doWordApp .wordToInt [.word64 (BitVec.ofNat 64 257)] = some (.number 257) := by
  simp [DataSem.doWordApp, DataSem.doWordAppIntegral]

end Flapjack.Test.DataSemWord
