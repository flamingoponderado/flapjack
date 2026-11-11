import Flapjack.Compiler.Backend.Semantics.ClosSem.GeneratedSize

/-! Values captured in scripts/hol-probes/clossem_generated_size_probe.out. -/
namespace Flapjack.Test.ClosSemGeneratedSizeParity
open Flapjack.Compiler.Backend

example : ClosSem.valueSizeHOL (.block 3 [.number 42, .word64 7]) = 15 := by decide
example : ClosSem.valueSizeHOL (.closure none [] [] 3 (.var .none 4)) = 9 := by decide
example : ClosSem.valueSizeHOL (.byteVector [0, 255, 2]) = 261 := by decide
example : ClosSem.valueSizeHOL (.recclosure (some 2) [.number 1] [.word64 5] [(1, .var .none 4)] 3) = 24 := by decide
example : ClosLang.opSizeHOL (.blockOp (.constant (.constCons 2 [.constWord64 9, .constInt 4]))) = 18 := by decide

end Flapjack.Test.ClosSemGeneratedSizeParity
