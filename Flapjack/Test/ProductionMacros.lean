import Flapjack.Compiler.Backend.StackLang.ProductionMacros

namespace Flapjack.Test.ProductionMacros
open Flapjack Flapjack.Compiler.Backend.StackLang.ProductionMacros

-- Complete recursive call-option assembly; operand/label positions stay distinct.
example : projectMacros (width := 8) (.call none (.label 17) none) =
    some (.call none (.label 17) none) := by simp [projectMacros]
example : projectMacros (width := 8)
    (.call none (.register 17) (some (.arith .xor 2 3 4, 5, 6))) =
    some (.call none (.register 17)
      (some (.inst (.arith (.binOp .xor 2 3 (.reg 4))), 5, 6))) := by simp [projectMacros]
example : projectMacros (width := 8)
    (.call (some (.const 2 255, 3, 4, 5)) (.label 17) none) =
    some (.call (some (.inst (.const 2 255), 3, 4, 5)) (.label 17) none) := by
  simp [projectMacros]
example : projectMacros (width := 8)
    (.call (some (.const 2 255, 3, 4, 5)) (.register 17)
      (some (.shift .ror 6 7 8, 9, 10))) =
    some (.call (some (.inst (.const 2 255), 3, 4, 5)) (.register 17)
      (some (.inst (.arith (.shift .ror 6 7 (.reg 8))), 9, 10))) := by simp [projectMacros]
example : projectMacros (width := 8)
    (.seq (.arith .or 2 3 4) (.loop (.shift .lsl 5 6 7))) =
    some (.seq (.inst (.arith (.binOp .or 2 3 (.reg 4))))
      (.loop (.inst (.arith (.shift .lsl 5 6 (.reg 7)))))) := by simp [projectMacros]
example : projectMacros (width := 8)
    (.ite .lower 2 (.imm 255) (.const 3 17) (.const 4 18)) =
    some (.ite .lower 2 (.imm 255) (.inst (.const 3 17)) (.inst (.const 4 18))) := by
  simp [projectMacros]
example : projectMacros (width := 1) (.const 2 1) = some (.inst (.const 2 1)) := by
  simp [projectMacros]
example : projectMacros (width := 1) (.const 2 2) = none := by simp [projectMacros]
example : projectMacros (width := 80) (.const 999 (2 ^ 79 + 1)) =
    some (.inst (.const 999 (BitVec.ofNat 80 (2 ^ 79 + 1)))) := by simp [projectMacros]
example : projectMacros (width := 8) (.const 2 256) = none := by simp [projectMacros]
example : projectMacros (width := 8) (.seq (.const 2 256) .skip) = none := by
  simp [projectMacros]
example : projectMacros (width := 8) (.seq .skip (.const 2 256)) = none := by
  simp [projectMacros]
example : projectMacros (width := 8) (.ite .equal 2 (.reg 3) (.const 4 256) .skip) = none := by
  simp [projectMacros]
example : projectMacros (width := 8) (.ite .equal 2 (.reg 3) .skip (.const 4 256)) = none := by
  simp [projectMacros]
example : projectMacros (width := 8) (.loop (.const 2 256)) = none := by simp [projectMacros]
example : projectMacros (width := 8)
    (.call (some (.const 2 256, 3, 4, 5)) (.register 17) none) = none := by
  simp [projectMacros]
example : projectMacros (width := 8)
    (.call none (.label 17) (some (.const 2 256, 3, 4))) = none := by simp [projectMacros]
example : projectMacros (width := 8)
    (.call (some (.const 2 256, 3, 4, 5)) (.register 17)
      (some (.const 6 7, 8, 9))) = none := by simp [projectMacros]
example : projectMacros (width := 8)
    (.call (some (.const 2 3, 4, 5, 6)) (.register 17)
      (some (.const 7 256, 8, 9))) = none := by simp [projectMacros]

-- Macro-free is intentionally narrower than the native codec input domain:
-- register validity, Unicode rejection and temporary-store bounds occur later.
example : projectMacros (width := 8) (.skip) = some (.skip) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.inst (.const 2 255)) = some (.inst (.const 2 255)) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.inst (.memOffset .store8 2 3 255)) = some (.inst (.memOffset .store8 2 3 255)) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.inst (.arith (.cakeAddCarry 2 3 4 5))) = some (.inst (.arith (.cakeAddCarry 2 3 4 5))) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.inst (.arith (.addCarry 2 3 4 5 6))) = some (.inst (.arith (.addCarry 2 3 4 5 6))) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.shMem .store8 2 3) = some (.shMem .store8 2 3) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.shMemOffset .load16 2 3 255) = some (.shMemOffset .load16 2 3 255) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.get 2 (.temp 999)) = some (.get 2 (.temp 999)) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.set (.temp 999) 2) = some (.set (.temp 999) 2) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.opCurrHeap .sub 2 3) = some (.opCurrHeap .sub 2 3) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.jumpLower 2 3 999) = some (.jumpLower 2 3 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.alloc 999) = some (.alloc 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.storeConsts 2 3 (some 999)) = some (.storeConsts 2 3 (some 999)) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.codeBufferWrite 2 3) = some (.codeBufferWrite 2 3) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.dataBufferWrite 2 3) = some (.dataBufferWrite 2 3) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.raise 999) = some (.raise 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.return 999) = some (.return 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.break 999) = some (.break 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.continue 999) = some (.continue 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.ffi "😀" 2 3 4 5 6) = some (.ffi "😀" 2 3 4 5 6) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.tick) = some (.tick) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.locValue 2 3 999) = some (.locValue 2 3 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.install 2 3 4 5 6) = some (.install 2 3 4 5 6) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.rawCall 999) = some (.rawCall 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.stackAlloc 999) = some (.stackAlloc 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.stackFree 999) = some (.stackFree 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.stackStore 2 999) = some (.stackStore 2 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.stackStoreAny 2 999) = some (.stackStoreAny 2 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.stackLoad 2 999) = some (.stackLoad 2 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.stackLoadAny 2 999) = some (.stackLoadAny 2 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.stackGetSize 999) = some (.stackGetSize 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.stackSetSize 999) = some (.stackSetSize 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.bitmapLoad 2 999) = some (.bitmapLoad 2 999) := by
  simp [projectMacros]
example : projectMacros (width := 8) (.halt 999) = some (.halt 999) := by
  simp [projectMacros]

end Flapjack.Test.ProductionMacros
