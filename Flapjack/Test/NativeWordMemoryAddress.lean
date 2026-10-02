import Flapjack.Compiler.Backend.WordToStack.NativeInstructions

import Flapjack.RiscV.WordToStack

/-! Fresh original native Addr/wInst fixtures and executed static-address boundary checks. No additional HOL port claimed. -/

namespace Flapjack.Test.NativeWordMemoryAddress

open Flapjack Flapjack.RiscV Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native

-- addr_load_0_2_0
example : wInstNative (width := 64) (.mem .load 0 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.inst (.mem .load 0 (.addr 1 (BitVec.ofNat 64 0)))) : HolProg 64) := by rfl

-- addr_load_0_2_8
example : wInstNative (width := 64) (.mem .load 0 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.inst (.mem .load 0 (.addr 1 (BitVec.ofNat 64 8)))) : HolProg 64) := by rfl

-- addr_load_0_2_18446744073709551608
example : wInstNative (width := 64) (.mem .load 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.inst (.mem .load 0 (.addr 1 (BitVec.ofNat 64 18446744073709551608)))) : HolProg 64) := by rfl

-- addr_load_4_2_0
example : wInstNative (width := 64) (.mem .load 4 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.inst (.mem .load 2 (.addr 1 (BitVec.ofNat 64 0)))) (.stackStore 2 6)) : HolProg 64) := by rfl

-- addr_load_4_2_8
example : wInstNative (width := 64) (.mem .load 4 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.inst (.mem .load 2 (.addr 1 (BitVec.ofNat 64 8)))) (.stackStore 2 6)) : HolProg 64) := by rfl

-- addr_load_4_2_18446744073709551608
example : wInstNative (width := 64) (.mem .load 4 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.inst (.mem .load 2 (.addr 1 (BitVec.ofNat 64 18446744073709551608)))) (.stackStore 2 6)) : HolProg 64) := by rfl

-- addr_load_0_6_0
example : wInstNative (width := 64) (.mem .load 0 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .load 0 (.addr 2 (BitVec.ofNat 64 0))))) : HolProg 64) := by rfl

-- addr_load_0_6_8
example : wInstNative (width := 64) (.mem .load 0 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .load 0 (.addr 2 (BitVec.ofNat 64 8))))) : HolProg 64) := by rfl

-- addr_load_0_6_18446744073709551608
example : wInstNative (width := 64) (.mem .load 0 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .load 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))))) : HolProg 64) := by rfl

-- addr_load_4_6_0
example : wInstNative (width := 64) (.mem .load 4 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.inst (.mem .load 2 (.addr 2 (BitVec.ofNat 64 0)))) (.stackStore 2 6))) : HolProg 64) := by rfl

-- addr_load_4_6_8
example : wInstNative (width := 64) (.mem .load 4 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.inst (.mem .load 2 (.addr 2 (BitVec.ofNat 64 8)))) (.stackStore 2 6))) : HolProg 64) := by rfl

-- addr_load_4_6_18446744073709551608
example : wInstNative (width := 64) (.mem .load 4 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.inst (.mem .load 2 (.addr 2 (BitVec.ofNat 64 18446744073709551608)))) (.stackStore 2 6))) : HolProg 64) := by rfl

-- addr_store_0_2_0
example : wInstNative (width := 64) (.mem .store 0 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.inst (.mem .store 0 (.addr 1 (BitVec.ofNat 64 0)))) : HolProg 64) := by rfl

-- addr_store_0_2_8
example : wInstNative (width := 64) (.mem .store 0 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.inst (.mem .store 0 (.addr 1 (BitVec.ofNat 64 8)))) : HolProg 64) := by rfl

-- addr_store_0_2_18446744073709551608
example : wInstNative (width := 64) (.mem .store 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.inst (.mem .store 0 (.addr 1 (BitVec.ofNat 64 18446744073709551608)))) : HolProg 64) := by rfl

-- addr_store_4_2_0
example : wInstNative (width := 64) (.mem .store 4 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 3 6) (.inst (.mem .store 3 (.addr 1 (BitVec.ofNat 64 0))))) : HolProg 64) := by rfl

-- addr_store_4_2_8
example : wInstNative (width := 64) (.mem .store 4 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 3 6) (.inst (.mem .store 3 (.addr 1 (BitVec.ofNat 64 8))))) : HolProg 64) := by rfl

-- addr_store_4_2_18446744073709551608
example : wInstNative (width := 64) (.mem .store 4 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 3 6) (.inst (.mem .store 3 (.addr 1 (BitVec.ofNat 64 18446744073709551608))))) : HolProg 64) := by rfl

-- addr_store_0_6_0
example : wInstNative (width := 64) (.mem .store 0 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .store 0 (.addr 2 (BitVec.ofNat 64 0))))) : HolProg 64) := by rfl

-- addr_store_0_6_8
example : wInstNative (width := 64) (.mem .store 0 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .store 0 (.addr 2 (BitVec.ofNat 64 8))))) : HolProg 64) := by rfl

-- addr_store_0_6_18446744073709551608
example : wInstNative (width := 64) (.mem .store 0 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .store 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))))) : HolProg 64) := by rfl

-- addr_store_4_6_0
example : wInstNative (width := 64) (.mem .store 4 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.stackLoad 3 6) (.inst (.mem .store 3 (.addr 2 (BitVec.ofNat 64 0)))))) : HolProg 64) := by rfl

-- addr_store_4_6_8
example : wInstNative (width := 64) (.mem .store 4 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.stackLoad 3 6) (.inst (.mem .store 3 (.addr 2 (BitVec.ofNat 64 8)))))) : HolProg 64) := by rfl

-- addr_store_4_6_18446744073709551608
example : wInstNative (width := 64) (.mem .store 4 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.stackLoad 3 6) (.inst (.mem .store 3 (.addr 2 (BitVec.ofNat 64 18446744073709551608)))))) : HolProg 64) := by rfl

-- addr_load8_0_2_0
example : wInstNative (width := 64) (.mem .load8 0 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.inst (.mem .load8 0 (.addr 1 (BitVec.ofNat 64 0)))) : HolProg 64) := by rfl

-- addr_load8_0_2_8
example : wInstNative (width := 64) (.mem .load8 0 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.inst (.mem .load8 0 (.addr 1 (BitVec.ofNat 64 8)))) : HolProg 64) := by rfl

-- addr_load8_0_2_18446744073709551608
example : wInstNative (width := 64) (.mem .load8 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.inst (.mem .load8 0 (.addr 1 (BitVec.ofNat 64 18446744073709551608)))) : HolProg 64) := by rfl

-- addr_load8_4_2_0
example : wInstNative (width := 64) (.mem .load8 4 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.inst (.mem .load8 2 (.addr 1 (BitVec.ofNat 64 0)))) (.stackStore 2 6)) : HolProg 64) := by rfl

-- addr_load8_4_2_8
example : wInstNative (width := 64) (.mem .load8 4 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.inst (.mem .load8 2 (.addr 1 (BitVec.ofNat 64 8)))) (.stackStore 2 6)) : HolProg 64) := by rfl

-- addr_load8_4_2_18446744073709551608
example : wInstNative (width := 64) (.mem .load8 4 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.inst (.mem .load8 2 (.addr 1 (BitVec.ofNat 64 18446744073709551608)))) (.stackStore 2 6)) : HolProg 64) := by rfl

-- addr_load8_0_6_0
example : wInstNative (width := 64) (.mem .load8 0 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .load8 0 (.addr 2 (BitVec.ofNat 64 0))))) : HolProg 64) := by rfl

-- addr_load8_0_6_8
example : wInstNative (width := 64) (.mem .load8 0 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .load8 0 (.addr 2 (BitVec.ofNat 64 8))))) : HolProg 64) := by rfl

-- addr_load8_0_6_18446744073709551608
example : wInstNative (width := 64) (.mem .load8 0 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .load8 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))))) : HolProg 64) := by rfl

-- addr_load8_4_6_0
example : wInstNative (width := 64) (.mem .load8 4 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.inst (.mem .load8 2 (.addr 2 (BitVec.ofNat 64 0)))) (.stackStore 2 6))) : HolProg 64) := by rfl

-- addr_load8_4_6_8
example : wInstNative (width := 64) (.mem .load8 4 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.inst (.mem .load8 2 (.addr 2 (BitVec.ofNat 64 8)))) (.stackStore 2 6))) : HolProg 64) := by rfl

-- addr_load8_4_6_18446744073709551608
example : wInstNative (width := 64) (.mem .load8 4 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.inst (.mem .load8 2 (.addr 2 (BitVec.ofNat 64 18446744073709551608)))) (.stackStore 2 6))) : HolProg 64) := by rfl

-- addr_store8_0_2_0
example : wInstNative (width := 64) (.mem .store8 0 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.inst (.mem .store8 0 (.addr 1 (BitVec.ofNat 64 0)))) : HolProg 64) := by rfl

-- addr_store8_0_2_8
example : wInstNative (width := 64) (.mem .store8 0 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.inst (.mem .store8 0 (.addr 1 (BitVec.ofNat 64 8)))) : HolProg 64) := by rfl

-- addr_store8_0_2_18446744073709551608
example : wInstNative (width := 64) (.mem .store8 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.inst (.mem .store8 0 (.addr 1 (BitVec.ofNat 64 18446744073709551608)))) : HolProg 64) := by rfl

-- addr_store8_4_2_0
example : wInstNative (width := 64) (.mem .store8 4 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 3 6) (.inst (.mem .store8 3 (.addr 1 (BitVec.ofNat 64 0))))) : HolProg 64) := by rfl

-- addr_store8_4_2_8
example : wInstNative (width := 64) (.mem .store8 4 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 3 6) (.inst (.mem .store8 3 (.addr 1 (BitVec.ofNat 64 8))))) : HolProg 64) := by rfl

-- addr_store8_4_2_18446744073709551608
example : wInstNative (width := 64) (.mem .store8 4 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 3 6) (.inst (.mem .store8 3 (.addr 1 (BitVec.ofNat 64 18446744073709551608))))) : HolProg 64) := by rfl

-- addr_store8_0_6_0
example : wInstNative (width := 64) (.mem .store8 0 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .store8 0 (.addr 2 (BitVec.ofNat 64 0))))) : HolProg 64) := by rfl

-- addr_store8_0_6_8
example : wInstNative (width := 64) (.mem .store8 0 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .store8 0 (.addr 2 (BitVec.ofNat 64 8))))) : HolProg 64) := by rfl

-- addr_store8_0_6_18446744073709551608
example : wInstNative (width := 64) (.mem .store8 0 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .store8 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))))) : HolProg 64) := by rfl

-- addr_store8_4_6_0
example : wInstNative (width := 64) (.mem .store8 4 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.stackLoad 3 6) (.inst (.mem .store8 3 (.addr 2 (BitVec.ofNat 64 0)))))) : HolProg 64) := by rfl

-- addr_store8_4_6_8
example : wInstNative (width := 64) (.mem .store8 4 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.stackLoad 3 6) (.inst (.mem .store8 3 (.addr 2 (BitVec.ofNat 64 8)))))) : HolProg 64) := by rfl

-- addr_store8_4_6_18446744073709551608
example : wInstNative (width := 64) (.mem .store8 4 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.stackLoad 3 6) (.inst (.mem .store8 3 (.addr 2 (BitVec.ofNat 64 18446744073709551608)))))) : HolProg 64) := by rfl

-- addr_load32_0_2_0
example : wInstNative (width := 64) (.mem .load32 0 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.inst (.mem .load32 0 (.addr 1 (BitVec.ofNat 64 0)))) : HolProg 64) := by rfl

-- addr_load32_0_2_8
example : wInstNative (width := 64) (.mem .load32 0 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.inst (.mem .load32 0 (.addr 1 (BitVec.ofNat 64 8)))) : HolProg 64) := by rfl

-- addr_load32_0_2_18446744073709551608
example : wInstNative (width := 64) (.mem .load32 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.inst (.mem .load32 0 (.addr 1 (BitVec.ofNat 64 18446744073709551608)))) : HolProg 64) := by rfl

-- addr_load32_4_2_0
example : wInstNative (width := 64) (.mem .load32 4 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.inst (.mem .load32 2 (.addr 1 (BitVec.ofNat 64 0)))) (.stackStore 2 6)) : HolProg 64) := by rfl

-- addr_load32_4_2_8
example : wInstNative (width := 64) (.mem .load32 4 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.inst (.mem .load32 2 (.addr 1 (BitVec.ofNat 64 8)))) (.stackStore 2 6)) : HolProg 64) := by rfl

-- addr_load32_4_2_18446744073709551608
example : wInstNative (width := 64) (.mem .load32 4 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.inst (.mem .load32 2 (.addr 1 (BitVec.ofNat 64 18446744073709551608)))) (.stackStore 2 6)) : HolProg 64) := by rfl

-- addr_load32_0_6_0
example : wInstNative (width := 64) (.mem .load32 0 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .load32 0 (.addr 2 (BitVec.ofNat 64 0))))) : HolProg 64) := by rfl

-- addr_load32_0_6_8
example : wInstNative (width := 64) (.mem .load32 0 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .load32 0 (.addr 2 (BitVec.ofNat 64 8))))) : HolProg 64) := by rfl

-- addr_load32_0_6_18446744073709551608
example : wInstNative (width := 64) (.mem .load32 0 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .load32 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))))) : HolProg 64) := by rfl

-- addr_load32_4_6_0
example : wInstNative (width := 64) (.mem .load32 4 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.inst (.mem .load32 2 (.addr 2 (BitVec.ofNat 64 0)))) (.stackStore 2 6))) : HolProg 64) := by rfl

-- addr_load32_4_6_8
example : wInstNative (width := 64) (.mem .load32 4 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.inst (.mem .load32 2 (.addr 2 (BitVec.ofNat 64 8)))) (.stackStore 2 6))) : HolProg 64) := by rfl

-- addr_load32_4_6_18446744073709551608
example : wInstNative (width := 64) (.mem .load32 4 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.inst (.mem .load32 2 (.addr 2 (BitVec.ofNat 64 18446744073709551608)))) (.stackStore 2 6))) : HolProg 64) := by rfl

-- addr_store32_0_2_0
example : wInstNative (width := 64) (.mem .store32 0 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.inst (.mem .store32 0 (.addr 1 (BitVec.ofNat 64 0)))) : HolProg 64) := by rfl

-- addr_store32_0_2_8
example : wInstNative (width := 64) (.mem .store32 0 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.inst (.mem .store32 0 (.addr 1 (BitVec.ofNat 64 8)))) : HolProg 64) := by rfl

-- addr_store32_0_2_18446744073709551608
example : wInstNative (width := 64) (.mem .store32 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.inst (.mem .store32 0 (.addr 1 (BitVec.ofNat 64 18446744073709551608)))) : HolProg 64) := by rfl

-- addr_store32_4_2_0
example : wInstNative (width := 64) (.mem .store32 4 (.addr 2 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 3 6) (.inst (.mem .store32 3 (.addr 1 (BitVec.ofNat 64 0))))) : HolProg 64) := by rfl

-- addr_store32_4_2_8
example : wInstNative (width := 64) (.mem .store32 4 (.addr 2 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 3 6) (.inst (.mem .store32 3 (.addr 1 (BitVec.ofNat 64 8))))) : HolProg 64) := by rfl

-- addr_store32_4_2_18446744073709551608
example : wInstNative (width := 64) (.mem .store32 4 (.addr 2 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 3 6) (.inst (.mem .store32 3 (.addr 1 (BitVec.ofNat 64 18446744073709551608))))) : HolProg 64) := by rfl

-- addr_store32_0_6_0
example : wInstNative (width := 64) (.mem .store32 0 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .store32 0 (.addr 2 (BitVec.ofNat 64 0))))) : HolProg 64) := by rfl

-- addr_store32_0_6_8
example : wInstNative (width := 64) (.mem .store32 0 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .store32 0 (.addr 2 (BitVec.ofNat 64 8))))) : HolProg 64) := by rfl

-- addr_store32_0_6_18446744073709551608
example : wInstNative (width := 64) (.mem .store32 0 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.inst (.mem .store32 0 (.addr 2 (BitVec.ofNat 64 18446744073709551608))))) : HolProg 64) := by rfl

-- addr_store32_4_6_0
example : wInstNative (width := 64) (.mem .store32 4 (.addr 6 (BitVec.ofNat 64 0))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.stackLoad 3 6) (.inst (.mem .store32 3 (.addr 2 (BitVec.ofNat 64 0)))))) : HolProg 64) := by rfl

-- addr_store32_4_6_8
example : wInstNative (width := 64) (.mem .store32 4 (.addr 6 (BitVec.ofNat 64 8))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.stackLoad 3 6) (.inst (.mem .store32 3 (.addr 2 (BitVec.ofNat 64 8)))))) : HolProg 64) := by rfl

-- addr_store32_4_6_18446744073709551608
example : wInstNative (width := 64) (.mem .store32 4 (.addr 6 (BitVec.ofNat 64 18446744073709551608))) (2,7,9) =
    ((.seq (.stackLoad 2 5) (.seq (.stackLoad 3 6) (.inst (.mem .store32 3 (.addr 2 (BitVec.ofNat 64 18446744073709551608)))))) : HolProg 64) := by rfl

example :
    let cfg : WordStackConfig := {
      locations := [(0, .register 4), (1, .stack 2)]
      scratch := 31
      addressScratch := 29
      stackBase := 10 }
    wordStackCompileLoadNatNested cfg 0 (.op .add [.var 1, .const 0]) = some (.seq (.stackLoad 31 12)
      (.inst (.memOffset .load 4 31 0))) := by
  simp [wordStackCompileLoadNatNested, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    let cfg : WordStackConfig := {
      locations := [(0, .register 4), (1, .stack 2)]
      scratch := 31
      addressScratch := 29
      stackBase := 10 }
    wordStackCompileLoadNatNested cfg 0 (.op .sub [.var 1, .const 8]) = some (.seq (.stackLoad 31 12)
      (.inst (.memOffset .load 4 31 18446744073709551608))) := by
  simp [wordStackCompileLoadNatNested, wordStackLoadOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    let cfg : WordStackConfig := {
      locations := [(0, .register 4), (1, .stack 2)]
      scratch := 31
      addressScratch := 29
      stackBase := 10 }
    wordStackCompileStoreNatNested cfg (.op .add [.var 1, .const 0]) (.var 0) = some (.seq (.stackLoad 31 12)
      (.inst (.memOffset .store 4 31 0))) := by
  simp [wordStackCompileStoreNatNested, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

example :
    let cfg : WordStackConfig := {
      locations := [(0, .register 4), (1, .stack 2)]
      scratch := 31
      addressScratch := 29
      stackBase := 10 }
    wordStackCompileStoreNatNested cfg (.op .sub [.var 1, .const 8]) (.var 0) = some (.seq (.stackLoad 31 12)
      (.inst (.memOffset .store 4 31 18446744073709551608))) := by
  simp [wordStackCompileStoreNatNested, wordStackStoreOffsetInst, wordStackLocation,
    wordStackOffset, lookupNatInfo]

end Flapjack.Test.NativeWordMemoryAddress
