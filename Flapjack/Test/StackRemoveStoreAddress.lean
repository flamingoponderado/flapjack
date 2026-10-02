import Flapjack.Compiler.Backend.StackRemove.StoreAddress

/-! Kernel replay of original storage positions and modular offsets; no new HOL theorem claimed. -/

namespace Flapjack.Test.StackRemoveStoreAddress

open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

-- position_0
example : storePos (.nextFree) = 1 := by decide +kernel

-- position_1
example : storePos (.endOfHeap) = 2 := by decide +kernel

-- position_2
example : storePos (.heapLength) = 3 := by decide +kernel

-- position_3
example : storePos (.otherHeap) = 4 := by decide +kernel

-- position_4
example : storePos (.triggerGC) = 5 := by decide +kernel

-- position_5
example : storePos (.allocSize) = 6 := by decide +kernel

-- position_6
example : storePos (.handler) = 7 := by decide +kernel

-- position_7
example : storePos (.globals) = 8 := by decide +kernel

-- position_8
example : storePos (.globReal) = 9 := by decide +kernel

-- position_9
example : storePos (.progStart) = 10 := by decide +kernel

-- position_10
example : storePos (.bitmapBase) = 11 := by decide +kernel

-- position_11
example : storePos (.genStart) = 12 := by decide +kernel

-- position_12
example : storePos (.codeBuffer) = 13 := by decide +kernel

-- position_13
example : storePos (.codeBufferEnd) = 14 := by decide +kernel

-- position_14
example : storePos (.bitmapBuffer) = 15 := by decide +kernel

-- position_15
example : storePos (.bitmapBufferEnd) = 16 := by decide +kernel

-- position_16
example : storePos (.temp (BitVec.ofNat 5 0)) = 17 := by decide +kernel

-- position_17
example : storePos (.temp (BitVec.ofNat 5 1)) = 18 := by decide +kernel

-- position_18
example : storePos (.temp (BitVec.ofNat 5 2)) = 19 := by decide +kernel

-- position_19
example : storePos (.temp (BitVec.ofNat 5 3)) = 20 := by decide +kernel

-- position_20
example : storePos (.temp (BitVec.ofNat 5 4)) = 21 := by decide +kernel

-- position_21
example : storePos (.temp (BitVec.ofNat 5 5)) = 22 := by decide +kernel

-- position_22
example : storePos (.temp (BitVec.ofNat 5 6)) = 23 := by decide +kernel

-- position_23
example : storePos (.temp (BitVec.ofNat 5 7)) = 24 := by decide +kernel

-- position_24
example : storePos (.temp (BitVec.ofNat 5 8)) = 25 := by decide +kernel

-- position_25
example : storePos (.temp (BitVec.ofNat 5 9)) = 26 := by decide +kernel

-- position_26
example : storePos (.temp (BitVec.ofNat 5 10)) = 27 := by decide +kernel

-- position_27
example : storePos (.temp (BitVec.ofNat 5 11)) = 28 := by decide +kernel

-- position_28
example : storePos (.temp (BitVec.ofNat 5 12)) = 29 := by decide +kernel

-- position_29
example : storePos (.temp (BitVec.ofNat 5 13)) = 30 := by decide +kernel

-- position_30
example : storePos (.temp (BitVec.ofNat 5 14)) = 31 := by decide +kernel

-- position_31
example : storePos (.temp (BitVec.ofNat 5 15)) = 32 := by decide +kernel

-- position_32
example : storePos (.temp (BitVec.ofNat 5 16)) = 33 := by decide +kernel

-- position_33
example : storePos (.temp (BitVec.ofNat 5 17)) = 34 := by decide +kernel

-- position_34
example : storePos (.temp (BitVec.ofNat 5 18)) = 35 := by decide +kernel

-- position_35
example : storePos (.temp (BitVec.ofNat 5 19)) = 36 := by decide +kernel

-- position_36
example : storePos (.temp (BitVec.ofNat 5 20)) = 37 := by decide +kernel

-- position_37
example : storePos (.temp (BitVec.ofNat 5 21)) = 38 := by decide +kernel

-- position_38
example : storePos (.temp (BitVec.ofNat 5 22)) = 39 := by decide +kernel

-- position_39
example : storePos (.temp (BitVec.ofNat 5 23)) = 40 := by decide +kernel

-- position_40
example : storePos (.temp (BitVec.ofNat 5 24)) = 41 := by decide +kernel

-- position_41
example : storePos (.temp (BitVec.ofNat 5 25)) = 42 := by decide +kernel

-- position_42
example : storePos (.temp (BitVec.ofNat 5 26)) = 43 := by decide +kernel

-- position_43
example : storePos (.temp (BitVec.ofNat 5 27)) = 44 := by decide +kernel

-- position_44
example : storePos (.temp (BitVec.ofNat 5 28)) = 45 := by decide +kernel

-- position_45
example : storePos (.temp (BitVec.ofNat 5 29)) = 46 := by decide +kernel

-- position_46
example : storePos (.temp (BitVec.ofNat 5 30)) = 47 := by decide +kernel

-- position_47
example : storePos (.temp (BitVec.ofNat 5 31)) = 48 := by decide +kernel

-- position_48
example : storePos (.currHeap) = 0 := by decide +kernel

-- offset_1_0
example : storeOffset (width := 1) (.nextFree) = BitVec.ofNat 1 0 := by decide +kernel

-- offset_1_10
example : storeOffset (width := 1) (.bitmapBase) = BitVec.ofNat 1 0 := by decide +kernel

-- offset_1_15
example : storeOffset (width := 1) (.bitmapBufferEnd) = BitVec.ofNat 1 0 := by decide +kernel

-- offset_1_16
example : storeOffset (width := 1) (.temp (BitVec.ofNat 5 0)) = BitVec.ofNat 1 0 := by decide +kernel

-- offset_1_47
example : storeOffset (width := 1) (.temp (BitVec.ofNat 5 31)) = BitVec.ofNat 1 0 := by decide +kernel

-- offset_1_48
example : storeOffset (width := 1) (.currHeap) = BitVec.ofNat 1 0 := by decide +kernel

-- offset_8_0
example : storeOffset (width := 8) (.nextFree) = BitVec.ofNat 8 255 := by decide +kernel

-- offset_8_10
example : storeOffset (width := 8) (.bitmapBase) = BitVec.ofNat 8 245 := by decide +kernel

-- offset_8_15
example : storeOffset (width := 8) (.bitmapBufferEnd) = BitVec.ofNat 8 240 := by decide +kernel

-- offset_8_16
example : storeOffset (width := 8) (.temp (BitVec.ofNat 5 0)) = BitVec.ofNat 8 239 := by decide +kernel

-- offset_8_47
example : storeOffset (width := 8) (.temp (BitVec.ofNat 5 31)) = BitVec.ofNat 8 208 := by decide +kernel

-- offset_8_48
example : storeOffset (width := 8) (.currHeap) = BitVec.ofNat 8 0 := by decide +kernel

-- offset_32_0
example : storeOffset (width := 32) (.nextFree) = BitVec.ofNat 32 4294967292 := by decide +kernel

-- offset_32_10
example : storeOffset (width := 32) (.bitmapBase) = BitVec.ofNat 32 4294967252 := by decide +kernel

-- offset_32_15
example : storeOffset (width := 32) (.bitmapBufferEnd) = BitVec.ofNat 32 4294967232 := by decide +kernel

-- offset_32_16
example : storeOffset (width := 32) (.temp (BitVec.ofNat 5 0)) = BitVec.ofNat 32 4294967228 := by decide +kernel

-- offset_32_47
example : storeOffset (width := 32) (.temp (BitVec.ofNat 5 31)) = BitVec.ofNat 32 4294967104 := by decide +kernel

-- offset_32_48
example : storeOffset (width := 32) (.currHeap) = BitVec.ofNat 32 0 := by decide +kernel

-- offset_64_0
example : storeOffset (width := 64) (.nextFree) = BitVec.ofNat 64 18446744073709551608 := by decide +kernel

-- offset_64_10
example : storeOffset (width := 64) (.bitmapBase) = BitVec.ofNat 64 18446744073709551528 := by decide +kernel

-- offset_64_15
example : storeOffset (width := 64) (.bitmapBufferEnd) = BitVec.ofNat 64 18446744073709551488 := by decide +kernel

-- offset_64_16
example : storeOffset (width := 64) (.temp (BitVec.ofNat 5 0)) = BitVec.ofNat 64 18446744073709551480 := by decide +kernel

-- offset_64_47
example : storeOffset (width := 64) (.temp (BitVec.ofNat 5 31)) = BitVec.ofNat 64 18446744073709551232 := by decide +kernel

-- offset_64_48
example : storeOffset (width := 64) (.currHeap) = BitVec.ofNat 64 0 := by decide +kernel

-- offset_80_0
example : storeOffset (width := 80) (.nextFree) = BitVec.ofNat 80 1208925819614629174706166 := by decide +kernel

-- offset_80_10
example : storeOffset (width := 80) (.bitmapBase) = BitVec.ofNat 80 1208925819614629174706066 := by decide +kernel

-- offset_80_15
example : storeOffset (width := 80) (.bitmapBufferEnd) = BitVec.ofNat 80 1208925819614629174706016 := by decide +kernel

-- offset_80_16
example : storeOffset (width := 80) (.temp (BitVec.ofNat 5 0)) = BitVec.ofNat 80 1208925819614629174706006 := by decide +kernel

-- offset_80_47
example : storeOffset (width := 80) (.temp (BitVec.ofNat 5 31)) = BitVec.ofNat 80 1208925819614629174705696 := by decide +kernel

-- offset_80_48
example : storeOffset (width := 80) (.currHeap) = BitVec.ofNat 80 0 := by decide +kernel

end Flapjack.Test.StackRemoveStoreAddress
