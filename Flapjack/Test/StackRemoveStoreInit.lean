import Flapjack.Compiler.Backend.StackRemove.StoreInit

/-! Fresh original store_init full definition/type and complete output snapshots
are recorded in store_init_probe.out. Every monomorphic constructor is observed,
including all fixed-width five-bit Temp payloads independently of output width.
Full initialization/compile routing remains a separate dependency-linked task. -/
namespace Flapjack.Test.StackRemoveStoreInit
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

private def storeNames : List StoreName :=
  [.currHeap, .globReal, .nextFree, .triggerGC, .endOfHeap, .heapLength, .otherHeap, .bitmapBase, .bitmapBuffer, .bitmapBufferEnd, .codeBuffer, .codeBufferEnd, .allocSize, .globals, .handler, .progStart, .genStart,
   .temp 0, .temp 1, .temp 2, .temp 3, .temp 4, .temp 5, .temp 6, .temp 7, .temp 8, .temp 9, .temp 10, .temp 11, .temp 12, .temp 13, .temp 14, .temp 15, .temp 16, .temp 17, .temp 18, .temp 19, .temp 20, .temp 21, .temp 22, .temp 23, .temp 24, .temp 25, .temp 26, .temp 27, .temp 28, .temp 29, .temp 30, .temp 31]

-- store_init_1_0_0: all49 original lookups.
example : storeNames.map (storeInit (width := 1) false 0) =
    [.inr 2, .inr 2, .inr 2, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_1_0_1: all49 original lookups.
example : storeNames.map (storeInit (width := 1) false 1) =
    [.inr 3, .inr 3, .inr 3, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_1_0_2: all49 original lookups.
example : storeNames.map (storeInit (width := 1) false 23) =
    [.inr 25, .inr 25, .inr 25, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_1_0_3: all49 original lookups.
example : storeNames.map (storeInit (width := 1) false 1208925819614629174706185) =
    [.inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_1_1_0: all49 original lookups.
example : storeNames.map (storeInit (width := 1) true 0) =
    [.inr 2, .inr 2, .inr 2, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_1_1_1: all49 original lookups.
example : storeNames.map (storeInit (width := 1) true 1) =
    [.inr 3, .inr 3, .inr 3, .inr 3, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_1_1_2: all49 original lookups.
example : storeNames.map (storeInit (width := 1) true 23) =
    [.inr 25, .inr 25, .inr 25, .inr 25, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_1_1_3: all49 original lookups.
example : storeNames.map (storeInit (width := 1) true 1208925819614629174706185) =
    [.inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_8_0_0: all49 original lookups.
example : storeNames.map (storeInit (width := 8) false 0) =
    [.inr 2, .inr 2, .inr 2, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_8_0_1: all49 original lookups.
example : storeNames.map (storeInit (width := 8) false 1) =
    [.inr 3, .inr 3, .inr 3, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_8_0_2: all49 original lookups.
example : storeNames.map (storeInit (width := 8) false 23) =
    [.inr 25, .inr 25, .inr 25, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_8_0_3: all49 original lookups.
example : storeNames.map (storeInit (width := 8) false 1208925819614629174706185) =
    [.inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_8_1_0: all49 original lookups.
example : storeNames.map (storeInit (width := 8) true 0) =
    [.inr 2, .inr 2, .inr 2, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_8_1_1: all49 original lookups.
example : storeNames.map (storeInit (width := 8) true 1) =
    [.inr 3, .inr 3, .inr 3, .inr 3, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_8_1_2: all49 original lookups.
example : storeNames.map (storeInit (width := 8) true 23) =
    [.inr 25, .inr 25, .inr 25, .inr 25, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_8_1_3: all49 original lookups.
example : storeNames.map (storeInit (width := 8) true 1208925819614629174706185) =
    [.inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_64_0_0: all49 original lookups.
example : storeNames.map (storeInit (width := 64) false 0) =
    [.inr 2, .inr 2, .inr 2, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_64_0_1: all49 original lookups.
example : storeNames.map (storeInit (width := 64) false 1) =
    [.inr 3, .inr 3, .inr 3, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_64_0_2: all49 original lookups.
example : storeNames.map (storeInit (width := 64) false 23) =
    [.inr 25, .inr 25, .inr 25, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_64_0_3: all49 original lookups.
example : storeNames.map (storeInit (width := 64) false 1208925819614629174706185) =
    [.inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_64_1_0: all49 original lookups.
example : storeNames.map (storeInit (width := 64) true 0) =
    [.inr 2, .inr 2, .inr 2, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_64_1_1: all49 original lookups.
example : storeNames.map (storeInit (width := 64) true 1) =
    [.inr 3, .inr 3, .inr 3, .inr 3, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_64_1_2: all49 original lookups.
example : storeNames.map (storeInit (width := 64) true 23) =
    [.inr 25, .inr 25, .inr 25, .inr 25, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_64_1_3: all49 original lookups.
example : storeNames.map (storeInit (width := 64) true 1208925819614629174706185) =
    [.inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_80_0_0: all49 original lookups.
example : storeNames.map (storeInit (width := 80) false 0) =
    [.inr 2, .inr 2, .inr 2, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_80_0_1: all49 original lookups.
example : storeNames.map (storeInit (width := 80) false 1) =
    [.inr 3, .inr 3, .inr 3, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_80_0_2: all49 original lookups.
example : storeNames.map (storeInit (width := 80) false 23) =
    [.inr 25, .inr 25, .inr 25, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_80_0_3: all49 original lookups.
example : storeNames.map (storeInit (width := 80) false 1208925819614629174706185) =
    [.inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_80_1_0: all49 original lookups.
example : storeNames.map (storeInit (width := 80) true 0) =
    [.inr 2, .inr 2, .inr 2, .inr 2, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_80_1_1: all49 original lookups.
example : storeNames.map (storeInit (width := 80) true 1) =
    [.inr 3, .inr 3, .inr 3, .inr 3, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_80_1_2: all49 original lookups.
example : storeNames.map (storeInit (width := 80) true 23) =
    [.inr 25, .inr 25, .inr 25, .inr 25, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

-- store_init_80_1_3: all49 original lookups.
example : storeNames.map (storeInit (width := 80) true 1208925819614629174706185) =
    [.inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 1208925819614629174706187, .inr 2, .inr 5, .inr 2, .inr 3, .inr 4, .inr 6, .inr 7, .inr 1, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0] := by rfl

end Flapjack.Test.StackRemoveStoreInit
