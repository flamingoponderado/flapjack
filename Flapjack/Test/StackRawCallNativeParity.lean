import Flapjack.Compiler.Backend.StackRawCall

/-! Kernel replay of the original rawcall native probe. These fixtures compare
complete constructor trees, including untouched and compiled handler bodies. -/
namespace Flapjack.Test.StackRawCallNativeParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall
private def tail : HolProg 64 := .seq (.stackFree 4) (.call none (.inl 7) none)
example : comp (sptInsert 7 4 .ln) tail = .rawCall 7 := by simp [comp, compSeq, destCase, tail, sptInsert, sptLookup]
example : comp (sptInsert 7 2 .ln) tail = .seq (.stackFree 2) (.rawCall 7) := by simp [comp, compSeq, destCase, tail, sptInsert, sptLookup]
example : comp (sptInsert 7 6 .ln) tail = .seq .tick (.seq (.stackAlloc 2) (.rawCall 7)) := by simp [comp, compSeq, destCase, tail, sptInsert, sptLookup]
example : comp (.ln : Spt Nat) tail = tail := by simp [comp, compSeq, destCase, tail, sptLookup]
example : compTop (sptInsert 7 4 .ln) tail = tail := by simp [comp, compTop, tail]
example : comp (sptInsert 7 4 .ln) (.call none (.inl 9) (some (tail,31,37)) : HolProg 64) =
    .call none (.inl 9) (some (tail,31,37)) := by simp [comp, tail]
example : comp (sptInsert 7 4 .ln)
    (.call (some (tail,2,3,4)) (.inl 9) (some (tail,31,37)) : HolProg 64) =
    .call (some (.rawCall 7,2,3,4)) (.inl 9) (some (.rawCall 7,31,37)) := by simp [comp, compSeq, destCase, tail, sptInsert, sptLookup]
end Flapjack.Test.StackRawCallNativeParity
