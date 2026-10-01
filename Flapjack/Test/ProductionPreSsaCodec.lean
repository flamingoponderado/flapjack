import Flapjack.Compiler.Backend.WordToStack.ProductionPreSsaDomain

namespace Flapjack.Test.ProductionPreSsaCodec
open Flapjack RiscV WordProgCarrierCodec

/-! Kernel fixtures for actual allocator-input acceptance. These are codec
claims only, not executable parity or HOL simulation tests. -/
example {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) :
    (wordLangProgToHOL (wordBeforeSsaAllocatorBody
      (loopToWordCompFuncRouted name parameters body))).isSome = true :=
  wordLangProgToHOL_sourceAllocatorInput_isSome name parameters body

private def nested (width : Nat) : LoopProg (BitVec width) :=
  .seq (.primitive [18, 22] .addCarry [2, 4, 6])
    (.loop [2, 4] (.call (some ([18], [22])) (some 100) [2, 4]
      (some (40, .raise 40, .return [18, 22], [2, 4]))) [18, 22])

example : (wordLangProgToHOL (wordBeforeSsaAllocatorBody
    (loopToWordCompFuncRouted 73 [2, 4] (nested 1)))).isSome = true :=
  wordLangProgToHOL_sourceAllocatorInput_isSome _ _ _
example : (wordLangProgToHOL (wordBeforeSsaAllocatorBody
    (loopToWordCompFuncRouted 73 [2, 4] (nested 64)))).isSome = true :=
  wordLangProgToHOL_sourceAllocatorInput_isSome _ _ _
example : (wordLangProgToHOL (wordBeforeSsaAllocatorBody
    (loopToWordCompFuncRouted 73 [2, 4] (nested 80)))).isSome = true :=
  wordLangProgToHOL_sourceAllocatorInput_isSome _ _ _

-- Full input syntax includes non-byte-ranged names and malformed primitive
-- lists. No encoding-success or byte-name premise is hidden in this result.
example : (wordLangProgToHOL (wordBeforeSsaAllocatorBody
    (loopToWordCompFuncRouted 91 []
      (.seq (.ffi "λ" 2 4 6 8 [10]) (.primitive [2] .addCarry [4]) :
        LoopProg (BitVec 64))))).isSome = true :=
  wordLangProgToHOL_sourceAllocatorInput_isSome _ _ _

-- The unsupported wider Word extension stays outside the input domain.
example : supportsCodec
    (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 64)) = false := by
  simp [supportsCodec]

end Flapjack.Test.ProductionPreSsaCodec
