import Flapjack.Pancake.LoopToWord.CompFuncCodecDomain

namespace Flapjack.Test.LoopToWordSourceCodec
open Flapjack

/-! Kernel fixtures for full source-output codec closure. These test the real
routed compiler and rejection distinction, not HOL execution equivalence. -/

example {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (body : LoopProg (BitVec width)) :
    (wordLangProgToHOL (loopToWordCompFuncRouted name parameters body)).isSome = true :=
  wordLangProgToHOL_loopToWordCompFuncRouted_isSome name parameters body

private def nested (width : Nat) : LoopProg (BitVec width) :=
  .seq (.primitive [18, 22] .addCarry [2, 4, 6])
    (.loop [2, 4] (.call (some ([18], [22])) (some 100) [2, 4]
      (some (40, .raise 40, .return [18, 22], [2, 4]))) [18, 22])

example : (wordLangProgToHOL (loopToWordCompFuncRouted 73 [2, 4]
    (nested 1))).isSome = true :=
  wordLangProgToHOL_loopToWordCompFuncRouted_isSome _ _ _

example : (wordLangProgToHOL (loopToWordCompFuncRouted 73 [2, 4]
    (nested 64))).isSome = true :=
  wordLangProgToHOL_loopToWordCompFuncRouted_isSome _ _ _

example : (wordLangProgToHOL (loopToWordCompFuncRouted 73 [2, 4]
    (nested 80))).isSome = true :=
  wordLangProgToHOL_loopToWordCompFuncRouted_isSome _ _ _

-- A non-byte-ranged FFI name exercises the compatibility route. Acceptance
-- here is a syntax-codec claim, not byte-observable FFI correctness.
example : (wordLangProgToHOL (loopToWordCompFuncRouted 91 []
    (.ffi "λ" 2 4 6 8 [10] : LoopProg (BitVec 64)))).isSome = true :=
  wordLangProgToHOL_loopToWordCompFuncRouted_isSome _ _ _

-- Malformed primitive lists remain in the theorem's unrestricted domain.
example : (wordLangProgToHOL (loopToWordCompFuncRouted 91 []
    (.primitive [2] .addCarry [4] : LoopProg (BitVec 64)))).isSome = true :=
  wordLangProgToHOL_loopToWordCompFuncRouted_isSome _ _ _

-- Unconditional source closure does not make the wider Word extension valid.
example : wordLangProgToHOL
    (.inst (.arith (.addCarry 1 2 3 4 5)) : WordProg (BitVec 64)) = none := by rfl

end Flapjack.Test.LoopToWordSourceCodec
