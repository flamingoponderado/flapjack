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

-- Every actual source input executes the native branch, without a supplied
-- encoding-success, compilation-success or successful allocation premise.
example {width : Nat} [NeZero width] (name : Nat) (parameters wordParameters : List Nat)
    (body : LoopProg (BitVec width)) :
    CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedLimit name wordParameters
        (wordBeforeSsaAllocatorBody (loopToWordCompFuncRouted name parameters body)) =
      CakeRegAlloc.cakeAllocateWordFunctionAfterDeadNativeLimit name wordParameters
        (wordBeforeSsaAllocatorBody (loopToWordCompFuncRouted name parameters body)) :=
  sourceAllocatorInput_usesNativeLimit name parameters body wordParameters


-- These statements name the actual PipelineDiagnostics source function,
-- rather than the separate loopToWordCompFuncRouted variant.
example {width : Nat} [NeZero width] (name : Nat) (parameters wordParameters : List Nat)
    (body : LoopProg (BitVec width)) :
    CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSA name wordParameters
        (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) =
      CakeRegAlloc.cakeAllocateWordFunctionAfterDeadNativeSSA name wordParameters
        (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) :=
  executedSourceAllocatorInput_usesNativeSSA name parameters body wordParameters

example {width : Nat} [NeZero width] (name : Nat) (parameters wordParameters : List Nat)
    (body : LoopProg (BitVec width)) :
    CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedLimit name wordParameters
        (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) =
      CakeRegAlloc.cakeAllocateWordFunctionAfterDeadNativeLimit name wordParameters
        (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) :=
  executedSourceAllocatorInput_usesNativeLimit name parameters body wordParameters

example : (wordLangProgToHOL (wordBeforeSsaAllocatorBody
    (LoopToWord.loopToWordCompFunc 73 [2,4] (nested 1)))).isSome = true :=
  executedSourceAllocatorInput_isSome _ _ _
example : (wordLangProgToHOL (wordBeforeSsaAllocatorBody
    (LoopToWord.loopToWordCompFunc 73 [2,4] (nested 64)))).isSome = true :=
  executedSourceAllocatorInput_isSome _ _ _
example : (wordLangProgToHOL (wordBeforeSsaAllocatorBody
    (LoopToWord.loopToWordCompFunc 73 [2,4] (nested 80)))).isSome = true :=
  executedSourceAllocatorInput_isSome _ _ _
example : (wordLangProgToHOL (wordBeforeSsaAllocatorBody
    (LoopToWord.loopToWordCompFunc 91 []
      (.seq (.ffi "λ" 2 4 6 8 [10]) (.primitive [2] .addCarry [4]) :
        LoopProg (BitVec 64))))).isSome = true :=
  executedSourceAllocatorInput_isSome _ _ _

-- Arbitrary Word inputs have a real rejection branch. A rejection proves
-- compatibility routing, not successful native SSA or allocation.
example {width : Nat} [NeZero width] (name : Nat) (parameters : List Nat)
    (program : WordProg (BitVec width))
    (rejected : wordLangProgToHOL (wordBeforeSsaAllocatorBody program) = none) :
    CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSA name parameters
        (wordBeforeSsaAllocatorBody program) =
      CakeRegAlloc.cakeAllocateWordFunctionAfterDead name parameters
        (wordBeforeSsaAllocatorBody program) :=
  CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSA_rejected _ _ _ rejected

end Flapjack.Test.ProductionPreSsaCodec
