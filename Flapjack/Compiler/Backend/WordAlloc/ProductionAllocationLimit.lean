import Flapjack.Compiler.Backend.WordAlloc.ProductionLimitVar
import Flapjack.Compiler.Backend.WordAlloc.ProductionRemoveDead
import Flapjack.RiscV.WordDeadCode

namespace Flapjack.RiscV.CakeRegAlloc

/-- Native full-program limit feeding the actual raw allocator implementation.
Codec failure remains explicit. This caller adapter is not yet installed in the
source pipeline and is not a HOL theorem port or source-image acceptance claim. -/
def cakeAllocateWordFunctionNativeLimit {width : Nat} [NeZero width]
    (parameters : List Nat) (program : WordProg (BitVec width))
    (currentFunction k : Nat) :
    Option (WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState) :=
  (wordLangProgToHOL program).bind (fun native =>
    cakeAllocateWordFunctionFromLimit (Compiler.Backend.WordAlloc.limitVar native)
      parameters program currentFunction k)

/-- Equality of the complete partial raw allocation result, without assuming
successful allocation, colouring or output facts. Flapjack infrastructure. -/
theorem cakeAllocateWordFunctionNativeLimit_eq {width : Nat} [NeZero width]
    (parameters : List Nat) (program : WordProg (BitVec width))
    (currentFunction k : Nat) :
    cakeAllocateWordFunctionNativeLimit parameters program currentFunction k =
      (wordLangProgToHOL program).bind (fun _ =>
        cakeAllocateWordFunction parameters program currentFunction k) := by
  have limit := wordSsaLimitVar_codec parameters program
  cases encoded : wordLangProgToHOL program with
  | none => simp [cakeAllocateWordFunctionNativeLimit, encoded]
  | some native =>
      simp only [encoded, Option.map_some, Option.some.injEq] at limit
      simp only [cakeAllocateWordFunctionNativeLimit, encoded, Option.bind_some, limit]
      rfl

/-- Native limit feeding the shared cleanup/IRC/retained-colour implementation,
with both liveness-based dead-code passes run by the reviewed `removeDeadProg`
(`wordRemoveDeadProgramViaHOL`). The complete input program is encoded, not a
synthetic maximum-only program. Codec rejection stays explicit; universal input
acceptance remains open. Flapjack production infrastructure with no HOL original. -/
def cakeAllocateWordFunctionAfterDeadWithColourNativeLimit
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width)) :
    Option (CakeAllocationWithColour (BitVec width)) :=
  (wordLangProgToHOL program).bind (fun native =>
    cakeAllocateWordFunctionAfterDeadWithColourFromLimitWith wordRemoveDeadProgramViaHOL
      (Compiler.Backend.WordAlloc.limitVar native) currentFunction parameters program)

/-- Legacy tuple projection of the same native-limit allocator adapter.
Flapjack production infrastructure; it is not yet the executed source route. -/
def cakeAllocateWordFunctionAfterDeadNativeLimit
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width)) :
    Option (WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState) :=
  (cakeAllocateWordFunctionAfterDeadWithColourNativeLimit
    currentFunction parameters program).map CakeAllocationWithColour.toLegacy

/-- Executed fixed-width allocator boundary. Every codec-accepted complete
input obtains its counter from reviewed native `limitVar` and runs both
dead-code passes through reviewed `removeDeadProg`. The broader Word extension
keeps its historical allocation behavior when the native codec rejects it; this
is compatibility, not a performance exception. Source-input closure separately
proves source functions never take that branch. -/
def cakeAllocateWordFunctionAfterDeadRoutedLimit
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width)) :
    Option (WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState) :=
  match wordLangProgToHOL program with
  | none => cakeAllocateWordFunctionAfterDead currentFunction parameters program
  | some native =>
      (cakeAllocateWordFunctionAfterDeadWithColourFromLimitWith wordRemoveDeadProgramViaHOL
        (Compiler.Backend.WordAlloc.limitVar native) currentFunction parameters program).map
        CakeAllocationWithColour.toLegacy

/-- A codec-rejected input keeps the complete historical allocation result,
including every failure. Flapjack routing infrastructure, not a HOL
allocation-correctness theorem. -/
theorem cakeAllocateWordFunctionAfterDeadRoutedLimit_rejected
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width))
    (rejected : wordLangProgToHOL program = none) :
    cakeAllocateWordFunctionAfterDeadRoutedLimit currentFunction parameters program =
      cakeAllocateWordFunctionAfterDead currentFunction parameters program := by
  simp [cakeAllocateWordFunctionAfterDeadRoutedLimit, rejected]

/-- Accepted input executes precisely the native full-program limit adapter,
not the compatibility branch. The premise is input codec acceptance only. -/
theorem cakeAllocateWordFunctionAfterDeadRoutedLimit_native
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    cakeAllocateWordFunctionAfterDeadRoutedLimit currentFunction parameters program =
      cakeAllocateWordFunctionAfterDeadNativeLimit currentFunction parameters program := by
  cases encoded : wordLangProgToHOL program with
  | none => simp [encoded] at accepted
  | some native =>
      simp [cakeAllocateWordFunctionAfterDeadRoutedLimit,
        cakeAllocateWordFunctionAfterDeadNativeLimit,
        cakeAllocateWordFunctionAfterDeadWithColourNativeLimit, encoded]

end Flapjack.RiscV.CakeRegAlloc
