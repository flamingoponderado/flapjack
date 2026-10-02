import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocationLimit
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAMetadata

namespace Flapjack.RiscV.CakeRegAlloc

/-- Actual shared allocator consuming one native full SSA pass. The complete
input is encoded once; native metadata supplies the final state and formals.
No separate HOL declaration has this production API. -/
def cakeAllocateWordFunctionAfterDeadWithColourNativeSSA
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width)) :
    Option (CakeAllocationWithColour (BitVec width)) :=
  (wordLangProgToHOL program).bind fun native =>
    cakeAllocateWordFunctionAfterDeadWithColourWithSsa wordRemoveDeadProgramViaHOL
      (fun count _ => wordFullSsaCcTransNativeWithStateFromHOL count native)
      currentFunction parameters program

/-- Legacy tuple projection retains the actual native SSA metadata and actual
shared allocation result, including every failure. Flapjack infrastructure. -/
def cakeAllocateWordFunctionAfterDeadNativeSSA
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width)) :
    Option (WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState) :=
  (cakeAllocateWordFunctionAfterDeadWithColourNativeSSA
    currentFunction parameters program).map CakeAllocationWithColour.toLegacy

/-- Executed fixed-width full SSA route. The source codec image executes native
setup and body renaming, then the shared cleanup/IRC consumer. The broader Word
extension retains its historical behavior on encoder rejection. Native output
acceptance is proved by the codec closure, not used as a fallback condition. -/
def cakeAllocateWordFunctionAfterDeadRoutedSSA
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width)) :
    Option (WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState) :=
  match wordLangProgToHOL program with
  | none => cakeAllocateWordFunctionAfterDead currentFunction parameters program
  | some native =>
      (cakeAllocateWordFunctionAfterDeadWithColourWithSsa wordRemoveDeadProgramViaHOL
        (fun count _ => wordFullSsaCcTransNativeWithStateFromHOL count native)
        currentFunction parameters program).map CakeAllocationWithColour.toLegacy

/-- Broad extension compatibility, without a successful allocation premise. -/
theorem cakeAllocateWordFunctionAfterDeadRoutedSSA_rejected
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width))
    (rejected : wordLangProgToHOL program = none) :
    cakeAllocateWordFunctionAfterDeadRoutedSSA currentFunction parameters program =
      cakeAllocateWordFunctionAfterDead currentFunction parameters program := by
  simp [cakeAllocateWordFunctionAfterDeadRoutedSSA, rejected]

/-- Complete accepted-input routing equation. Only the input encoder condition
is assumed, not any allocation, output-decoder or target evaluation result. -/
theorem cakeAllocateWordFunctionAfterDeadRoutedSSA_native
    {width : Nat} [NeZero width] (currentFunction : Nat)
    (parameters : List Nat) (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    cakeAllocateWordFunctionAfterDeadRoutedSSA currentFunction parameters program =
      cakeAllocateWordFunctionAfterDeadNativeSSA currentFunction parameters program := by
  cases encoded : wordLangProgToHOL program with
  | none => simp [encoded] at accepted
  | some native =>
      simp [cakeAllocateWordFunctionAfterDeadRoutedSSA,
        cakeAllocateWordFunctionAfterDeadNativeSSA,
        cakeAllocateWordFunctionAfterDeadWithColourNativeSSA, encoded]

end Flapjack.RiscV.CakeRegAlloc
