import Flapjack.RiscV.ArtifactFormat
namespace Flapjack.RiscV
/-- Frozen pre-wiring dispatcher for the unconditional behavior-preservation
proof. Flapjack-specific regression infrastructure, not a HOL port or an
executed alternative. -/
private def previousRuntimeSymbolName (crepe : List (CompiledFunction (RiscV.Word 64)))
    (ordinal label : Nat) : String :=
  if label == 0 then s!"cml__Init_{ordinal}"
  else if label == 1 then s!"cml__Halt0_{ordinal}"
  else if label == 2 then s!"cml__Halt2_{ordinal}"
  else if label == Flapjack.Compiler.Backend.StackLang.gcStubLocation then s!"cml__GC_{ordinal}"
  else if label == Flapjack.raiseStubLocation then s!"cml__Raise_{ordinal}"
  else if label == Flapjack.storeConstsStubLocation then s!"cml__StoreConsts_{ordinal}"
  else if label == Flapjack.firstLoopName then s!"cml_generated_main_{ordinal}"
  else match crepe[label - Flapjack.firstLoopName]? with
    | some function => s!"cml_{sanitizeSymbolName function.name}_{ordinal}"
    | none => s!"cml_section_{ordinal}"

/-- The executed table dispatcher preserves all prior outputs for arbitrary
source functions, ordinal and label. No finite input/sample premise. -/
theorem initializedRuntimeSymbolName_preserved
    (crepe : List (CompiledFunction (RiscV.Word 64))) (ordinal label : Nat) :
    initializedRuntimeSymbolName crepe ordinal label =
      previousRuntimeSymbolName crepe ordinal label := by
  by_cases h0 : label = 0
  · subst label; rfl
  by_cases h1 : label = 1
  · subst label; rfl
  by_cases h2 : label = 2
  · subst label; rfl
  by_cases h4 : label = 4
  · subst label; rfl
  by_cases h5 : label = 5
  · subst label; rfl
  by_cases h6 : label = 6
  · subst label; rfl
  simp [initializedRuntimeSymbolName, initializedRuntimeStubName,
    previousRuntimeSymbolName, Flapjack.Compiler.Backend.StackRemove.stubNames,
    Flapjack.Compiler.Backend.StackAlloc.stubNames,
    Flapjack.Compiler.Backend.WordToStack.stubNames,
    Flapjack.Compiler.Backend.StackLang.gcStubLocation,
    Flapjack.raiseStubLocation, Flapjack.storeConstsStubLocation,
    Flapjack.wordNumStubs, Flapjack.stackNumStubs,
    h0, h1, h2, h4, h5, h6, Ne.symm h0, Ne.symm h1, Ne.symm h2,
    Ne.symm h4, Ne.symm h5, Ne.symm h6]
  rfl
/-- Complete symbol-line output preserves addresses, lengths and ordinals for
arbitrary initialized sections, not merely the six runtime-name examples. -/
theorem initializedRuntimeSymbolLines_preserved
    (crepe : List (CompiledFunction (RiscV.Word 64)))
    (sections : List (EncodedRiscVSection 64)) :
    initializedRuntimeSymbolLines crepe sections =
      sections.zipIdx.map (fun (entry, ordinal) =>
        s!"    makesym({previousRuntimeSymbolName crepe ordinal entry.label}, {entry.address.toNat}, {entry.bytes.length})") := by
  unfold initializedRuntimeSymbolLines
  apply congrArg (fun f => List.map f sections.zipIdx)
  funext pair
  rcases pair with ⟨entry, ordinal⟩
  dsimp only
  rw [initializedRuntimeSymbolName_preserved]
end Flapjack.RiscV
