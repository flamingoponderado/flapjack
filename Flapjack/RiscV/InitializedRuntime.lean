import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.WordToStack.NativeStubs
import Flapjack.RiscV.Lab
import Flapjack.Compiler.Backend.StackToLab.RuntimeLabels
import Flapjack.Compiler.Backend.DataToWord.MaxHeapLimit

/-! Executed runtime initialization infrastructure, with no standalone HOL
original. This uses the reviewed whole StackRemove/native naming/section
composition and derives all relocation labels from its actual output. The
legacy fixed runtime table is not a source for this linker.
-/
namespace Flapjack.RiscV

/-- Literal data component of original riscv_configScript.sml:51, an SML
quotation used by riscv_backend_config_def, with the actual Pancake no-GC
override from compilerScript.sml:744–747. This is its data-field projection,
not a tagged port of the whole backend configuration update. -/
def initializedRuntimeDataConfig : Flapjack.Compiler.Backend.DataToWord.Config :=
  { tagBits := 4, lenBits := 4, padBits := 2, lenSize := 32,
    hasDiv := true, hasLongdiv := false, hasFpOps := false, hasFpTern := false,
    be := false, callEmptyFfi := false, gcKind := .none }

/-- RV64 Pancake runtime composition, including the original three entry stubs.
The source bodies arrive through the existing broad allocation/raw-call/long-div
preparation. Their legacy support entries are replaced by native None-GC,
Raise and StoreConsts definitions, and global labels are injectively normalized.
The native allocation pass then builds the original GC support and feeds the
whole native StackRemove/name/section composition. This boundary does not claim
to replace the upstream broad compiler passes or establish their simulation. -/
def initializedRuntimeLab? {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start registerCount : Nat)
    (programs : List (Nat × StackProg Nat)) : Option (LabProgram (Word width)) := do
  let native ← Flapjack.Compiler.Backend.StackToLab.InitializedProduction.nativeInputs? programs
  let source := Flapjack.Compiler.Backend.StackToLab.RuntimeLabels.originalInputs
    (native.filter (fun entry => entry.1 >= 3))
  let support :=
    [(Flapjack.raiseStubLocation, Flapjack.Compiler.Backend.WordToStack.Native.raiseStubNative false registerCount),
     (Flapjack.storeConstsStubLocation, Flapjack.Compiler.Backend.WordToStack.Native.storeConstsStubNative registerCount)]
  let native := Flapjack.Compiler.Backend.StackAlloc.compile
    initializedRuntimeDataConfig (support ++ source)
  let heap := 2 * Flapjack.Compiler.Backend.DataToWord.maxHeapLimit width
    initializedRuntimeDataConfig - 1
  Flapjack.Compiler.Backend.StackToLab.InitializedProduction.compileNative?
    jump bounds false heap pointer
    (Flapjack.Compiler.Backend.StackToLab.RuntimeLabels.originalSection start)
    Flapjack.Compiler.Backend.RiscVConfig.riscvNames native

/-- Stored-length convergence over the complete actual program. Exhausting the
relocation budget fails, matching HOL `remove_labels_loop`; an unconverged
program must never reach instruction lowering. -/
def initializedRuntimeEncodeStable [NeZero width] (fuel : Nat)
    (context : WordFfiContext) (haltPc : Nat) (program : LabProgram (Word width)) :
    Option (LabProgram (Word width)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let labels := labLabelIndexOf (labCollectStoredProgramLabels 0 program)
      let next := labEncodeStoredProgram context labels 0 0 haltPc program
      if labStoredLineLengths next == labStoredLineLengths program then some next
      else initializedRuntimeEncodeStable fuel context haltPc next

/-- Both relocation sweeps retain original maximum observed instruction slots;
all entry/GC/raise/store/source labels come from the generated program. -/
def compileLabProgramLinkedWithNativeInitialization [NeZero width]
    (context : WordFfiContext) (program : LabProgram (Word width)) :
    Option (List (Nat × Word width × List (Instruction width))) := do
  let initial := labInitialStoredProgram program
  let encoded ← initializedRuntimeEncodeStable 8 context (labStoredProgramLength initial) initial
  let relabelled := labUpdateStoredLabelLengths 0 encoded
  let final ← initializedRuntimeEncodeStable 8 context (labStoredProgramLength relabelled) relabelled
  let labels := labLabelIndexOf (labCollectStoredProgramLabels 0 final)
  compileLabProgramLinkedWithStoredLengthsAux context labels 0 0
    (labStoredProgramLength final) final

end Flapjack.RiscV
