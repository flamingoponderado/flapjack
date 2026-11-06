import Flapjack.Compiler.Backend.BackendPasses.WordOptimise
import Flapjack.Compiler.Backend.PresLang.Stack
import Flapjack.Compiler.Backend.PresLang.Lab
import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.LabFilter

/-! Capture the stack and labelled-assembly stages from
`backend_passesScript.sml`. This follows the normal width-indexed backend
passes; source-level review of the display representations remains open. -/
namespace Flapjack.Compiler.Backend.BackendPasses
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm

abbrev StackFunctions := List (Nat × StackLang.HolProg 64)

/-- Stack snapshots, resulting labelled program, bitmap and frame metadata. -/
structure StackStages where
  wordToStack : StackFunctions
  rawCall : StackFunctions
  allocated : StackFunctions
  removed : StackFunctions
  named : StackFunctions
  lab : LabSem.LabProgHOL 64
  filtered : LabSem.LabProgHOL 64
  bitmaps : List (BitVec 64)
  wordConfig : WordToStack.Native.Config
  frames : List Nat
  names : Spt MlString

/-- Run the exact width-indexed stack pipeline while retaining its stages. -/
def captureStack (asm : AsmConfigExact 64) (config : Backend.Config)
    (word : WordOptimiseStages) : StackStages :=
  let (bitmaps, wordConfig, frames, stack) :=
    WordToStack.Native.compileNative asm config.stackConf.perfCalls word.allocated
  let rawCall := StackRawCall.compile stack
  let allocated := StackAlloc.compile config.dataConf rawCall
  let maxHeap := 2 * DataToWord.maxHeapLimit 64 config.dataConf - 1
  let sp := asm.regCount - (asm.avoidRegs.length + 3)
  let removed := StackRemove.compileHOL config.stackConf.jump asm.addrOffset
    (StackToLab.isGenGc config.dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation allocated
  let named := StackNames.compileHOL config.stackConf.regNames removed
  let lab := named.map StackToLab.progToSectionHOL
  ⟨stack, rawCall, allocated, removed, named, lab, LabFilter.filterSkip lab, bitmaps, wordConfig, frames, word.names⟩

/-- The captured labelled program is the ordinary stack-to-lab result. -/
theorem captureStack_lab (asm : AsmConfigExact 64) (config : Backend.Config)
    (word : WordOptimiseStages) :
    (captureStack asm config word).lab =
      StackToLab.compile config.stackConf config.dataConf
        (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1)
        (asm.regCount - (asm.avoidRegs.length + 3)) asm.addrOffset
        (captureStack asm config word).wordToStack := by
  rfl

private def title (s : String) : List HolChar := (ofString ("# " ++ s ++ "\n\n")).explode
private def stackBytes (names : Spt MlString) (fs : StackFunctions) : List HolChar :=
  PresLang.Stack.functionBytes names (fs.map fun (n, body) => (n, PresLang.Stack.fromHol body))

/-- Render the five StackLang snapshots, LabLang program and filtered program. -/
def stackReportBytes (s : StackStages) : List HolChar :=
  title "after word_to_stack" ++ stackBytes s.names s.wordToStack ++
  title "after stack_rawcall" ++ stackBytes s.names s.rawCall ++
  title "after stack_alloc" ++ stackBytes s.names s.allocated ++
  title "after stack_remove" ++ stackBytes s.names s.removed ++
  title "after stack_names" ++ stackBytes s.names s.named ++
  title "after stack_to_lab" ++ PresLang.Lab.sectionBytes s.names (PresLang.Lab.fromHol s.lab) ++
  title "after filter_skip" ++ PresLang.Lab.sectionBytes s.names (PresLang.Lab.fromHol s.filtered)

end Flapjack.Compiler.Backend.BackendPasses
