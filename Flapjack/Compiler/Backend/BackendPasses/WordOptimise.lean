import Flapjack.Compiler.Backend.BackendPasses.Word
import Flapjack.Compiler.Backend.WordToWord.FastCompile
import Flapjack.Compiler.Backend.RegAlloc.Executable

/-! Capture WordLang optimization and allocation stages from
`backend_passesScript.sml`. The executable allocator replacement is the
same one used by the ordinary RISC-V compiler. Display correspondence and
the remaining stack/target explorer stages are still open. -/
namespace Flapjack.Compiler.Backend.BackendPasses
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm

abbrev WordFunctions := List (Nat × Nat × WordLangProgHOL (BitVec 64))

/-- The original per-pass WordLang snapshots and remaining allocation oracle. -/
structure WordOptimiseStages where
  simp : WordFunctions
  inst : WordFunctions
  ssa : WordFunctions
  firstDead : WordFunctions
  cse : WordFunctions
  copy : WordFunctions
  twoReg : WordFunctions
  reachable : WordFunctions
  finalDead : WordFunctions
  allocated : WordFunctions
  remainingOracle : List (Option (Spt Nat))
  names : Spt MlString

private def mapBody (f : Nat → WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64))
    (ps : WordFunctions) : WordFunctions :=
  ps.map fun (name, arity, p) => (name, arity, f arity p)

/-- Apply the executable word passes in CakeML's stage order. -/
def captureWordOptimise (asm : AsmConfigExact 64) (config : WordToWord.Config)
    (stage : WordStage) : WordOptimiseStages :=
  let simp := mapBody (fun _ p => WordSimp.compileExp p) stage.functions
  let inst := mapBody (fun _ p => WordInst.instSelectExecutable asm (maxVarHOL p + 1) p) simp
  let ssa := mapBody (fun arity p => WordAlloc.fullSsaCcTrans arity p) inst
  let firstDead := mapBody (fun _ p => WordAlloc.removeDeadProg p) ssa
  let cse := mapBody (fun _ p => WordCse.wordCommonSubexpElim p) firstDead
  let copy := mapBody (fun _ p => WordCopy.copyProp p) cse
  let twoReg := mapBody (fun _ p => WordInst.threeToTwoRegProg asm.twoRegArith p) copy
  let reachable := mapBody (fun _ p => WordUnreach.removeUnreach p) twoReg
  let finalDead := mapBody (fun _ p => WordAlloc.removeDeadProg p) reachable
  let (oracles, remaining) := WordToWord.nextNOracle finalDead.length config.colOracle
  let regCount := asm.regCount - (5 + asm.avoidRegs.length)
  let allocated := (finalDead.zip oracles).map fun ((name, arity, p), oracle) =>
    (name, arity, WordRemove.removeMustTerminate
      (WordToWord.wordAllocWith RegAlloc.regAllocExecutable name asm config.regAlg regCount p oracle))
  ⟨simp, inst, ssa, firstDead, cse, copy, twoReg, reachable, finalDead, allocated, remaining, stage.names⟩

private def title (s : String) : List HolChar := (ofString ("# " ++ s ++ "\n\n")).explode

/-- Render all word optimization stages using CakeML's original headings. -/
def wordOptimiseReportBytes (s : WordOptimiseStages) : List HolChar :=
  title "after word_simp" ++ PresLang.Word.functionBytes s.names s.simp ++
  title "after word_inst" ++ PresLang.Word.functionBytes s.names s.inst ++
  title "after word_ssa" ++ PresLang.Word.functionBytes s.names s.ssa ++
  title "after remove_dead in word_ssa" ++ PresLang.Word.functionBytes s.names s.firstDead ++
  title "after word_cse" ++ PresLang.Word.functionBytes s.names s.cse ++
  title "after word_copy" ++ PresLang.Word.functionBytes s.names s.copy ++
  title "after three_to_two_reg from word_inst" ++ PresLang.Word.functionBytes s.names s.twoReg ++
  title "after word_unreach" ++ PresLang.Word.functionBytes s.names s.reachable ++
  title "after remove_dead in word_alloc" ++ PresLang.Word.functionBytes s.names s.finalDead ++
  title "after word_alloc (and remove_must_terminate)" ++ PresLang.Word.functionBytes s.names s.allocated

end Flapjack.Compiler.Backend.BackendPasses
