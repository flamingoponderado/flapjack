import Flapjack.Compiler.Backend.WordAlloc.ProductionColouringProgram
import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicCaller
import Flapjack.Compiler.Backend.WordAlloc.TotalColour
import Flapjack.Compiler.Backend.RegAlloc.ProductionInitTags
import Flapjack.RiscV.OracleAllocator

namespace Flapjack.WordAlloc
open RegAlloc RiscV.CakeRegAlloc Flapjack.Compiler.Encoders.Asm

/-! Actual allocated-program output, using the actual total-colour lookup.
These are implementation correspondence theorems with no separate HOL
original. The reviewed native total colouring and program colouring retain
their own tags; all output facts below follow from accepted input encoding. -/

theorem totalColour_production (entries : NatInfoMap Nat) (key : Nat) :
    RiscV.CakeAlloc.totalColour entries key = totalColour (sptFromAList entries) key := by
  have defaults : RiscV.CakeAlloc.spDefault entries key =
      Flapjack.spDefault (sptFromAList entries) key := by
    rw [← Flapjack.spDefaultIndexed_corresponds]
    exact RegAlloc.tagDecoder_production entries key
  calc
    RiscV.CakeAlloc.totalColour entries key =
        2 * Flapjack.spDefault (sptFromAList entries) key := by
          rw [RiscV.CakeAlloc.totalColour, defaults]
    _ = totalColour (sptFromAList entries) key :=
      (congrFun (totalColourAlt (sptFromAList entries)) key).symm

theorem totalColourProgram_production {width : Nat} [NeZero width]
    (entries : NatInfoMap Nat) (program : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    wordLangProgToHOL (wordApplyTotalColour entries program) =
      some (applyColour (totalColour (sptFromAList entries)) native) := by
  unfold wordApplyTotalColour
  rw [funext (totalColour_production entries)]
  exact colouringProgram_production _ program native encoded

theorem allocatorWrapperWithActualOutput {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (config : AsmConfigExact width) (target : config.isa = .riscv)
    (algorithm : Algorithm) (mode functionName limit : Nat) :
    ∃ colours : NatInfoMap Nat,
      regAlloc algorithm (getHeuristics mode functionName native).2 limit
        (getHeuristics mode functionName native).1
        (getClashTree native []) (getForced config native []) (getStackOnly native) =
          .success (sptFromAList colours) ∧
      cakeDoRegAlloc algorithm.toProduction
        ((wordGetHeuristics mode functionName program).2.map
          (cakeSpillCostMap (cakeMkBij (wordClashTree program [])).nextNode))
        limit ((wordGetHeuristics mode functionName program).1.map wordMoveToTriple)
        (wordClashTree program []) (cakeGetForced program)
        (cakeGetStackOnly program) = some colours ∧
      wordLangProgToHOL (wordApplyTotalColour colours program) =
        some (applyColour (totalColour (sptFromAList colours)) native) := by
  obtain ⟨colours, nativeRun, actualRun⟩ :=
    allocatorWrapperFromCompleteActualInputs program native encoded config target
      algorithm mode functionName limit
  exact ⟨colours, nativeRun, actualRun, totalColourProgram_production colours program native encoded⟩

end Flapjack.WordAlloc
