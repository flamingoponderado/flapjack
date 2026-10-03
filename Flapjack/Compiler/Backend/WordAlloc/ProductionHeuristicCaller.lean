import Flapjack.Compiler.Backend.WordAlloc.ProductionActualInputs
import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicOutput

namespace Flapjack.WordAlloc
open RegAlloc RiscV.CakeRegAlloc Flapjack.Compiler.Encoders.Asm

/-! All actual allocator analysis inputs are source-derived here, including
heuristic moves and spill costs. This is an implementation correspondence to
the existing native allocator caller, not a new HOL declaration. Algorithm
and heuristic-mode scalar choices remain explicit; the executed default guard,
SSA transport and allocated-program output are separate obligations. -/

theorem allocatorWrapperFromCompleteActualInputs {width : Nat} [NeZero width]
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
        (cakeGetStackOnly program) = some colours := by
  have heuristic := getHeuristics_production mode functionName program native encoded
  have composed := allocatorWrapperFromActualProducers program native encoded config target
    algorithm (wordGetHeuristics mode functionName program).2 limit
    ((wordGetHeuristics mode functionName program).1.map wordMoveToTriple)
  have moves := congrArg Prod.fst heuristic
  have costs := congrArg Prod.snd heuristic
  change (wordGetHeuristics mode functionName program).1.map wordMoveToTriple =
    (getHeuristics mode functionName native).1 at moves
  change (wordGetHeuristics mode functionName program).2.map sptFromAList =
    (getHeuristics mode functionName native).2 at costs
  simpa only [moves, costs] using composed

end Flapjack.WordAlloc
