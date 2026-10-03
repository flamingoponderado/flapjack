import Flapjack.Compiler.Backend.WordAlloc.ProductionClashTree
import Flapjack.Compiler.Backend.WordAlloc.ProductionStackOnly

namespace Flapjack.WordAlloc
open RegAlloc RiscV.CakeRegAlloc Flapjack.Compiler.Encoders.Asm

/-- Actual allocator caller using all three source-routed input producers.
Encoder acceptance supplies the clash tree, forced pairs, stack-only set and
forced endpoint bounds; no producer result is assumed. Algorithm, preference
moves and spill-cost associations remain inputs. The complete heuristic
producer, default guard, SSA and allocated-program output route remain separate
obligations. This implementation theorem has no independent HOL original. -/
theorem allocatorWrapperFromActualProducers {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (config : AsmConfigExact width) (target : config.isa = .riscv)
    (algorithm : Algorithm) (entries : Option (NatInfoMap Nat)) (limit : Nat)
    (moves : List (Nat × (Nat × Nat))) :
    ∃ colours : NatInfoMap Nat,
      regAlloc algorithm (entries.map sptFromAList) limit moves
        (getClashTree native []) (getForced config native []) (getStackOnly native) =
          .success (sptFromAList colours) ∧
      cakeDoRegAlloc algorithm.toProduction
        (entries.map (cakeSpillCostMap (cakeMkBij (wordClashTree program [])).nextNode))
        limit moves (wordClashTree program []) (cakeGetForced program)
        (cakeGetStackOnly program) = some colours := by
  have treeEq : productionClashTreeToNative (wordClashTree program []) =
      getClashTree native [] := by
    simpa only [List.map_nil] using clashTree_production program native encoded []
  have forcedEq := getForced_production config target program native encoded
  have bounds : ∀ pair ∈ cakeGetForced program,
      cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (wordClashTree program [])).toAllocator) pair.1 <
        (cakeMkBij (wordClashTree program [])).nextNode ∧
      cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (wordClashTree program [])).toAllocator) pair.2 <
        (cakeMkBij (wordClashTree program [])).nextNode := by
    rw [forcedEq]
    intro pair member
    have sourceMembers := getForcedInGetClashTree native [] config pair member
    constructor
    · apply producedAllocator_name_bound
      rw [treeEq]
      exact sourceMembers.1
    · apply producedAllocator_name_bound
      rw [treeEq]
      exact sourceMembers.2
  have composed := regAlloc_production algorithm entries limit moves
    (wordClashTree program []) (cakeGetForced program)
    (cakeGetStackOnly program) bounds
  have stackEq := stackOnly_production program native encoded
  change sptFromAList ((cakeGetStackOnly program).map (fun name => (name, ()))) = _ at stackEq
  simpa only [treeEq, forcedEq, stackEq] using composed

end Flapjack.WordAlloc
