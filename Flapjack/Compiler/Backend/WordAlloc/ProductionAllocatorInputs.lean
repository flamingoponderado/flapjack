import Flapjack.Compiler.Backend.WordAlloc.Proofs.GetForced
import Flapjack.Compiler.Backend.RegAlloc.ProductionInitializer

namespace Flapjack.WordAlloc
open RegAlloc RiscV.CakeRegAlloc Flapjack.Compiler.Encoders.Asm

/-- Original WordAlloc forced endpoints have bounded actual allocator indices.
The already ported source membership theorem, exact input codec and produced
bijection derive the bounds; no successful allocator result or desired graph
is assumed. This is untagged caller-premise discharge, not a duplicate HOL
get_forced theorem. Set well-formedness and actual program producer linkage
remain separate source boundary obligations. -/
theorem allocatorForcedInputBounds {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (config : AsmConfigExact width)
    (wellFormed : NativeClashTreeSetsWf (getClashTree program [])) :
    ∀ pair ∈ getForced config program [],
      cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (nativeClashTreeToProduction (getClashTree program []))).toAllocator)
          pair.1 < (cakeMkBij (nativeClashTreeToProduction (getClashTree program []))).nextNode ∧
      cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (nativeClashTreeToProduction (getClashTree program []))).toAllocator)
          pair.2 < (cakeMkBij (nativeClashTreeToProduction (getClashTree program []))).nextNode := by
  intro pair belongs
  have sourceMembers := getForcedInGetClashTree program [] config pair belongs
  constructor
  · apply producedAllocator_name_bound
    simpa only [clashTreeCodec_roundtrip _ wellFormed] using sourceMembers.1
  · apply producedAllocator_name_bound
    simpa only [clashTreeCodec_roundtrip _ wellFormed] using sourceMembers.2

/-- Original WordAlloc producer inputs discharge the actual initializer's
forced bound condition. Native tree/set well-formedness are genuine carrier
inputs; the full successful result and state relation are conclusions. This
untagged caller theorem does not establish actual WordProg producer equality
or the whole allocator/compilation correctness theorem. -/
theorem allocatorInitializerFromOriginalInputs {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (config : AsmConfigExact width)
    (stackOnly : NumSet) (stackWellFormed : sptWf stackOnly = true)
    (wellFormed : NativeClashTreeSetsWf (getClashTree program [])) :
    ∃ result, initRaState (getClashTree program []) (getForced config program []) stackOnly
        (mkBij (getClashTree program []))
        (initializerNativeSeed (cakeMkBij (nativeClashTreeToProduction (getClashTree program []))).nextNode) =
        (.success (), result) ∧ goodRaState result ∧ ProductionStateRel result
          (cakeInitRaState (nativeClashTreeToProduction (getClashTree program []))
            (getForced config program []) ((sptToAList stackOnly).map Prod.fst)) :=
  initializer_original_production (getClashTree program []) wellFormed
    (getForced config program []) stackOnly stackWellFormed
    (allocatorForcedInputBounds program config wellFormed)

end Flapjack.WordAlloc
