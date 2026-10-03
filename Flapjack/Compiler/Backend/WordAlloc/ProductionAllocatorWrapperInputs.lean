import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorSetWF
import Flapjack.Compiler.Backend.RegAlloc.ProductionWrapper

namespace Flapjack.WordAlloc
open RegAlloc RiscV.CakeRegAlloc Flapjack.Compiler.Encoders.Asm

/-- The real accepted source encoding discharges every full allocator-wrapper
input premise. Original forced membership and canonical input representation
derive bounds; source set validity is proved from the encoding. The successful
native result and actual colour map are conclusions, not supplied evidence.

This is untagged implementation/caller infrastructure, not an independent HOL
theorem. The actual allocator is applied to the canonical rendering of original
producer inputs here. Equality with actual WordProg clash-tree, forced-pair and
stack-only producers remains a separate whole-route obligation. -/
theorem allocatorWrapperFromEncodedInputs {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (config : AsmConfigExact width) (algorithm : Algorithm)
    (entries : Option (NatInfoMap Nat)) (limit : Nat)
    (moves : List (Nat × (Nat × Nat))) :
    ∃ colours : NatInfoMap Nat,
      regAlloc algorithm (entries.map sptFromAList) limit moves
        (getClashTree native []) (getForced config native []) (getStackOnly native) =
          .success (sptFromAList colours) ∧
      cakeDoRegAlloc algorithm.toProduction
        (entries.map (cakeSpillCostMap
          (cakeMkBij (nativeClashTreeToProduction (getClashTree native []))).nextNode))
        limit moves (nativeClashTreeToProduction (getClashTree native []))
        (getForced config native []) ((sptToAList (getStackOnly native)).map Prod.fst) =
          some colours := by
  have valid := productionAllocator_setsWf program native encoded
  have bounds := allocatorForcedInputBounds native config valid.1
  have composed := regAlloc_production algorithm entries limit moves
    (nativeClashTreeToProduction (getClashTree native []))
    (getForced config native []) ((sptToAList (getStackOnly native)).map Prod.fst) bounds
  have unitEntries : ∀ entries : List (Nat × Unit),
      (entries.map Prod.fst).map (fun name => (name, ())) = entries := by
    intro entries
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
        rcases entry with ⟨key, payload⟩
        cases payload
        simp only [List.map_cons, ih]
  have stackRoundtrip : sptFromAList
      (((sptToAList (getStackOnly native)).map Prod.fst).map (fun name => (name, ()))) =
      getStackOnly native := by
    rw [unitEntries]
    exact (sptEqThm _ _ ⟨sptWfFromAList _, valid.2⟩).mpr
      (fun key => sptLookup_sptFromAList_sptToAList key _)
  simpa only [clashTreeCodec_roundtrip _ valid.1, stackRoundtrip] using composed

end Flapjack.WordAlloc
