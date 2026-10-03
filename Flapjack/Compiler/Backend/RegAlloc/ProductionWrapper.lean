import Flapjack.Compiler.Backend.RegAlloc.ProductionInitializer
import Flapjack.Compiler.Backend.RegAlloc.ProductionMovePreparation
import Flapjack.Compiler.Backend.RegAlloc.ProductionAllocLoop
import Flapjack.Compiler.Backend.RegAlloc.ProductionExtraction
import Flapjack.Compiler.Backend.RegAlloc.Allocator

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-! Complete actual/native allocator composition. These are implementation
correspondence declarations without independent HOL originals. The native
wrapper already has its own reviewed source tag; the actual WordLang producer
correspondence is a separate obligation. -/

/-- Constructor-for-constructor implementation codec, with no independent
HOL declaration; both allocator choices are retained. -/
def Algorithm.toProduction : Algorithm → CakeAlgorithm
  | .Simple => .simple
  | .IRC => .irc

private theorem bind_ret_eq {value : Type} (computation : M State value StateException) :
    bind computation ret = computation := by
  funext state
  cases result : computation state with
  | mk outcome next => cases outcome <;> simp only [Translator.Monadic.MonadBase.bind, result, ret]

/-- The complete original wrapper succeeds with exactly the executed colour
map. The only bound is on original forced inputs through the real produced
bijection; selected-move bounds and all successful phase results are derived.
No target evaluation, supplied output map or post-state relation is assumed. -/
theorem regAlloc_production (algorithm : Algorithm) (entries : Option (NatInfoMap Nat))
    (limit : Nat) (moves : List (Nat × (Nat × Nat))) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (stackOnly : List Nat)
    (forcedBounds : ∀ pair ∈ forced,
      cakeSpDefaultIndexed (cakeSpDefaultIndex (cakeMkBij tree).toAllocator) pair.1 <
        (cakeMkBij tree).nextNode ∧
      cakeSpDefaultIndexed (cakeSpDefaultIndex (cakeMkBij tree).toAllocator) pair.2 <
        (cakeMkBij tree).nextNode) :
    ∃ colours : NatInfoMap Nat,
      regAlloc algorithm (entries.map sptFromAList) limit moves
        (productionClashTreeToNative tree) forced
        (sptFromAList (stackOnly.map (fun name => (name, ())))) =
          .success (sptFromAList colours) ∧
      cakeDoRegAlloc algorithm.toProduction
        (entries.map (cakeSpillCostMap (cakeMkBij tree).nextNode))
        limit moves tree forced stackOnly = some colours := by
  let initial := cakeInitRaState tree forced stackOnly
  let renamed := moves.map (cakeUpdateMove
    (cakeAllocatorIndexLookup (cakeAllocatorIndex (cakeMkBij tree).toAllocator)))
  let admitted := filterReversed
    (fun move => cakeFullConsistencyOk initial limit move.2.1 move.2.2) renamed
  let selected := if algorithm = .Simple then [] else admitted
  obtain ⟨native, initialRun, initialGood, initialRel⟩ :=
    initializer_production tree forced stackOnly forcedBounds
  have initialDim : initial.dim = (cakeMkBij tree).nextNode := rfl
  have dimension : native.dim = (cakeMkBij tree).nextNode :=
    initialRel.dimension.symm.trans initialDim
  have admittedBounds := admittedMoves_bounds initial limit renamed
  have selectedBounds : ∀ move ∈ selected,
      move.2.1 < native.dim ∧ move.2.2 < native.dim := by
    intro move member
    dsimp only [selected] at member
    split at member
    · simp at member
    · simpa only [← initialRel.dimension] using admittedBounds move member
  have filterRun := fullConsistencyFilter_production limit renamed initialRel initialGood []
  simp only [List.append_nil] at filterRun
  obtain ⟨allocated, allocationRun, allocationGood, allocationDim, allocationRel⟩ :=
    doAlloc1_production selected entries limit initialRel initialGood selectedBounds
  let initialized := cakeInitAlloc1Heu selected limit initial
  let allocatedActual := cakeRptDoStep (entries.map (cakeSpillCostMap initial.dim))
    limit initialized.1 initialized.2
  obtain ⟨final, colourRun, finalGood, finalDim, finalRel⟩ :=
    colouringExtract_production tree limit renamed allocatedActual.stack
      allocationRel allocationGood (dimension.symm.trans allocationDim)
  let table := cakeResortMovesSp
    (cakeMovesToSp renamed (CakeNodeMap.ofSize (cakeMkBij tree).nextNode))
  let finalActual := cakeAssignStemps limit
    (fun s n bads => cakeNegBiasedPref s limit table n bads)
    (cakeAssignAtemps limit allocatedActual.stack
      (fun s n ks => cakeBiasedPref s table n ks) allocatedActual)
  let colours := cakeExtractColor finalActual (cakeMkBij tree).toAllocator
  refine ⟨colours, ?_, ?_⟩
  · have renamedEq := allocatorMoves_production tree moves
    rw [mkBij_production] at renamedEq
    unfold regAlloc regAllocAux
    rw [mkBij_production]
    change runIraState _ (initializerIraSeed (cakeMkBij tree).nextNode) = _
    rw [runInitializerSeed_eq]
    unfold Translator.Monadic.MonadBase.run
    rw [← mkBij_production]
    change (doRegAlloc algorithm (entries.map sptFromAList) limit moves
      (productionClashTreeToNative tree) forced
      (sptFromAList (stackOnly.map (fun name => (name, ()))))
      (mkBij (productionClashTreeToNative tree))
      (initializerNativeSeed (cakeMkBij tree).nextNode)).1 = .success (sptFromAList colours)
    simp only [doRegAlloc, bind_ret_eq]
    simp only [initialRun, ignoreBind, ret,
      Translator.Monadic.MonadBase.bind]
    rw [mkBij_production, ← renamedEq]
    change (bind (stExFilter
      (fun move => fullConsistencyOk limit move.2.1 move.2.2) renamed [])
      (fun filtered => bind (doAlloc1 (if algorithm = .Simple then [] else filtered)
        (entries.map sptFromAList) limit) (fun nodes =>
          ignoreBind (assignAtemps limit nodes (biasedPref (resortMoves (movesToSp renamed .ln))))
            (ignoreBind (assignStemps limit (negBiasedPref limit (resortMoves (movesToSp renamed .ln))))
              (extractColor (sptFromAList (cakeMkBij tree).toAllocator))))) native).1 = _
    simp only [Translator.Monadic.MonadBase.bind, filterRun]
    change (bind (doAlloc1 selected (entries.map sptFromAList) limit)
      (fun nodes => ignoreBind
        (assignAtemps limit nodes (biasedPref (resortMoves (movesToSp renamed .ln))))
        (ignoreBind (assignStemps limit (negBiasedPref limit (resortMoves (movesToSp renamed .ln))))
          (extractColor (sptFromAList (cakeMkBij tree).toAllocator)))) native).1 = _
    simp only [Translator.Monadic.MonadBase.bind, allocationRun]
    exact congrArg Prod.fst colourRun
  · have actualRun : cakeDoRegAlloc algorithm.toProduction
        (entries.map (cakeSpillCostMap (cakeMkBij tree).nextNode))
        limit moves tree forced stackOnly =
        (if finalActual.failure.isSome then none else some colours) := by
      cases algorithm <;> rfl
    rw [actualRun, finalRel.failure]
    rfl

end Flapjack.RegAlloc
