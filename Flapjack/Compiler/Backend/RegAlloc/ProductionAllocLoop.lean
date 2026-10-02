import Flapjack.Compiler.Backend.RegAlloc.ProductionInitAlloc

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- The executed initializer/repeated-phase/stack slice used by
cakeDoRegAllocFromState implements native doAlloc1. Initializer fuel, the
cost-map dimension, all successful native transitions and the returned stack
are derived from the original state relation and good-state/move bounds.
This is cross-implementation infrastructure, not a duplicate HOL do_alloc1
port; move selection, initial graph production and colouring remain separate. -/
theorem doAlloc1_production (moves : List (Nat × (Nat × Nat)))
    (entries : Option (NatInfoMap Nat)) (limit : Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ move ∈ moves, move.2.1 < native.dim ∧ move.2.2 < native.dim) :
    ∃ result : State,
      let initialized := cakeInitAlloc1Heu moves limit production
      let final := cakeRptDoStep (entries.map (cakeSpillCostMap production.dim))
        limit initialized.1 initialized.2
      doAlloc1 moves (entries.map sptFromAList) limit native = (.success final.stack, result) ∧
      goodRaState result ∧ native.dim = result.dim ∧ ProductionStateRel result final := by
  obtain ⟨initialState, initialRun, initialGood, initialDim, initialRel⟩ :=
    initAlloc1Heu_production moves limit related good bounds
  obtain ⟨result, loopRun, resultGood, resultDim, resultRel⟩ :=
    rptDoStep_production entries limit (cakeInitAlloc1Heu moves limit production).1
      initialRel initialGood
  have costDim : (cakeInitAlloc1Heu moves limit production).2.dim = production.dim :=
    initialRel.dimension.trans (initialDim.symm.trans related.dimension.symm)
  rw [costDim] at resultRel
  refine ⟨result, ?_, resultGood, initialDim.trans resultDim, resultRel⟩
  simp only [doAlloc1, Translator.Monadic.MonadBase.bind, getDim, initialRun,
    ignoreBind, loopRun, getStack, ret]
  rw [resultRel.stack]

end Flapjack.RegAlloc
