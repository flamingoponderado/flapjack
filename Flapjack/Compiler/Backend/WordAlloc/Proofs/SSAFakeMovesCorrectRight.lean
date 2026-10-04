import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFakeMovesCorrectLeft

namespace Flapjack.Compiler.Backend.WordAlloc

namespace FakeMovesRightWitnesses

/-- Canonical full-state finite-map translation roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end FakeMovesRightWitnesses

/-- Full original right fake-move simulation with all original premises and
five actual native evaluator conclusions. Fresh HOL replay confirms independent
source/target code/FFI dimensions and shared word width. The full evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8); only Move and zero Const
paths execute here. Seq restores the unchanged clock/termdep from the relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem fakeMovesCorrectR {width : Nat} [NeZero width] {C₁ F₁ C₂ F₂ : Type}
    (prio : Option (Unit ⊕ Unit)) (names : List Nat) (next : Nat)
    (left right : Spt Nat) (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂)
    (allocated : isAllocVar next) (distinct : names.Nodup) (valid : ssaMapOK next right) :
    let moves := fakeMoves (width := width) prio names left right next
    ssaLocalsRel next right source.locals target.locals →
    let evaluated := WordSemStateFiniteExact.evaluate moves.2.1 target
    evaluated.1 = none ∧
    (∀ key, key ∉ names → sptLookup key moves.2.2.2.2 = sptLookup key right) ∧
    (∀ key value, key < next → sptLookup key target.locals = some value →
      sptLookup key evaluated.2.locals = some value) ∧
    ssaLocalsRel moves.2.2.1 moves.2.2.2.2 source.locals evaluated.2.locals ∧
    Flapjack.WordAlloc.wordStateEqRel target evaluated.2 := by
  induction names with
  | nil =>
    dsimp only [fakeMoves]
    intro related
    simp only [WordSemStateFiniteExact.evaluate]
    exact ⟨True.intro, fun _ _ => True.intro, fun _ _ _ found => found, related,
      by simp [Flapjack.WordAlloc.wordStateEqRel]⟩
  | cons name names ih =>
    have absent := (List.nodup_cons.mp distinct).1
    have tail := ih distinct.tail
    dsimp only at tail ⊢
    intro related
    have tailResult := tail related
    have frame := fakeMovesFrame (width := width) prio names next left right allocated
    generalize hm : fakeMoves (width := width) prio names left right next = moves at tailResult frame
    rcases moves with ⟨moveL, moveR, counter, leftTree, rightTree⟩
    simp only at tailResult frame
    generalize he : WordSemStateFiniteExact.evaluate moveR target = evaluated at tailResult
    rcases evaluated with ⟨result, after⟩
    simp only at tailResult
    rcases tailResult with ⟨resultNone, unchanged, preserved, localsRelated, stateRelated⟩
    subst result
    have fixed := fakeMovesFixClock target after stateRelated
    have finish := fakeMoveFinish source target after names name next counter right rightTree
      (unchanged := unchanged) (preserved := preserved) (related := localsRelated)
      (stateRelated := stateRelated) (valid := frame.2.2.2 valid) (bound := frame.2.1)
    simp only [fakeMoves, hm]
    cases hl : sptLookup name rightTree with
    | none =>
      cases hr : sptLookup name leftTree with
      | none =>
        simp only [he]
        exact ⟨True.intro, fun key outside => unchanged key
          (fun member => outside (List.mem_cons_of_mem name member)),
          preserved, localsRelated, stateRelated⟩
      | some register =>
        have summary := finish (.word 0) (by intro register found; rw [hl] at found; cases found)
        simpa [WordSemStateFiniteExact.evaluate, he, fixed, fakeMove,
          WordSemStateFiniteExact.inst, WordSemStateFiniteExact.assign,
          WordSemStateFiniteExact.wordExp] using And.intro True.intro summary
    | some register =>
      cases hr : sptLookup name leftTree with
      | some other =>
        simp only [he]
        exact ⟨True.intro, fun key outside => unchanged key
          (fun member => outside (List.mem_cons_of_mem name member)),
          preserved, localsRelated, stateRelated⟩
      | none =>
        obtain ⟨value, found⟩ := (sptMem_iff_lookup register after.locals).mp
          (localsRelated.1 name register hl)
        have summary := finish value (by intro r mapped; rw [hl] at mapped; cases mapped; exact found)
        simpa [WordSemStateFiniteExact.evaluate, he, fixed,
          WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, found,
          WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar,
          LoopSemStateFiniteExact.sptAlistInsert] using And.intro True.intro summary

end Flapjack.Compiler.Backend.WordAlloc
