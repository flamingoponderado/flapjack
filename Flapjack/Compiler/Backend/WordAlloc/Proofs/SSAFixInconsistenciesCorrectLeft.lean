import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFakeMovesCorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.CorrectLeft

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack infrastructure for composing the fieldwise whole-state frame.
No independent HOL theorem is being ported by this local transitivity helper. -/
theorem fakeMovesStateRelationTrans {width : Nat} [NeZero width] {C F : Type}
    (first middle last : WordSemStateFiniteExact width C F)
    (h₁ : Flapjack.WordAlloc.wordStateEqRel first middle)
    (h₂ : Flapjack.WordAlloc.wordStateEqRel middle last) :
    Flapjack.WordAlloc.wordStateEqRel first last := by
  simp_all [Flapjack.WordAlloc.wordStateEqRel]

namespace FixInconsistenciesLeftWitnesses

/-- Canonical full-state finite-map translation roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end FixInconsistenciesLeftWitnesses

/-- Full original left branch reconciliation theorem. Fresh literal HOL replay
confirms source/target share all word/code/FFI dimensions here. All original
allocation/map premises, quantified states and locals relation implication are
retained, with the actual returned program evaluated to NONE and both final
relations proved. The evaluator inherits reals_as_rational_cuts, SOUNDNESS
item 8; the returned code only executes Move and zero Const instructions. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fix_inconsistencies_correctL"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem fixInconsistenciesCorrectL {width : Nat} [NeZero width] {C F : Type}
    (next : Nat) (left right : Spt Nat) (prio : Option (Unit ⊕ Unit))
    (source target : WordSemStateFiniteExact width C F)
    (h : isAllocVar next ∧ ssaMapOK next left) :
    let (moveL, _, nextOut, ssaOut) := fixInconsistencies (width := width) prio left right next
    ssaLocalsRel next left source.locals target.locals →
    let (result, after) := WordSemStateFiniteExact.evaluate moveL target
    result = none ∧ ssaLocalsRel nextOut ssaOut source.locals after.locals ∧
      Flapjack.WordAlloc.wordStateEqRel target after := by
  let names := (sptToAList (sptUnion left right)).map Prod.fst
  have distinct : names.Nodup := sptAllDistinctMapFstToAList _
  simp only [fixInconsistencies]
  change (let (leftMoves, rightMoves, counter, leftTree, rightTree) := mergeMoves names left right next
          let (leftProg, _, nextOut, ssaOut, _) := fakeMoves (width := width) prio names leftTree rightTree counter
          ssaLocalsRel next left source.locals target.locals →
          let (result, after) := WordSemStateFiniteExact.evaluate
            (.seq (.move (priority prio true) leftMoves) leftProg) target
          result = none ∧ ssaLocalsRel nextOut ssaOut source.locals after.locals ∧
            Flapjack.WordAlloc.wordStateEqRel target after)
  have frame := mergeMovesFrame names next left right h.1
  generalize hm : mergeMoves names left right next = merged at frame ⊢
  rcases merged with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
  dsimp only at frame ⊢
  intro related
  have mergedResult := mergeMovesCorrectL names next left right source target
    (priority prio true) h.1 distinct h.2 related
  rw [hm] at mergedResult
  dsimp only at mergedResult
  generalize he : WordSemStateFiniteExact.evaluate (.move (priority prio true) leftMoves) target = evaluated at mergedResult
  rcases evaluated with ⟨result, middle⟩
  dsimp only at mergedResult
  rcases mergedResult with ⟨noneResult, _, _, middleRelated, middleFrame⟩
  subst result
  have fakeResult := fakeMovesCorrectL prio names counter leftTree rightTree source middle
    frame.1 distinct (frame.2.2.1 h.2) middleRelated
  generalize hf : fakeMoves (width := width) prio names leftTree rightTree counter = fakes at fakeResult ⊢
  rcases fakes with ⟨leftProg, rightProg, nextOut, ssaOut, rightOut⟩
  dsimp only at fakeResult ⊢
  generalize he₂ : WordSemStateFiniteExact.evaluate leftProg middle = evaluated₂ at fakeResult
  rcases evaluated₂ with ⟨result₂, after⟩
  dsimp only at fakeResult
  rcases fakeResult with ⟨noneResult₂, _, _, afterRelated, afterFrame⟩
  subst result₂
  have fixed := fakeMovesFixClock target middle middleFrame
  simp only [WordSemStateFiniteExact.evaluate, he, fixed, he₂]
  exact ⟨True.intro, afterRelated, fakeMovesStateRelationTrans target middle after middleFrame afterFrame⟩

end Flapjack.Compiler.Backend.WordAlloc
