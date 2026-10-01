import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFakeMovesCorrectRight
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveLookups
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsSwap

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack infrastructure extracting the two output map facts needed by
HOL right reconciliation. This is a derived composition of merge/fake frame
ports, not a separately claimed HOL declaration. -/
theorem reconciliationMapsAgree {width : Nat} [NeZero width]
    (prio : Option (Unit ⊕ Unit)) (left right : Spt Nat) (next : Nat) :
    let names := (sptToAList (sptUnion left right)).map Prod.fst
    let merged := mergeMoves names left right next
    let fakes := fakeMoves (width := width) prio names merged.2.2.2.1 merged.2.2.2.2 merged.2.2.1
    sptDomain fakes.2.2.2.1 = sptDomain fakes.2.2.2.2 ∧
      ∀ key, sptLookup key fakes.2.2.2.1 = sptLookup key fakes.2.2.2.2 := by
  dsimp only
  let names := (sptToAList (sptUnion left right)).map Prod.fst
  have membership (key : Nat) : key ∈ names ↔ sptDomain left key ∨ sptDomain right key := by
    simpa only [sptDomain_sptUnion] using sptMemMapFstToAList (sptUnion left right) key
  have mergeFrame := mergeMovesFrame2 names next left right
  generalize hm : mergeMoves names left right next = merged at mergeFrame ⊢
  rcases merged with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
  dsimp only at mergeFrame ⊢
  have fakeFrame := fakeMovesFrame2 (width := width) prio names counter leftTree rightTree
  have fakeLookup := fakeMovesFrame3 (width := width) prio names counter leftTree rightTree
  generalize hf : fakeMoves (width := width) prio names leftTree rightTree counter = fakes at fakeFrame fakeLookup ⊢
  rcases fakes with ⟨leftProg, rightProg, nextOut, leftOut, rightOut⟩
  dsimp only at fakeFrame fakeLookup ⊢
  have leftDomain : ∀ key, sptDomain leftOut key ↔ sptDomain left key ∨ sptDomain right key := by
    intro key
    rw [fakeFrame.1, mergeFrame.1, mergeFrame.2.1]
    simp only [membership key]
    tauto
  have rightDomain : ∀ key, sptDomain rightOut key ↔ sptDomain left key ∨ sptDomain right key := by
    intro key
    rw [fakeFrame.2.1, mergeFrame.1, mergeFrame.2.1]
    simp only [membership key]
    tauto
  refine ⟨?_, ?_⟩
  · funext key
    exact propext ((leftDomain key).trans (rightDomain key).symm)
  · intro key
    by_cases member : key ∈ names
    · by_cases common : sptDomain (sptInter left right) key
      · have commonMerged : sptDomain (sptInter leftTree rightTree) key := by
          simpa only [sptDomain_sptInter, mergeFrame.1, mergeFrame.2.1] using common
        obtain ⟨preserveL, preserveR⟩ := fakeLookup key (Or.inr commonMerged)
        rw [preserveL, preserveR]
        exact mergeFrame.2.2 key ⟨member, common⟩
      · have outsideMerged : ¬ sptDomain (sptInter leftTree rightTree) key := by
          simpa only [sptDomain_sptInter, mergeFrame.1, mergeFrame.2.1] using common
        exact fakeFrame.2.2 key ⟨member, outsideMerged⟩
    · have absent : ¬ (sptDomain left key ∨ sptDomain right key) := by
        intro present
        exact member ((membership key).mpr present)
      have noLeft : ¬ sptDomain leftOut key := fun h => absent ((leftDomain key).mp h)
      have noRight : ¬ sptDomain rightOut key := fun h => absent ((rightDomain key).mp h)
      have lnone : sptLookup key leftOut = none := by
        cases found : sptLookup key leftOut with
        | none => rfl
        | some value => exact False.elim (noLeft (by simp [sptDomain, found]))
      have rnone : sptLookup key rightOut = none := by
        cases found : sptLookup key rightOut with
        | none => rfl
        | some value => exact False.elim (noRight (by simp [sptDomain, found]))
      rw [lnone, rnone]

namespace FixInconsistenciesRightWitnesses

/-- Canonical full-state finite-map translation roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end FixInconsistenciesRightWitnesses

/-- Full original right branch reconciliation: the actual returned right program
establishes locals correspondence at the returned LEFT SSA map. Its agreement
with the right map is proved from union/toAList and native merge/fake frames.
Fresh literal HOL replay confirms shared source/target word/code/FFI types.
Universal states commute across the state-independent allocation/map premises.
The full evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8); only
Move and zero Const instructions execute in this returned program. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fix_inconsistencies_correctR"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem fixInconsistenciesCorrectR {width : Nat} [NeZero width] {C F : Type}
    (next : Nat) (left right : Spt Nat) (prio : Option (Unit ⊕ Unit))
    (source target : WordSemStateFiniteExact width C F)
    (h : isAllocVar next ∧ ssaMapOK next right) :
    let (_, moveR, nextOut, ssaOut) := fixInconsistencies (width := width) prio left right next
    ssaLocalsRel next right source.locals target.locals →
    let (result, after) := WordSemStateFiniteExact.evaluate moveR target
    result = none ∧ ssaLocalsRel nextOut ssaOut source.locals after.locals ∧
      Flapjack.WordAlloc.wordStateEqRel target after := by
  let names := (sptToAList (sptUnion left right)).map Prod.fst
  have maps := reconciliationMapsAgree (width := width) prio left right next
  dsimp only at maps
  have distinct : names.Nodup := sptAllDistinctMapFstToAList _
  simp only [fixInconsistencies]
  change (let (leftMoves, rightMoves, counter, leftTree, rightTree) := mergeMoves names left right next
          let (_, rightProg, nextOut, ssaOut, rightOut) := fakeMoves (width := width) prio names leftTree rightTree counter
          ssaLocalsRel next right source.locals target.locals →
          let (result, after) := WordSemStateFiniteExact.evaluate
            (.seq (.move (priority prio false) rightMoves) rightProg) target
          result = none ∧ ssaLocalsRel nextOut ssaOut source.locals after.locals ∧
            Flapjack.WordAlloc.wordStateEqRel target after)
  have frame := mergeMovesFrame names next left right h.1
  generalize hm : mergeMoves names left right next = merged at frame ⊢
  rcases merged with ⟨leftMoves, rightMoves, counter, leftTree, rightTree⟩
  dsimp only at frame ⊢
  intro related
  have mergedResult := mergeMovesCorrectR names next left right source target
    (priority prio false) h.1 distinct h.2 related
  rw [hm] at mergedResult
  dsimp only at mergedResult
  generalize he : WordSemStateFiniteExact.evaluate (.move (priority prio false) rightMoves) target = evaluated at mergedResult
  rcases evaluated with ⟨result, middle⟩
  dsimp only at mergedResult
  rcases mergedResult with ⟨noneResult, _, _, middleRelated, middleFrame⟩
  subst result
  have fakeResult := fakeMovesCorrectR prio names counter leftTree rightTree source middle
    frame.1 distinct (frame.2.2.2 h.2) middleRelated
  generalize hf : fakeMoves (width := width) prio names leftTree rightTree counter = fakes at fakeResult ⊢
  rcases fakes with ⟨leftProg, rightProg, nextOut, ssaOut, rightOut⟩
  dsimp only at fakeResult ⊢
  generalize he₂ : WordSemStateFiniteExact.evaluate rightProg middle = evaluated₂ at fakeResult
  rcases evaluated₂ with ⟨result₂, after⟩
  dsimp only at fakeResult
  rcases fakeResult with ⟨noneResult₂, _, _, afterRelated, afterFrame⟩
  subst result₂
  rw [hm, hf] at maps
  dsimp only at maps
  have outputRelated := ssaEqRelSwap nextOut ssaOut rightOut source after
    ⟨afterRelated, maps.1, maps.2⟩
  have fixed := fakeMovesFixClock target middle middleFrame
  simp only [WordSemStateFiniteExact.evaluate, he, fixed, he₂]
  exact ⟨True.intro, outputRelated, fakeMovesStateRelationTrans target middle after middleFrame afterFrame⟩

end Flapjack.Compiler.Backend.WordAlloc
