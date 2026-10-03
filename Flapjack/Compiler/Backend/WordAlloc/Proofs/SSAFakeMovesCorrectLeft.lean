import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMoveFrames
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMovePreserve

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack infrastructure for the two native fake-move branches. A missing
map key cannot have a source value; a present key reads its existing selected
register. This local insertion lemma has no independent HOL original. -/
theorem fakeMoveLocalsInsert {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) (name : Nat) (value : α)
    (related : ssaLocalsRel next ssa source target) (valid : ssaMapOK next ssa)
    (chosen : ∀ register, sptLookup name ssa = some register →
      sptLookup register target = some value) :
    ssaLocalsRel (next + 4) (sptInsert name next ssa) source
      (sptInsert next value target) := by
  refine ⟨?_, ?_⟩
  · intro key register found
    by_cases same : key = name
    · subst key
      rw [sptLookup_sptInsert_same] at found
      cases found
      exact (sptMem_iff_lookup next _).mpr ⟨value, sptLookup_sptInsert_same ..⟩
    · rw [sptLookup_sptInsert_ne _ _ _ _ same] at found
      obtain ⟨oldValue, oldFound⟩ := (sptMem_iff_lookup register target).mp
        (related.1 key register found)
      refine (sptMem_iff_lookup register _).mpr ⟨oldValue, ?_⟩
      rw [sptLookup_sptInsert_ne _ _ _ _ (by have := (valid key register found).2; omega)]
      exact oldFound
  · intro key oldValue found
    obtain ⟨domain, matching, bound⟩ := related.2 key oldValue found
    obtain ⟨register, mapped⟩ := (sptMem_iff_lookup key ssa).mp domain
    by_cases same : key = name
    · subst key
      have read := chosen register mapped
      have equal : oldValue = value := by
        simpa only [mapped, Option.getD_some, read, Option.some.injEq] using matching.symm
      subst oldValue
      refine ⟨(sptMem_iff_lookup name _).mpr ⟨next, sptLookup_sptInsert_same ..⟩, ?_, ?_⟩
      · simp only [sptLookup_sptInsert_same, Option.getD_some]
      · intro allocated
        have := bound allocated
        omega
    · refine ⟨(sptMem_iff_lookup key _).mpr ⟨register, ?_⟩, ?_, ?_⟩
      · rw [sptLookup_sptInsert_ne _ _ _ _ same]
        exact mapped
      · rw [sptLookup_sptInsert_ne _ _ _ _ same, mapped]
        simp only [Option.getD_some]
        rw [sptLookup_sptInsert_ne _ _ _ _ (by have := (valid key register mapped).2; omega)]
        simpa only [mapped, Option.getD_some] using matching
      · intro allocated
        have := bound allocated
        omega


/-- Flapjack infrastructure: the source state relation supplies both fields
restored by Seq, so a successful native suffix uses the actual prior state. -/
theorem fakeMovesFixClock {width : Nat} [NeZero width] {C F : Type}
    (before after : WordSemStateFiniteExact width C F)
    (related : Flapjack.WordAlloc.wordStateEqRel before after) :
    WordSemStateFiniteExact.fixClock before ((none : Option (WordSemResult width)), after) =
      (none, after) := by
  have clock := Flapjack.WordAlloc.wsrClock related
  have termdep : after.termdep = before.termdep := by
    unfold Flapjack.WordAlloc.wordStateEqRel at related
    tauto
  simp [WordSemStateFiniteExact.fixClock, ← clock, ← termdep]


/-- Flapjack infrastructure for the inductive branch summary. It combines the
actual fresh local insertion with the tail proof facts; no HOL tag is claimed
for this factored intermediate statement. -/
theorem fakeMoveFinish {width : Nat} [NeZero width] {C₁ F₁ C₂ F₂ : Type}
    (source : WordSemStateFiniteExact width C₁ F₁)
    (before after : WordSemStateFiniteExact width C₂ F₂)
    (names : List Nat) (name next counter : Nat) (ssa ssaTail : Spt Nat)
    (value : WordLocW width)
    (unchanged : ∀ key, key ∉ names → sptLookup key ssaTail = sptLookup key ssa)
    (preserved : ∀ key oldValue, key < next → sptLookup key before.locals = some oldValue →
      sptLookup key after.locals = some oldValue)
    (related : ssaLocalsRel counter ssaTail source.locals after.locals)
    (stateRelated : Flapjack.WordAlloc.wordStateEqRel before after)
    (valid : ssaMapOK counter ssaTail) (bound : next ≤ counter)
    (chosen : ∀ register, sptLookup name ssaTail = some register →
      sptLookup register after.locals = some value) :
    (∀ key, key ∉ name :: names →
      sptLookup key (sptInsert name counter ssaTail) = sptLookup key ssa) ∧
    (∀ key oldValue, key < next → sptLookup key before.locals = some oldValue →
      sptLookup key (WordSemStateFiniteExact.setVar counter value after).locals = some oldValue) ∧
    ssaLocalsRel (counter + 4) (sptInsert name counter ssaTail) source.locals
      (WordSemStateFiniteExact.setVar counter value after).locals ∧
    Flapjack.WordAlloc.wordStateEqRel before (WordSemStateFiniteExact.setVar counter value after) := by
  refine ⟨?_, ?_, fakeMoveLocalsInsert counter ssaTail source.locals after.locals
    name value related valid chosen, ?_⟩
  · intro key outside
    have different : key ≠ name := by intro same; subst key; exact outside (by simp)
    rw [sptLookup_sptInsert_ne _ _ _ _ different]
    exact unchanged key (fun member => outside (List.mem_cons_of_mem name member))
  · intro key oldValue below found
    change sptLookup key (sptInsert counter value after.locals) = some oldValue
    rw [sptLookup_sptInsert_ne _ _ _ _ (by omega)]
    exact preserved key oldValue below found
  · simpa only [Flapjack.WordAlloc.wordStateEqRel, WordSemStateFiniteExact.setVar] using stateRelated


namespace FakeMovesLeftWitnesses

/-- Canonical full-state finite-map translation roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end FakeMovesLeftWitnesses

/-- Full original left fake-move simulation with all original premises and five
actual native evaluator conclusions. Fresh HOL replay confirms independent
source/target code and FFI dimensions with shared word width. Source-domain
selector observations are guarded by SOME; Seq restores the actual unchanged
clock and termdep. The full evaluator inherits reals_as_rational_cuts,
SOUNDNESS item 8; these paths execute only Move and zero Const instructions. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "fake_moves_correctL"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem fakeMovesCorrectL {width : Nat} [NeZero width] {C₁ F₁ C₂ F₂ : Type}
    (prio : Option (Unit ⊕ Unit)) (names : List Nat) (next : Nat)
    (left right : Spt Nat) (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂)
    (allocated : isAllocVar next) (distinct : names.Nodup) (valid : ssaMapOK next left) :
    let moves := fakeMoves (width := width) prio names left right next
    ssaLocalsRel next left source.locals target.locals →
    let evaluated := WordSemStateFiniteExact.evaluate moves.1 target
    evaluated.1 = none ∧
    (∀ key, key ∉ names → sptLookup key moves.2.2.2.1 = sptLookup key left) ∧
    (∀ key value, key < next → sptLookup key target.locals = some value →
      sptLookup key evaluated.2.locals = some value) ∧
    ssaLocalsRel moves.2.2.1 moves.2.2.2.1 source.locals evaluated.2.locals ∧
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
    generalize he : WordSemStateFiniteExact.evaluate moveL target = evaluated at tailResult
    rcases evaluated with ⟨result, after⟩
    simp only at tailResult
    rcases tailResult with ⟨resultNone, unchanged, preserved, localsRelated, stateRelated⟩
    subst result
    have fixed := fakeMovesFixClock target after stateRelated
    have finish := fakeMoveFinish source target after names name next counter left leftTree
      (unchanged := unchanged) (preserved := preserved) (related := localsRelated)
      (stateRelated := stateRelated) (valid := frame.2.2.1 valid) (bound := frame.2.1)
    simp only [fakeMoves, hm]
    cases hl : sptLookup name leftTree with
    | none =>
      cases hr : sptLookup name rightTree with
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
      cases hr : sptLookup name rightTree with
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
