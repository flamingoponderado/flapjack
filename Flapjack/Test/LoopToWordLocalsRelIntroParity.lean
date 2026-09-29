import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelIntro

/-!
# Original-domain parity for `loop_to_wordProof$locals_rel_intro`

Replays the introduction of the three `locals_rel` clauses on a concrete
two-entry context with nonzero even registers `4` and `6`, plus the failure of
the nonzero/even clause for an odd-register context.
-/

namespace Flapjack.Test.LoopToWordLocalsRelIntroParity

open Flapjack Flapjack.LoopToWord

private def ctx2 : Spt Nat := sptInsert 1 6 (sptInsert 0 4 (.ln : Spt Nat))
private def src2 : Spt (WordLocW 64) :=
  sptInsert 1 (.word 8) (sptInsert 0 (.word 7) (.ln : Spt (WordLocW 64)))
private def tgt2 : Spt (WordLocW 64) :=
  sptInsert 6 (.word 8) (sptInsert 4 (.word 7) (.ln : Spt (WordLocW 64)))

private def ctxOdd : Spt Nat := sptInsert 0 3 (.ln : Spt Nat)

private theorem ctx2_localsRel : localsRelHOL (width := 64) ctx2 src2 tgt2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right hl hr heq
    have memOf : ∀ x, sptMem x ctx2 → x = 0 ∨ x = 1 := by
      intro x hm
      rw [sptMem_iff_lookup] at hm
      obtain ⟨vv, hv⟩ := hm
      by_cases h1 : x = 1
      · exact Or.inr h1
      · by_cases h0 : x = 0
        · exact Or.inl h0
        · exfalso
          rw [ctx2, sptLookup_sptInsert_ne 1 x 6 (sptInsert 0 4 .ln) h1,
            sptLookup_sptInsert_ne 0 x 4 .ln h0, sptLookup] at hv
          simp at hv
    rcases memOf left hl with rfl | rfl <;> rcases memOf right hr with rfl | rfl
    · rfl
    · simp [findVarHOL, ctx2, sptLookup, sptInsert] at heq
    · simp [findVarHOL, ctx2, sptLookup, sptInsert] at heq
    · rfl
  · intro name register hlookup
    by_cases h1 : name = 1
    · subst name
      rw [ctx2, sptLookup_sptInsert_same] at hlookup
      injection hlookup with hreg
      subst hreg
      decide
    · rw [ctx2, sptLookup_sptInsert_ne 1 name 6 (sptInsert 0 4 .ln) h1] at hlookup
      by_cases h0 : name = 0
      · subst name
        rw [sptLookup_sptInsert_same] at hlookup
        injection hlookup with hreg
        subst hreg
        decide
      · rw [sptLookup_sptInsert_ne 0 name 4 .ln h0, sptLookup] at hlookup
        simp at hlookup
  · intro name value hsource
    by_cases h1 : name = 1
    · subst name
      rw [src2, sptLookup_sptInsert_same] at hsource
      injection hsource with hvalue
      subst hvalue
      exact ⟨6, by rw [ctx2, sptLookup_sptInsert_same],
        by rw [tgt2, sptLookup_sptInsert_same]⟩
    · rw [src2, sptLookup_sptInsert_ne 1 name (WordLocW.word (8 : BitVec 64))
        (sptInsert 0 (WordLocW.word (7 : BitVec 64)) .ln) h1] at hsource
      by_cases h0 : name = 0
      · subst name
        rw [sptLookup_sptInsert_same] at hsource
        injection hsource with hvalue
        subst hvalue
        exact ⟨4,
          by rw [ctx2, sptLookup_sptInsert_ne 1 0 6 (sptInsert 0 4 .ln) (by decide),
            sptLookup_sptInsert_same],
          by rw [tgt2, sptLookup_sptInsert_ne 6 4 (WordLocW.word (8 : BitVec 64))
            (sptInsert 4 (WordLocW.word (7 : BitVec 64)) .ln) (by decide),
            sptLookup_sptInsert_same]⟩
      · rw [sptLookup_sptInsert_ne 0 name (WordLocW.word (7 : BitVec 64)) .ln h0,
          sptLookup] at hsource
        simp at hsource

/-- Positive: the three clauses are recovered from the concrete relation. -/
example : (localsRelHOLIntro (width := 64) ctx2 src2 tgt2 ctx2_localsRel).2.1 0 4
    (by rw [ctx2, sptLookup_sptInsert_ne 1 0 6 (sptInsert 0 4 .ln) (by decide),
      sptLookup_sptInsert_same]) = (⟨by decide, by decide⟩ : 4 ≠ 0 ∧ 4 % 2 = 0) := rfl

/-- Positive: the simulation clause maps register `0` to `4`. -/
example : ∃ register, sptLookup 0 ctx2 = some register ∧
    sptLookup register tgt2 = some (WordLocW.word (7 : BitVec 64)) :=
  (localsRelHOLIntro (width := 64) ctx2 src2 tgt2 ctx2_localsRel).2.2 0
    (WordLocW.word (7 : BitVec 64))
    (by rw [src2, sptLookup_sptInsert_ne 1 0 (WordLocW.word (8 : BitVec 64))
        (sptInsert 0 (WordLocW.word (7 : BitVec 64)) .ln) (by decide),
      sptLookup_sptInsert_same])

/-- Negative: an odd-register context fails the nonzero/even clause. -/
example : ¬ (∀ name register, sptLookup name ctxOdd = some register →
    register ≠ 0 ∧ register % 2 = 0) := by
  intro h
  have h3 := h 0 3 (by rw [ctxOdd, sptLookup_sptInsert_same])
  exact absurd h3.2 (by decide)

def localsRelIntroProbeChecks : List Bool :=
  [ sptLookup 0 ctx2 == some 4 && sptLookup 1 ctx2 == some 6,
    sptLookup 4 tgt2 == some (WordLocW.word (7 : BitVec 64)) &&
      sptLookup 6 tgt2 == some (WordLocW.word (8 : BitVec 64)) ]

#guard localsRelIntroProbeChecks.all id

def runChecks : IO Bool := do
  let passed := localsRelIntroProbeChecks.all id
  if passed then
    IO.println "PASS Loop-to-Word locals_rel_intro exact parity rows"
  else
    IO.println "FAIL Loop-to-Word locals_rel_intro exact parity rows"
  pure passed

end Flapjack.Test.LoopToWordLocalsRelIntroParity
