import Flapjack.Pancake.Proofs.LoopToWord.FindVar

/-!
# Original-domain parity for `loop_to_wordProof$find_var_neq_0` /
# `find_var_neq_odd`

Positive rows apply the exact theorems on a concrete context whose registers
`4` and `6` are nonzero even.  Negative rows show that the source hypotheses
are needed: an odd register violates the even-only premise, and the even
register `4` is excluded only by the oddness premise on `k`.
-/

namespace Flapjack.Test.LoopToWordFindVarParity

open Flapjack Flapjack.LoopToWord

private def ctx2 : Spt Nat := sptInsert 1 6 (sptInsert 0 4 (.ln : Spt Nat))
private def src2 : Spt (WordLocW 64) :=
  sptInsert 1 (.word 8) (sptInsert 0 (.word 7) (.ln : Spt (WordLocW 64)))
private def tgt2 : Spt (WordLocW 64) :=
  sptInsert 6 (.word 8) (sptInsert 4 (.word 7) (.ln : Spt (WordLocW 64)))

/-- A context that maps `0` to the odd register `3`. -/
private def ctxOdd : Spt Nat := sptInsert 0 3 (.ln : Spt Nat)

private theorem ctx2_localsRel : localsRelHOL (width := 64) ctx2 src2 tgt2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right hl hr heq
    have hl' : sptMem left ctx2 ∨ True := Or.inr trivial
    have mem0 : sptMem left ctx2 → left = 0 ∨ left = 1 := by
      intro hm
      rw [sptMem_iff_lookup] at hm
      obtain ⟨vv, hv⟩ := hm
      by_cases h1 : left = 1
      · exact Or.inr h1
      · by_cases h0 : left = 0
        · exact Or.inl h0
        · exfalso
          rw [ctx2, sptLookup_sptInsert_ne 1 left 6 (sptInsert 0 4 .ln) h1,
            sptLookup_sptInsert_ne 0 left 4 .ln h0, sptLookup] at hv
          simp at hv
    have mem1 : sptMem right ctx2 → right = 0 ∨ right = 1 := by
      intro hm
      rw [sptMem_iff_lookup] at hm
      obtain ⟨vv, hv⟩ := hm
      by_cases h1 : right = 1
      · exact Or.inr h1
      · by_cases h0 : right = 0
        · exact Or.inl h0
        · exfalso
          rw [ctx2, sptLookup_sptInsert_ne 1 right 6 (sptInsert 0 4 .ln) h1,
            sptLookup_sptInsert_ne 0 right 4 .ln h0, sptLookup] at hv
          simp at hv
    rcases mem0 hl with rfl | rfl <;> rcases mem1 hr with rfl | rfl
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

private theorem ctx2_even : ∀ n m, sptLookup n ctx2 = some m → m ≠ 0 ∧ m % 2 = 0 := by
  intro name register hlookup
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

/-- Positive: an in-domain variable of the concrete `locals_rel` context maps
to a nonzero register. -/
example : findVarHOL ctx2 0 ≠ 0 :=
  findVarHOL_ne_zero ctx2 src2 tgt2 0 ⟨by rw [sptMem_iff_lookup]; exact ⟨4, by rw [ctx2, sptLookup_sptInsert_ne 1 0 6 (sptInsert 0 4 .ln) (by decide), sptLookup_sptInsert_same]⟩, ctx2_localsRel⟩

/-- Positive: the even-only context premise excludes every odd register. -/
example : findVarHOL ctx2 0 ≠ 3 :=
  findVarHOL_ne_odd ctx2 0 3 ⟨ctx2_even, by decide⟩

/-- Negative: the odd register `3` of `ctxOdd` is exactly what the even-only
premise rules out, so keying on an even-only context is necessary. -/
example : findVarHOL ctxOdd 0 = 3 := by
  simp [findVarHOL, ctxOdd, sptLookup]

/-- Negative: the even register `4` is a possible `find_var` result, so the
oddness premise on `k` is necessary (the theorem does not apply at `k = 4`). -/
example : findVarHOL ctx2 0 = 4 := by
  simp [findVarHOL, ctx2, sptLookup, sptInsert]

def findVarProbeChecks : List Bool :=
  [ findVarHOL ctx2 0 == 4,
    findVarHOL ctx2 1 == 6,
    findVarHOL ctxOdd 0 == 3,
    decide (findVarHOL ctx2 0 ≠ 3),
    decide (findVarHOL ctx2 1 ≠ 5) ]

#guard findVarProbeChecks.all id

def runChecks : IO Bool := do
  let passed := findVarProbeChecks.all id
  if passed then
    IO.println "PASS Loop-to-Word find_var_neq_0 and find_var_neq_odd exact parity rows"
  else
    IO.println "FAIL Loop-to-Word find_var_neq_0 and find_var_neq_odd exact parity rows"
  pure passed

end Flapjack.Test.LoopToWordFindVarParity
