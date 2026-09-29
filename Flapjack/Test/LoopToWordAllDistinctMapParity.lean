import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelAllDistinct

/-!
# Original-domain parity for `loop_to_wordProof$locals_rel_ALL_DISTINCT_MAP`

The positive rows instantiate the exact theorem on a concrete two-entry context
whose registers `4` and `6` are distinct and nonzero even, so the mapped
register list is distinct.  The negative rows show that each source hypothesis
is necessary: dropping `set xs SUBSET domain ctxt` maps two out-of-domain names
to the default register `0`, and dropping `ALL_DISTINCT xs` repeats a register.
-/

namespace Flapjack.Test.LoopToWordAllDistinctMapParity

open Flapjack Flapjack.LoopToWord

private def ctx2 : Spt Nat := sptInsert 1 6 (sptInsert 0 4 (.ln : Spt Nat))
private def src2 : Spt (WordLocW 64) :=
  sptInsert 1 (.word 8) (sptInsert 0 (.word 7) (.ln : Spt (WordLocW 64)))
private def tgt2 : Spt (WordLocW 64) :=
  sptInsert 6 (.word 8) (sptInsert 4 (.word 7) (.ln : Spt (WordLocW 64)))

/-- The context with non-injective register assignment `0 ↦ 4`, `1 ↦ 4`. -/
private def ctxDup : Spt Nat := sptInsert 1 4 (sptInsert 0 4 (.ln : Spt Nat))

private theorem ctx2_mem (left : Nat) :
    sptMem left ctx2 ↔ left = 0 ∨ left = 1 := by
  rw [sptMem_iff_lookup]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h
    by_cases h1 : left = 1
    · exact Or.inr h1
    · by_cases h0 : left = 0
      · exact Or.inl h0
      · exfalso
        rw [ctx2, sptLookup_sptInsert_ne 1 left 6 (sptInsert 0 4 .ln) h1,
          sptLookup_sptInsert_ne 0 left 4 .ln h0, sptLookup] at hv
        simp at hv
  · intro h
    rcases h with rfl | rfl
    · exact ⟨4, by rw [ctx2, sptLookup_sptInsert_ne 1 0 6 (sptInsert 0 4 .ln) (by decide), sptLookup_sptInsert_same]⟩
    · exact ⟨6, by rw [ctx2, sptLookup_sptInsert_same]⟩

private theorem ctx2_even (name register : Nat)
    (hlookup : sptLookup name ctx2 = some register) :
    register ≠ 0 ∧ register % 2 = 0 := by
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

private theorem ctx2_sim (name : Nat) (value : WordLocW 64)
    (hsource : sptLookup name src2 = some value) :
    ∃ register, sptLookup name ctx2 = some register ∧
      sptLookup register tgt2 = some value := by
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

private theorem ctx2_localsRel : localsRelHOL (width := 64) ctx2 src2 tgt2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right hl hr heq
    have hl' := (ctx2_mem left).mp hl
    have hr' := (ctx2_mem right).mp hr
    rcases hl' with rfl | rfl <;> rcases hr' with rfl | rfl
    · rfl
    · simp [findVarHOL, ctx2, sptLookup, sptInsert] at heq
    · simp [findVarHOL, ctx2, sptLookup, sptInsert] at heq
    · rfl
  · intro name register hlookup
    exact ctx2_even name register hlookup
  · intro name value hsource
    exact ctx2_sim name value hsource

/-- Positive: the concrete context satisfies the relation, so the theorem
applies to the distinct list `[0, 1]` inside its domain. -/
example : (([0, 1] : List Nat).map (findVarHOL ctx2)).Nodup :=
  localsRelHOLAllDistinctMap ctx2 src2 tgt2 [0, 1]
    ⟨ctx2_localsRel,
      by intro name hname; rw [ctx2_mem]; simp at hname; omega,
      by decide⟩

/-- Positive: a single-entry list is trivially distinct. -/
example : (([1] : List Nat).map (findVarHOL ctx2)).Nodup :=
  localsRelHOLAllDistinctMap ctx2 src2 tgt2 [1]
    ⟨ctx2_localsRel,
      by intro name hname; rw [ctx2_mem]; simp at hname; omega,
      by decide⟩

/-- Negative: two names outside the context domain both map to the default
register `0`, so the subset hypothesis is necessary. -/
example : ¬ (([5, 6] : List Nat).map (findVarHOL ctx2)).Nodup := by
  have h : ([5, 6] : List Nat).map (findVarHOL ctx2) = [0, 0] := by
    simp [findVarHOL, ctx2, sptLookup, sptInsert]
  rw [h]
  decide

/-- Negative: a repeated source name repeats its mapped register, so the
distinctness hypothesis is necessary. -/
example : ¬ (([0, 0] : List Nat).map (findVarHOL ctx2)).Nodup := by
  have h : ([0, 0] : List Nat).map (findVarHOL ctx2) = [4, 4] := by
    simp [findVarHOL, ctx2, sptLookup, sptInsert]
  rw [h]
  decide

/-- Negative: a non-injective context maps distinct names to one register, so
the relation hypothesis is necessary. -/
example : ¬ (([0, 1] : List Nat).map (findVarHOL ctxDup)).Nodup := by
  have h : ([0, 1] : List Nat).map (findVarHOL ctxDup) = [4, 4] := by
    simp [findVarHOL, ctxDup, sptLookup, sptInsert]
  rw [h]
  decide

def allDistinctMapProbeChecks : List Bool :=
  [ ([0, 1] : List Nat).map (findVarHOL ctx2) == [4, 6],
    ([1, 0] : List Nat).map (findVarHOL ctx2) == [6, 4],
    ([5, 6] : List Nat).map (findVarHOL ctx2) == [0, 0],
    ([0, 1] : List Nat).map (findVarHOL ctxDup) == [4, 4] ]

#guard allDistinctMapProbeChecks.all id

def runChecks : IO Bool := do
  let passed := allDistinctMapProbeChecks.all id
  if passed then
    IO.println "PASS Loop-to-Word locals_rel_ALL_DISTINCT_MAP exact parity rows"
  else
    IO.println "FAIL Loop-to-Word locals_rel_ALL_DISTINCT_MAP exact parity rows"
  pure passed

end Flapjack.Test.LoopToWordAllDistinctMapParity
