import Flapjack.RiscV.Allocator

namespace Flapjack.Compiler.Backend.WordAlloc

/-- First-match production list lookup equals the canonical map codec, on
arbitrary lists including duplicates. Flapjack-only representation law. -/
theorem productionMergeMapLookup (entries : List (Nat × Nat)) (key : Nat) :
    lookupNatInfo key entries = sptAListLookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨name,value⟩
    by_cases h : name = key
    · subst name; simp [lookupNatInfo,sptAListLookup]
    · have hk : key ≠ name := Ne.symm h
      simp [lookupNatInfo,sptAListLookup,h,hk,ih]

private theorem decodedLookup (tree : Spt Nat) (key : Nat) :
    lookupNatInfo key (sptToAList tree) = sptLookup key tree := by
  rw [productionMergeMapLookup]
  simpa only [sptLookup_sptFromAList] using sptLookup_sptFromAList_sptToAList key tree

/-- Actual allocator caller preserves every native output observation and both
independent state counters. No map distinctness, finite-width counter bound,
or presumed output relation occurs in the premises. This transports the native
operation through production state codecs, not a new tagged HOL theorem. -/
theorem wordSsaMergeMovesCorresponds (names : List Nat) (left right : WordSsaState) (next : Nat) :
    let native := mergeMoves names (sptFromAList left.current) (sptFromAList right.current) next
    let executed := wordSsaMergeMoves names left right next
    executed.1 = native.1 ∧ executed.2.1 = native.2.1 ∧
    executed.2.2.1 = native.2.2.1 ∧
    executed.2.2.2.1.next = left.next ∧ executed.2.2.2.2.next = right.next ∧
    (∀ key, lookupNatInfo key executed.2.2.2.1.current = sptLookup key native.2.2.2.1) ∧
    (∀ key, lookupNatInfo key executed.2.2.2.2.current = sptLookup key native.2.2.2.2) := by
  unfold wordSsaMergeMoves mergeMovesExecutable
  obtain ⟨lm,rm,n,l,r⟩ := mergeMoves names (sptFromAList left.current) (sptFromAList right.current) next
  simp only
  exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,decodedLookup l,decodedLookup r⟩
end Flapjack.Compiler.Backend.WordAlloc
