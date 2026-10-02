import Flapjack.Compiler.Backend.WordAlloc.ProductionMergeMoves

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Decoder lookup for arbitrary native trees. Flapjack API correspondence,
not an independent HOL declaration. -/
theorem productionSsaDecodedLookup (tree : Spt Nat) (key : Nat) :
    lookupNatInfo key (sptToAList tree) = sptLookup key tree := by
  rw [productionMergeMapLookup]
  simpa only [sptLookup_sptFromAList] using sptLookup_sptFromAList_sptToAList key tree

/-- Actual allocator fresh-name caller preserves the complete native output
name, counter, ordered map decoder, and every lookup for unrestricted input
states, including duplicate keys. No independent HOL original. -/
theorem wordSsaFreshCorresponds (state : WordSsaState) (name : Nat) :
    let native := nextVarRename name (sptFromAList state.current) state.next
    let executed := wordSsaFresh state name
    executed.2 = native.1 ∧ executed.1.next = native.2.2 ∧
    executed.1.current = sptToAList native.2.1 ∧
    ∀ key, lookupNatInfo key executed.1.current = sptLookup key native.2.1 := by
  simp only [wordSsaFresh,ssaNextVarRenameExecutable,nextVarRename]
  exact ⟨True.intro,True.intro,True.intro,productionSsaDecodedLookup _⟩

/-- Actual forced-renaming caller retains the original independent counter and
returns precisely the native map traversal and lookup observations. -/
theorem wordSsaForceRenameCorresponds (renamings : List (Nat × Nat)) (state : WordSsaState) :
    (wordSsaForceRename renamings state).next = state.next ∧
    (wordSsaForceRename renamings state).current =
      sptToAList (forceRename renamings (sptFromAList state.current)) ∧
    ∀ key, lookupNatInfo key (wordSsaForceRename renamings state).current =
      sptLookup key (forceRename renamings (sptFromAList state.current)) := by
  exact ⟨rfl,rfl,productionSsaDecodedLookup _⟩

/-- The production observer exposes native traversal order exactly, with no
canonical-input or distinct-key premise. -/
theorem wordSsaKeysCorresponds (state : WordSsaState) :
    wordSsaKeys state = (sptToAList (sptFromAList state.current)).map Prod.fst := rfl

/-- The actual allocator cutset caller retains its independent counter,
returns the full ordered native intersection decoder, and has precisely the
cutset-restricted first-match lookup. Flapjack production boundary proof. -/
theorem wordSsaRestrictCorresponds (state : WordSsaState) (names : List Nat) :
    (wordSsaRestrict state names).next = state.next ∧
    (wordSsaRestrict state names).current =
      sptToAList (sptInter (sptFromAList state.current)
        (sptFromAList (names.map (fun name => (name, ()))))) ∧
    ∀ key, lookupNatInfo key (wordSsaRestrict state names).current =
      if key ∈ names then lookupNatInfo key state.current else none := by
  refine ⟨rfl, rfl, ?_⟩
  intro key
  simp only [wordSsaRestrict, productionMergeMapLookup]
  exact ssaRestrictExecutableLookup state.current names key

end Flapjack.Compiler.Backend.WordAlloc
