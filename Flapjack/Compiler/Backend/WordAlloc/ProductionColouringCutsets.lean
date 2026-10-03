import Flapjack.Compiler.Backend.WordAlloc.ProductionCutsetContext
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

namespace Flapjack.WordAlloc

/-! Actual coloured cutsets cross a list boundary. The native key-renaming
definition rebuilds a canonical sparse tree, so decoding and re-encoding its
output retains collisions and mixed traversal exactly. These codec theorems
have no separate HOL original; the original key operations are already tagged. -/

theorem colouringListCodec (names : List Nat) :
    LoopToWord.toNumSetHOL names = numSetToExact names := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simpa only [LoopToWord.toNumSetHOL, numSetToExact, List.map_cons, sptFromAList] using
        congrArg (sptInsert name ()) ih

theorem colouringUnitRoundTrip (tree : Spt Unit) (wellFormed : sptWf tree = true) :
    numSetToExact (numSetFromExact tree) = tree := by
  apply (sptEqThm _ _ ⟨sptWfFromAList _, wellFormed⟩).mpr
  intro key
  have domains : sptDomain (numSetToExact (numSetFromExact tree)) key ↔ sptDomain tree key := by
    rw [domain_numSetToExact, mem_numSetFromExact]
  change sptLookup key (numSetToExact (numSetFromExact tree)) = sptLookup key tree
  cases first : sptLookup key (numSetToExact (numSetFromExact tree)) <;>
    cases second : sptLookup key tree
  · rfl
  · simp only [sptDomain, first, second, Option.isSome_none, Option.isSome_some] at domains
    cases domains.mpr trivial
  · simp only [sptDomain, first, second, Option.isSome_none, Option.isSome_some] at domains
    cases domains.mp trivial
  · congr

theorem colouringNumSet_production (colour : Nat → Nat) (names : List Nat) :
    LoopToWord.toNumSetHOL (wordApplyColourNumSet colour names) =
      applyNummapKey colour (LoopToWord.toNumSetHOL names) := by
  rw [wordApplyColourNumSet, applyNummapKeyExecutable, colouringListCodec,
    colouringListCodec, colouringUnitRoundTrip]
  exact sptWfFromAList _

theorem colouringCutsets_production (colour : Nat → Nat) (names : List Nat × List Nat) :
    wordCutsetsToHOL (wordApplyColourNumSets colour names) =
      applyNummapsKey colour (wordCutsetsToHOL names) := by
  rcases names with ⟨left, right⟩
  change (LoopToWord.toNumSetHOL (wordApplyColourNumSet colour left),
    LoopToWord.toNumSetHOL (wordApplyColourNumSet colour right)) =
    (applyNummapKey colour (LoopToWord.toNumSetHOL left),
     applyNummapKey colour (LoopToWord.toNumSetHOL right))
  rw [colouringNumSet_production, colouringNumSet_production]

end Flapjack.WordAlloc
