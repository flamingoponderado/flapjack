import Flapjack.Pancake.LoopToWord.ContextBridge
import Flapjack.Pipeline

/-!
# Checked parity for the production ↔ exact `loop_to_word` context bridge

Bead `flapjack-pxn.18.5.9.7`.  These fixtures exercise the untagged Flapjack
adapter `Flapjack.LoopToWord.natInfoMapToSpt` and its lookup agreement against
the production `Flapjack.WordContext` and the exact HOL context carrier used by
`findVarHOL`, including the accepted `pipelineWordContext` bridge
(`Flapjack.Pipeline`).  They are infrastructure tests, not HOL probes.
-/

namespace Flapjack.Test.LoopToWordContextBridgeParity

open Flapjack Flapjack.LoopToWord

/-! ## Adapter agreement on concrete maps -/

/-- First-match of `[(3, 7), (5, 9)]` is preserved by the right-recursive
insertion. -/
example : sptLookup 3 (natInfoMapToSpt [(3, 7), (5, 9)]) = some 7 := by
  rw [sptLookup_natInfoMapToSpt]
  simp [lookupNatInfo]

example : sptLookup 5 (natInfoMapToSpt [(3, 7), (5, 9)]) = some 9 := by
  rw [sptLookup_natInfoMapToSpt]
  simp [lookupNatInfo]

example : sptLookup 4 (natInfoMapToSpt [(3, 7), (5, 9)]) = none := by
  rw [sptLookup_natInfoMapToSpt]
  simp [lookupNatInfo]

/-- Duplicate keys follow the association list's first match: the head is
inserted last and wins. -/
example : sptLookup 1 (natInfoMapToSpt [(1, 10), (2, 20), (1, 30)]) = some 10 := by
  rw [sptLookup_natInfoMapToSpt]
  simp [lookupNatInfo]

example : sptLookup 2 (natInfoMapToSpt [(1, 10), (2, 20), (1, 30)]) = some 20 := by
  rw [sptLookup_natInfoMapToSpt]
  simp [lookupNatInfo]

/-! ## Agreement with the production `pipelineWordContext`

The adapter of `(pipelineWordContext slots).vars` looks up every present slot at
its assigned register `name + 2`, matching the existing
`wordFindVar_pipelineWordContext_of_mem`. -/

theorem sptLookup_natInfoMapToSpt_pipelineWordContext_of_mem
    (slots : List Nat) (name : Nat) (hmem : name ∈ slots) :
    sptLookup name (natInfoMapToSpt (pipelineWordContext slots).vars) =
      some (name + 2) := by
  rw [sptLookup_natInfoMapToSpt, pipelineWordContext]
  exact lookupNatInfo_map_add_two_of_mem slots name hmem

/-- The exact `findVarHOL` over the adapter returns the same register as the
production `wordFindVar` for every present pipeline slot. -/
theorem findVarHOL_natInfoMapToSpt_pipelineWordContext_of_mem
    (slots : List Nat) (name : Nat) (hmem : name ∈ slots) :
    findVarHOL (natInfoMapToSpt (pipelineWordContext slots).vars) name = name + 2 := by
  unfold findVarHOL
  rw [sptLookup_natInfoMapToSpt_pipelineWordContext_of_mem slots name hmem]
  rfl

/-- Production/exact agreement through the adapter and the accepted
`wordFindVar_pipelineWordContext_of_mem` bridge. -/
theorem wordFindVar_eq_findVarHOL_pipelineWordContext_of_mem
    (slots : List Nat) (name : Nat) (hmem : name ∈ slots) :
    wordFindVar (pipelineWordContext slots) name =
      findVarHOL (natInfoMapToSpt (pipelineWordContext slots).vars) name := by
  apply wordFindVar_eq_findVarHOL_of_present
  rw [pipelineWordContext]
  exact lookupNatInfo_map_add_two_of_mem slots name hmem

/-- The kernel-checked combination of the adapter agreement with the existing
`wordFindVar_pipelineWordContext_of_mem`. -/
example : sptLookup 7 (natInfoMapToSpt (pipelineWordContext [4, 7]).vars) = some 9 :=
  sptLookup_natInfoMapToSpt_pipelineWordContext_of_mem [4, 7] 7 (by simp)

example : wordFindVar (pipelineWordContext [4, 7]) 7 =
    findVarHOL (natInfoMapToSpt (pipelineWordContext [4, 7]).vars) 7 :=
  wordFindVar_eq_findVarHOL_pipelineWordContext_of_mem [4, 7] 7 (by simp)

/-- Probe context `[(3, 7), (5, 9)]` used by the `runChecks` rows. -/
def bridgeProbeMap : NatInfoMap Nat := [(3, 7), (5, 9)]

/-- Probe pipeline slots for the `runChecks` rows. -/
def bridgeProbeSlots : List Nat := [4, 7]

def runChecks : IO Bool := do
  let checks :=
    [ ("LoopToWord context bridge preserves first-match 3 -> 7",
        sptLookup 3 (natInfoMapToSpt bridgeProbeMap) == some 7),
      ("LoopToWord context bridge preserves first-match 5 -> 9",
        sptLookup 5 (natInfoMapToSpt bridgeProbeMap) == some 9),
      ("LoopToWord context bridge leaves 4 absent",
        sptLookup 4 (natInfoMapToSpt bridgeProbeMap) == none),
      ("LoopToWord context bridge duplicate key keeps the head value",
        sptLookup 1 (natInfoMapToSpt [(1, 10), (2, 20), (1, 30)]) == some 10),
      ("LoopToWord context bridge matches pipelineWordContext slots",
        sptLookup 7 (natInfoMapToSpt (pipelineWordContext bridgeProbeSlots).vars) ==
          some 9),
      ("LoopToWord exact findVarHOL matches production wordFindVar on a present key",
        wordFindVar (pipelineWordContext bridgeProbeSlots) 7 ==
          findVarHOL (natInfoMapToSpt (pipelineWordContext bridgeProbeSlots).vars) 7) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopToWordContextBridgeParity
