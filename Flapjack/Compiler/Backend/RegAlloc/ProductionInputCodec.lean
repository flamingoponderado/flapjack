import Flapjack.Compiler.Backend.RegAlloc.ProductionBijection

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc

/-- Original native tree rendered in the executed list carrier. This codec is
Flapjack infrastructure; establishing that actual WordAlloc producers supply
this rendering is a separate obligation. -/
def nativeClashTreeToProduction : ClashTree → WordClashTree
  | .delta writes reads => .delta writes reads
  | .set live => .set ((sptToAList live).map Prod.fst)
  | .branch live left right => .branch
      (live.map (fun set => (sptToAList set).map Prod.fst))
      (nativeClashTreeToProduction left) (nativeClashTreeToProduction right)
  | .seq left right => .seq (nativeClashTreeToProduction left) (nativeClashTreeToProduction right)

/-- Real validity of original unit sets at every source constructor. This
predicate supplies no compiler result or correspondence premise. -/
def NativeClashTreeSetsWf : ClashTree → Prop
  | .delta _ _ => True
  | .set live => sptWf live = true
  | .branch live left right =>
      (∀ set, live = some set → sptWf set = true) ∧
      NativeClashTreeSetsWf left ∧ NativeClashTreeSetsWf right
  | .seq left right => NativeClashTreeSetsWf left ∧ NativeClashTreeSetsWf right

private theorem unitAssociations (entries : List (Nat × Unit)) :
    (entries.map Prod.fst).map (fun key => (key, ())) = entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, payload⟩ := entry
    cases payload
    simp only [List.map_cons, ih]

private theorem unitRoundtrip (tree : NumSet) (wellFormed : sptWf tree = true) :
    sptFromAList (((sptToAList tree).map Prod.fst).map (fun key => (key, ()))) = tree := by
  rw [unitAssociations]
  exact (sptEqThm _ _ ⟨sptWfFromAList _, wellFormed⟩).mpr
    (fun key => sptLookup_sptFromAList_sptToAList key tree)

/-- The executed input codec reconstructs every original well-formed unit set
and preserves the full tree, including both branch children and optional live
sets. Untagged carrier infrastructure, not a source producer theorem. -/
theorem clashTreeCodec_roundtrip (tree : ClashTree) (wellFormed : NativeClashTreeSetsWf tree) :
    productionClashTreeToNative (nativeClashTreeToProduction tree) = tree := by
  induction tree with
  | delta writes reads => rfl
  | set live => exact congrArg ClashTree.set (unitRoundtrip live wellFormed)
  | branch live left right leftIH rightIH =>
    obtain ⟨sets, leftWf, rightWf⟩ := wellFormed
    cases live with
    | none => simp only [nativeClashTreeToProduction, productionClashTreeToNative,
        Option.map_none, leftIH leftWf, rightIH rightWf]
    | some live => simp only [nativeClashTreeToProduction, productionClashTreeToNative,
        Option.map_some, unitRoundtrip live (sets live rfl), leftIH leftWf, rightIH rightWf]
  | seq left right leftIH rightIH =>
    simp only [nativeClashTreeToProduction, productionClashTreeToNative,
      leftIH wellFormed.1, rightIH wellFormed.2]

/-- The complete executed indexed bijection on a rendered original input
returns exactly the original two maps and counter. Set validity is a genuine
source input requirement; no target maps, counter, or successful evaluation
are assumed. Actual WordAlloc producer discharge remains open. -/
theorem mkBij_nativeInput_production (tree : ClashTree) (wellFormed : NativeClashTreeSetsWf tree) :
    mkBij tree =
      (sptFromAList (cakeMkBij (nativeClashTreeToProduction tree)).toAllocator,
       sptFromAList (cakeMkBij (nativeClashTreeToProduction tree)).fromAllocator,
       (cakeMkBij (nativeClashTreeToProduction tree)).nextNode) := by
  have run := mkBij_production (nativeClashTreeToProduction tree)
  rw [clashTreeCodec_roundtrip tree wellFormed] at run
  exact run

end Flapjack.RegAlloc
