import Flapjack.Compiler.Backend.RegAlloc.ProductionNumSet
import Flapjack.Compiler.Backend.RegAlloc.Remap

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc

/-- Canonical native input tree reconstructed from the executed list carrier.
This is Flapjack correspondence infrastructure, not a HOL datatype port.
Original WordAlloc producer correspondence is a separate obligation. -/
def productionClashTreeToNative : WordClashTree → ClashTree
  | .delta writes reads => .delta writes reads
  | .set names => .set (sptFromAList (names.map (fun name => (name, ()))))
  | .branch live left right => .branch
      (live.map (fun names => sptFromAList (names.map (fun name => (name, ())))))
      (productionClashTreeToNative left) (productionClashTreeToNative right)
  | .seq left right => .seq (productionClashTreeToNative left) (productionClashTreeToNative right)

/-- Canonical conversion of both actual binding histories and the fresh counter.
The membership accelerator is intentionally absent from the native carrier. -/
def productionBijectionBuildToNative (built : CakeNodeBijectionBuild) : Spt Nat × Spt Nat × Nat :=
  (sptFromAList built.toAllocator, sptFromAList built.fromAllocator, built.nextNode)

private theorem lookupCodec (key : Nat) (entries : NatInfoMap Nat) :
    sptLookup key (sptFromAList entries) = lookupNatInfo key entries := by
  rw [sptLookup_sptFromAList]
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name, value⟩ := entry
    by_cases equal : key = name
    · subst name; simp [sptAListLookup, lookupNatInfo]
    · simp [sptAListLookup, lookupNatInfo, equal, Ne.symm equal, ih]

/-- Full executed indexed remapping, including duplicate skips and both maps,
agrees with native listRemap. The index premise concerns the incoming builder;
the complete producer below constructs it from empty input. No output premise
or allocation-success premise is used. Untagged actual/native infrastructure. -/
theorem listRemapBuild_production (names : List Nat) (built : CakeNodeBijectionBuild)
    (indexed : ∀ key, built.index[key]? = lookupNatInfo key built.toAllocator) :
    listRemap names (productionBijectionBuildToNative built) =
      productionBijectionBuildToNative (cakeListRemapBuild names built) := by
  induction names generalizing built with
  | nil => rfl
  | cons name rest ih =>
    have lookup : sptLookup name (sptFromAList built.toAllocator) = built.index[name]? :=
      (lookupCodec name built.toAllocator).trans (indexed name).symm
    simp only [productionBijectionBuildToNative, listRemap, cakeListRemapBuild, lookup]
    cases present : built.index[name]? with
    | some value => simpa only [productionBijectionBuildToNative] using ih built indexed
    | none =>
      let fresh : CakeNodeBijectionBuild :=
        { toAllocator := (name, built.nextNode) :: built.toAllocator
          fromAllocator := (built.nextNode, name) :: built.fromAllocator
          index := built.index.insert name built.nextNode
          nextNode := built.nextNode + 1 }
      have nextIndexed : ∀ key, fresh.index[key]? = lookupNatInfo key fresh.toAllocator := by
        intro key
        simp [fresh, Std.TreeMap.getElem?_insert, lookupNatInfo, indexed]
      simpa only [productionBijectionBuildToNative, fresh, sptFromAList] using ih fresh nextIndexed

private theorem setKeys (names : List Nat) :
    (sptToAList (sptFromAList (names.map (fun name => (name, ()))))).map Prod.fst =
      Flapjack.NumSet.fromAList names := by
  have keys := congrArg (List.map Prod.fst) (numSetFromAList_production names)
  simpa [List.map_map, Function.comp_def] using keys.symm

/-- Complete executed traversal agrees with the native traversal on the
canonical input codec. Set enumeration uses the proved mixed tree order;
Delta reads first, Branch visits left first, and Seq visits right first.
This infrastructure assumes only the incoming accelerator invariant. -/
theorem mkBijBuildAux_production (tree : WordClashTree) (built : CakeNodeBijectionBuild)
    (indexed : ∀ key, built.index[key]? = lookupNatInfo key built.toAllocator) :
    mkBijAux (productionClashTreeToNative tree) (productionBijectionBuildToNative built) =
      productionBijectionBuildToNative (cakeMkBijBuildAux tree built) := by
  induction tree generalizing built with
  | delta writes reads =>
    simp only [productionClashTreeToNative, mkBijAux, cakeMkBijBuildAux]
    rw [listRemapBuild_production reads built indexed]
    exact listRemapBuild_production writes _ (Flapjack.listRemapBuild_index reads built indexed)
  | set names =>
    simp only [productionClashTreeToNative, mkBijAux, cakeMkBijBuildAux, setKeys]
    exact listRemapBuild_production _ _ indexed
  | branch live left right leftIH rightIH =>
    simp only [productionClashTreeToNative, mkBijAux, cakeMkBijBuildAux]
    rw [leftIH built indexed, rightIH _ (Flapjack.mkBijBuildAux_index left built indexed)]
    cases live with
    | none => rfl
    | some names =>
      simp only [Option.map_some, setKeys]
      exact listRemapBuild_production _ _
        (Flapjack.mkBijBuildAux_index right _ (Flapjack.mkBijBuildAux_index left built indexed))
  | seq left right leftIH rightIH =>
    simp only [productionClashTreeToNative, mkBijAux, cakeMkBijBuildAux]
    rw [rightIH built indexed]
    exact leftIH _ (Flapjack.mkBijBuildAux_index right built indexed)

/-- Whole executed producer: both native maps and the fresh counter are
constructed from empty input, with the actual ordered membership invariant
discharged. This establishes the canonical tree-codec boundary; original
WordAlloc input production and full allocator graph initialization remain
separate obligations. Untagged production correspondence infrastructure. -/
theorem mkBij_production (tree : WordClashTree) :
    mkBij (productionClashTreeToNative tree) =
      (sptFromAList (cakeMkBij tree).toAllocator,
       sptFromAList (cakeMkBij tree).fromAllocator, (cakeMkBij tree).nextNode) := by
  have run := mkBijBuildAux_production tree
    { toAllocator := [], fromAllocator := [], index := {}, nextNode := 0 }
    (by intro key; simp [lookupNatInfo])
  simpa only [mkBij, cakeMkBij, cakeMkBijBuild, productionBijectionBuildToNative,
    sptFromAList] using run

end Flapjack.RegAlloc
