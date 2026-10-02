import Flapjack.Compiler.Backend.RegAlloc.ProductionMkGraph
import Flapjack.Compiler.Backend.RegAlloc.Proofs.MkBij

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc

/-- Original bijection construction bounds every produced forward lookup,
without an assumed desired map or post-state. This untagged specialization
combines the already ported native empty-input bijection invariants. -/
theorem mkBij_lookup_bound (tree : ClashTree) (name node : Nat)
    (lookup : sptLookup name (mkBij tree).1 = some node) :
    node < (mkBij tree).2.2 := by
  rcases built : mkBijAux tree (.ln, .ln, 0) with ⟨forward, reverse, dimension⟩
  have emptyInverse : spInverts (.ln : Spt Nat) .ln := by
    intro key value found
    simp [sptLookup] at found
  have emptyDomain : sptDomain (.ln : Spt Nat) = (fun key => key < 0) := by
    funext key
    simp [sptDomain, sptLookup]
  have invariants := mkBijAuxBij tree .ln .ln 0 forward reverse dimension
    ⟨built, emptyInverse, emptyInverse, emptyDomain⟩
  have result : mkBij tree = (forward, reverse, dimension) := by
    simp only [mkBij, built]
  rw [result] at lookup ⊢
  have inverse := invariants.1 name node lookup
  have belongs : sptDomain reverse node := by simp [sptDomain, inverse]
  rw [invariants.2.2] at belongs
  exact belongs

/-- The actual indexed forward decoder has a bounded result whenever its
original produced forward map contains the name. The complete builder
correspondence discharges the native bijection premise. Untagged actual
initializer infrastructure; absent physical-name behavior is not changed. -/
theorem producedAllocator_lookup_bound (tree : WordClashTree) (name node : Nat)
    (lookup : sptLookup name (sptFromAList (cakeMkBij tree).toAllocator) = some node) :
    node < (cakeMkBij tree).nextNode := by
  have bound := mkBij_lookup_bound (productionClashTreeToNative tree) name node
  rw [mkBij_production] at bound
  exact bound lookup

/-- Every original clash-tree name is in the produced forward domain and
therefore has a bounded native default-decoder value. The domain fact is
derived from mkBijAuxDomain, rather than supplied as an input assumption.
Untagged empty-input specialization used by actual initializer assembly. -/
theorem mkBij_name_bound (tree : ClashTree) (name : Nat) (belongs : inClashTree tree name) :
    Flapjack.spDefault (mkBij tree).1 name < (mkBij tree).2.2 := by
  rcases built : mkBijAux tree (.ln, .ln, 0) with ⟨forward, reverse, dimension⟩
  have domain := mkBijAuxDomain tree .ln .ln 0 forward reverse dimension built
  have result : mkBij tree = (forward, reverse, dimension) := by
    simp only [mkBij, built]
  have available : sptDomain forward name := by
    rw [domain]
    exact Or.inr belongs
  cases found : sptLookup name forward with
  | none => simp [sptDomain, found] at available
  | some node =>
    have bound := mkBij_lookup_bound tree name node (by simpa only [result] using found)
    simpa only [result, Flapjack.spDefault, found, Option.getD_some] using bound

/-- The actual initializer's indexed forward decoder is bounded for every
name of its native input codec. Both the real builder and real decoder are
used; neither a desired graph nor successful target evaluation is assumed.
Untagged actual/native initializer infrastructure. -/
theorem producedAllocator_name_bound (tree : WordClashTree) (name : Nat)
    (belongs : inClashTree (productionClashTreeToNative tree) name) :
    cakeSpDefaultIndexed (cakeSpDefaultIndex (cakeMkBij tree).toAllocator) name <
      (cakeMkBij tree).nextNode := by
  rw [tagDecoder_production]
  have bound := mkBij_name_bound (productionClashTreeToNative tree) name belongs
  simpa only [mkBij_production] using bound

private theorem enumeratedName_domain (names : List Nat) (name : Nat)
    (belongs : name ∈ NumSet.fromAList names) :
    sptDomain (sptFromAList (names.map (fun key => (key, ())))) name := by
  apply (sptMemMapFstToAList _ _).mp
  have keys := congrArg (List.map Prod.fst) (numSetFromAList_production names)
  have same : (sptToAList (sptFromAList (names.map (fun key => (key, ()))))).map Prod.fst =
      NumSet.fromAList names := by
    simpa [List.map_map, Function.comp_def] using keys.symm
  rwa [same]

/-- The graph input bound predicate follows from bounds on original clash
names. Exact native set-domain correspondence discharges Set and optional
Branch sets. Untagged input-domain infrastructure, independent of graph output. -/
theorem graphInputBound_of_clashNames (ta : Nat → Nat) (dimension : Nat) (tree : WordClashTree)
    (bounds : ∀ name, inClashTree (productionClashTreeToNative tree) name → ta name < dimension) :
    ProductionGraphInputBound ta dimension tree := by
  induction tree with
  | delta writes reads =>
    exact ⟨fun name belongs => bounds name (Or.inl belongs),
      fun name belongs => bounds name (Or.inr belongs)⟩
  | set names =>
    exact fun name belongs => bounds name (enumeratedName_domain names name belongs)
  | branch live left right ihLeft ihRight =>
    refine ⟨ihLeft (fun name belongs => bounds name (Or.inl belongs)),
      ihRight (fun name belongs => bounds name (Or.inr (Or.inl belongs))), ?_⟩
    intro names equal name belongs
    subst live
    exact bounds name (Or.inr (Or.inr (enumeratedName_domain names name belongs)))
  | seq left right ihLeft ihRight =>
    exact ⟨ihLeft (fun name belongs => bounds name (Or.inl belongs)),
      ihRight (fun name belongs => bounds name (Or.inr belongs))⟩

/-- The executed initializer's produced bijection discharges the complete
graph input-node domain. No bound on the desired graph or target state is
assumed, and the indexed production decoder is the actual caller's decoder.
Untagged original-input premise discharge for full initializer assembly. -/
theorem producedAllocator_graphInputBound (tree : WordClashTree) :
    ProductionGraphInputBound
      (cakeSpDefaultIndexed (cakeSpDefaultIndex (cakeMkBij tree).toAllocator))
      (cakeMkBij tree).nextNode tree := by
  exact graphInputBound_of_clashNames _ _ tree (producedAllocator_name_bound tree)

end Flapjack.RegAlloc
