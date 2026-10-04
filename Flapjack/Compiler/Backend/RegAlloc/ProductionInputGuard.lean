import Flapjack.Compiler.Backend.RegAlloc.ProductionInputCodec

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc

/-! Executable checks for the original allocator's input representation and
forced endpoint bounds. These implementation guards have no independent HOL
original. They reuse the reviewed input codec and assume no allocator output. -/

/-- Check every native unit-set carrier, including an optional branch live set. -/
def nativeClashTreeSetsWfCheck : ClashTree → Bool
  | .delta _ _ => true
  | .set live => sptWf live
  | .branch live left right =>
      (live.map sptWf |>.getD true) &&
        nativeClashTreeSetsWfCheck left && nativeClashTreeSetsWfCheck right
  | .seq left right => nativeClashTreeSetsWfCheck left && nativeClashTreeSetsWfCheck right

/-- The check accepts exactly the existing native tree validity predicate. -/
theorem nativeClashTreeSetsWfCheck_iff (tree : ClashTree) :
    nativeClashTreeSetsWfCheck tree = true ↔ NativeClashTreeSetsWf tree := by
  induction tree with
  | delta writes reads => simp [nativeClashTreeSetsWfCheck, NativeClashTreeSetsWf]
  | set live => rfl
  | branch live left right leftIH rightIH =>
      cases live <;> simp [nativeClashTreeSetsWfCheck, NativeClashTreeSetsWf, leftIH, rightIH, and_assoc]
  | seq left right leftIH rightIH =>
      simp [nativeClashTreeSetsWfCheck, NativeClashTreeSetsWf, leftIH, rightIH]

/-- Check the original forced endpoints through the actual rendered bijection.
The indexed lookup and dimension are the ones in `regAlloc_production`. -/
def nativeForcedBoundsCheck (tree : ClashTree) (forced : List (Nat × Nat)) : Bool :=
  let bijection := cakeMkBij (nativeClashTreeToProduction tree)
  let index := cakeSpDefaultIndex bijection.toAllocator
  forced.all fun pair =>
    decide (cakeSpDefaultIndexed index pair.1 < bijection.nextNode) &&
      decide (cakeSpDefaultIndexed index pair.2 < bijection.nextNode)

/-- Every endpoint, including absent names under the original default lookup,
is checked; this is precisely the existing wrapper's bound premise. -/
theorem nativeForcedBoundsCheck_iff (tree : ClashTree) (forced : List (Nat × Nat)) :
    nativeForcedBoundsCheck tree forced = true ↔
      ∀ pair ∈ forced,
        cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (nativeClashTreeToProduction tree)).toAllocator)
          pair.1 < (cakeMkBij (nativeClashTreeToProduction tree)).nextNode ∧
        cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (nativeClashTreeToProduction tree)).toAllocator)
          pair.2 < (cakeMkBij (nativeClashTreeToProduction tree)).nextNode := by
  simp [nativeForcedBoundsCheck, List.all_eq_true]

/-- Whole-input guard for the efficient realization. Invalid raw carriers or
forced endpoints select the caller's original allocator fallback. -/
def nativeRegAllocInputGuard (costs : Option (Spt Nat)) (tree : ClashTree)
    (forced : List (Nat × Nat)) (stackOnly : NumSet) : Bool :=
  nativeClashTreeSetsWfCheck tree && (costs.map sptWf |>.getD true) &&
    sptWf stackOnly && nativeForcedBoundsCheck tree forced

/-- Exact input-side requirements for the existing codec/wrapper composition;
there is no successful allocation, output map, or post-state premise. -/
theorem nativeRegAllocInputGuard_iff (costs : Option (Spt Nat)) (tree : ClashTree)
    (forced : List (Nat × Nat)) (stackOnly : NumSet) :
    nativeRegAllocInputGuard costs tree forced stackOnly = true ↔
      NativeClashTreeSetsWf tree ∧
      (∀ entries, costs = some entries → sptWf entries = true) ∧
      sptWf stackOnly = true ∧
      (∀ pair ∈ forced,
        cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (nativeClashTreeToProduction tree)).toAllocator)
          pair.1 < (cakeMkBij (nativeClashTreeToProduction tree)).nextNode ∧
        cakeSpDefaultIndexed
          (cakeSpDefaultIndex (cakeMkBij (nativeClashTreeToProduction tree)).toAllocator)
          pair.2 < (cakeMkBij (nativeClashTreeToProduction tree)).nextNode) := by
  cases costs <;>
    simp [nativeRegAllocInputGuard, nativeClashTreeSetsWfCheck_iff,
      nativeForcedBoundsCheck_iff, and_assoc]

end Flapjack.RegAlloc
