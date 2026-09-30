import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsRanges

namespace Flapjack.PanGlobalsInitGlobalsRecursiveDisjoint
open Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Flapjack-specific original initializer induction-premise certificate
(HOL 2182-2191). After both map updates, every present global block remains
disjoint from the recursive tail's free region. The new head uses the original
combined-size bound; old globals use original free-region disjointness and
tail containment. Name replacement is allowed. No new disjointness premise
or separately named HOL declaration is introduced. -/
theorem recursiveGlobalsFreeDisjoint {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (name : MlS)
    (shape : ShapeHOL) (value : ValueHOL width) (tailSize : Nat)
    (hrel : panGlobalsStateRelHOLExact false context source target)
    (hbound : (panBytesInWord width).toNat * (sizeOfShapeHOL shape + tailSize) < 2 ^ width)
    (hfree : ∀ key sh offset,
      (source.globals.lookup key).isSome = true ∧
        context.globals.lookup key = some (sh, offset) →
      ∀ address, addresses (target.topAddr - offset) (sizeOfShapeHOL sh) address →
        ¬ addresses (target.topAddr - panBytesInWord width *
          BitVec.ofNat width (sizeOfShapeHOL shape + tailSize) - context.globalsSize)
          (sizeOfShapeHOL shape + tailSize) address) :
    let nextOffset := context.globalsSize + panBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL shape)
    ∀ key sh offset,
      ((PanSemStateFiniteExact.setGlobalHOLFinite name value source).globals.lookup key).isSome = true ∧
        (context.globals.updateEq (name, (shape, nextOffset))).lookup key = some (sh, offset) →
      ∀ address, addresses (target.topAddr - offset) (sizeOfShapeHOL sh) address →
        ¬ addresses (target.topAddr - panBytesInWord width * BitVec.ofNat width tailSize - nextOffset)
          tailSize address := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwidth⟩ := hrel
  obtain ⟨hprefix, _, hseparate⟩ := PanGlobalsInitGlobalsRanges.allocationPartition
    target.topAddr context.globalsSize (sizeOfShapeHOL shape) tailSize hwidth hbound
  dsimp only
  intro key sh offset ⟨hpresent, hcontext⟩ address hblock
  rw [← PanGlobalsInitGlobalsRanges.recursiveFreeBase target.topAddr context.globalsSize
    (sizeOfShapeHOL shape) tailSize]
  intro htail
  by_cases hkey : key = name
  · subst key
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hcontext
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcontext)
    exact hseparate address htail hblock
  · have hold : (source.globals.lookup key).isSome = true := by
      simpa [PanSemStateFiniteExact.setGlobalHOLFinite,
        HolFiniteMapExact.lookup_update_pointwise, FUPDATE, hkey, Ne.symm hkey] using hpresent
    have hctx : context.globals.lookup key = some (sh, offset) := by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hkey] using hcontext
    exact hfree key sh offset ⟨hold, hctx⟩ address hblock (hprefix address htail)

end Flapjack.PanGlobalsInitGlobalsRecursiveDisjoint
