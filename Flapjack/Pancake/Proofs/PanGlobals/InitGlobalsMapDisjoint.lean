import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsRanges

namespace Flapjack.PanGlobalsInitGlobalsMapDisjoint
open Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Flapjack-specific original initializer map-update obligation (HOL
2300-2327). Original block separation and old-global/free-range disjointness
imply separation after both maps update at the initializer name. Arbitrary
replacement names are allowed; no fresh-name or scalar restriction is used.
This composition has no independently named HOL declaration. -/
theorem initializerMapsDisjoint {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (name : MlS)
    (shape : ShapeHOL) (value : ValueHOL width) (tailSize : Nat)
    (hrel : panGlobalsStateRelHOLExact false context source target)
    (hfree : ∀ key sh offset,
      (source.globals.lookup key).isSome = true ∧
        context.globals.lookup key = some (sh, offset) →
      ∀ address, addresses (target.topAddr - offset) (sizeOfShapeHOL sh) address →
        ¬ addresses (target.topAddr - panBytesInWord width *
          BitVec.ofNat width (sizeOfShapeHOL shape + tailSize) - context.globalsSize)
          (sizeOfShapeHOL shape + tailSize) address) :
    disjointGlobalsHOLExact target.topAddr
      (context.globals.updateEq (name, (shape, context.globalsSize + panBytesInWord width *
        BitVec.ofNat width (sizeOfShapeHOL shape))))
      (PanSemStateFiniteExact.setGlobalHOLFinite name value source).globals := by
  classical
  let offset := context.globalsSize + panBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL shape)
  let freeBase := target.topAddr - panBytesInWord width *
    BitVec.ofNat width (sizeOfShapeHOL shape + tailSize) - context.globalsSize
  have hbase : freeBase + panBytesInWord width * BitVec.ofNat width tailSize =
      target.topAddr - offset :=
    PanGlobalsInitGlobalsRanges.headAllocationBase target.topAddr context.globalsSize
      (sizeOfShapeHOL shape) tailSize
  have hhead : ∀ address, addresses (target.topAddr - offset) (sizeOfShapeHOL shape) address →
      addresses freeBase (sizeOfShapeHOL shape + tailSize) address := by
    intro address h
    rw [← hbase] at h
    have h' := (PanGlobalsMemStores.addresses_add tailSize (sizeOfShapeHOL shape)
      freeBase address).mpr (Or.inr (by simpa only [panBytesInWord] using h))
    simpa only [Nat.add_comm] using h'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdisjoint, _⟩ := hrel
  intro key key' sh addr sh' addr' hne hk hk' hc hc' address
  change (source.globals.update (name, value)).lookup key ≠ none at hk
  change (source.globals.update (name, value)).lookup key' ≠ none at hk'
  by_cases heq : key = name
  · subst key
    have hother : key' ≠ name := Ne.symm hne
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
    have hold : source.globals.lookup key' ≠ none := by
      simpa [HolFiniteMapExact.lookup_update_pointwise, FUPDATE, hother, Ne.symm hother] using hk'
    have hctx : context.globals.lookup key' = some (sh', addr') := by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hother] using hc'
    rintro ⟨hnew, holdBlock⟩
    have hsome : (source.globals.lookup key').isSome = true := by
      cases h : source.globals.lookup key' <;> simp_all
    exact hfree key' sh' addr' ⟨hsome, hctx⟩ address holdBlock (hhead address hnew)
  · have hold : source.globals.lookup key ≠ none := by
      simpa [HolFiniteMapExact.lookup_update_pointwise, FUPDATE, heq, Ne.symm heq] using hk
    have hctx : context.globals.lookup key = some (sh, addr) := by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, heq] using hc
    by_cases heq' : key' = name
    · subst key'
      simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hc'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc')
      rintro ⟨holdBlock, hnew⟩
      have hsome : (source.globals.lookup key).isSome = true := by
        cases h : source.globals.lookup key <;> simp_all
      exact hfree key sh addr ⟨hsome, hctx⟩ address holdBlock (hhead address hnew)
    · have hold' : source.globals.lookup key' ≠ none := by
        simpa [HolFiniteMapExact.lookup_update_pointwise, FUPDATE, heq', Ne.symm heq'] using hk'
      have hctx' : context.globals.lookup key' = some (sh', addr') := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, heq'] using hc'
      exact hdisjoint key key' sh addr sh' addr' hne hold hold' hctx hctx' address

end Flapjack.PanGlobalsInitGlobalsMapDisjoint
