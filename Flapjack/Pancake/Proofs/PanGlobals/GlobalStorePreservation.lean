import Flapjack.Pancake.Proofs.PanGlobals.MemStores
import Flapjack.Pancake.Proofs.PanGlobals.MemoryLookup

namespace Flapjack.PanGlobalsGlobalStorePreservation

open Flapjack.Pancake.PanLang
open Flapjack.PanGlobalsMemStores
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Flapjack source-derived certificate for original Assign573-585. A shaped
store to an existing global leaves all other global loads and source-domain
memory cells unchanged. The store premise is an internal memory obligation,
derived separately from the original state relation by the Assign caller;
this synthesized helper is not a tagged compiler correctness theorem. -/
theorem stateRel_storePreserves {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ)
    (name : MlS) (oldValue value : ValueHOL width) (address : BitVec width)
    (memory : BitVec width → HolWordLab width)
    (hrel : panGlobalsStateRelHOLExact true context source target)
    (hlookup : source.globals.lookup name = some oldValue)
    (hcontext : context.globals.lookup name = some (shapeOfHOLExact oldValue, address))
    (hshape : shapeOfHOLExact value = shapeOfHOLExact oldValue)
    (hstore : letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
      panMemStoresHOL (target.topAddr - address) (flattenHOL value)
        target.memaddrs target.memory = some memory) :
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    (∀ name' value', name' ≠ name → source.globals.lookup name' = some value' →
      ∃ address', context.globals.lookup name' = some (shapeOfHOLExact value', address') ∧
        memLoadHOLExact (shapeOfHOLExact value') (target.topAddr - address')
          target.memaddrs memory [] = some value') ∧
    (∀ slot, source.memaddrs slot → source.memory slot = memory slot) := by
  classical
  rcases hrel with ⟨_, _, _, _, _, _, _, _, hglobals, _, _, _, hmemory, _, _, hdisjoint, _, _, _⟩
  obtain ⟨address0, hc0, hwf, _, hseparate, _⟩ := hglobals name oldValue hlookup
  have heq : address0 = address := by
    rw [hcontext] at hc0
    exact (congrArg Prod.snd (Option.some.inj hc0)).symm
  subst address0
  have hwf' : isWfShapeExactHOL ([] : Flapjack.Pancake.PanLang.StructContextExact) (shapeOfHOLExact value) = true := by
    simpa [hshape, isWfShapeNilHOL] using hwf
  have hlength : (flattenHOL value).length = sizeOfShapeHOL (shapeOfHOLExact oldValue) := by
    simpa [hshape] using flattenHOL_length_eq_sizeOfShapeHOL value hwf'
  constructor
  · intro name' value' hne hlookup'
    obtain ⟨address', hc', hwf'', hload', _, _⟩ := hglobals name' value' hlookup'
    have hsep : ∀ slot, addresses (target.topAddr - address')
        (sizeOfShapeHOL (shapeOfHOLExact value')) slot →
        ¬ addresses (target.topAddr - address) (flattenHOL value).length slot := by
      intro slot hslot hwrite
      rw [hlength] at hwrite
      exact hdisjoint name' name (shapeOfHOLExact value') address'
        (shapeOfHOLExact oldValue) address hne (by simp [hlookup'])
        (by simp [hlookup]) hc' hcontext slot ⟨hslot, hwrite⟩
    refine ⟨address', hc', ?_⟩
    rw [memStoresLoadDisjointHOL.1 (shapeOfHOLExact value') (target.topAddr - address)
      (flattenHOL value) target.memaddrs target.memory memory [] (target.topAddr - address')
      ⟨hstore, rfl, by simpa [isWfShapeNilHOL] using hwf'', hsep⟩]
    exact hload'
  · intro slot hslot
    rw [hmemory slot hslot]
    symm
    apply PanGlobalsMemoryLookup.memStoresLookupHOL (target.topAddr - address)
      (flattenHOL value) target.memaddrs target.memory memory slot
    exact ⟨hstore, by simpa [hlength] using hseparate slot hslot⟩

end Flapjack.PanGlobalsGlobalStorePreservation
