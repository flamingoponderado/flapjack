import Flapjack.Pancake.Proofs.PanGlobals.GlobalBlockAlignment
import Flapjack.Pancake.Proofs.PanGlobals.MemStores

namespace Flapjack.PanGlobalsGlobalStoreReload

open Flapjack.Pancake.PanLang
open Flapjack.PanGlobalsMemStores

/-- Flapjack source-derived certificate for original Assign543-568. Successful
storage and shaped reload are derived from the original state relation; this
synthesized statement is not a separate HOL declaration or a compiler theorem.
It admits arbitrary values and derives alignment and the strict nonwrapping
length bound internally rather than exposing extra compiler assumptions. -/
theorem stateRel_storeReload {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ)
    (name : MlS) (oldValue value : ValueHOL width)
    (hrel : panGlobalsStateRelHOLExact true context source target)
    (hlookup : source.globals.lookup name = some oldValue)
    (hshape : shapeOfHOLExact value = shapeOfHOLExact oldValue) :
    letI : DecidablePred target.memaddrs := fun a => Classical.propDecidable (target.memaddrs a)
    ∃ address memory,
      context.globals.lookup name = some (shapeOfHOLExact value, address) ∧
      panMemStoresHOL (target.topAddr - address) (flattenHOL value)
        target.memaddrs target.memory = some memory ∧
      memLoadHOLExact (shapeOfHOLExact value) (target.topAddr - address)
        target.memaddrs memory [] = some value := by
  classical
  rcases hrel with ⟨_, _, _, _, _, _, _, _, hglobals, _, _, _, _, _, _, _, hnot, htop, hw⟩
  obtain ⟨address, hc, hwf, hload, _, ha⟩ := hglobals name oldValue hlookup
  have hwf' : isWfShapeExactHOL ([] : Flapjack.Pancake.PanLang.StructContextExact) (shapeOfHOLExact value) = true := by
    simpa [hshape, isWfShapeNilHOL] using hwf
  obtain ⟨memory, hstore⟩ := memLoadMemStoreHOL.1
    (shapeOfHOLExact oldValue) (target.topAddr - address) target.memaddrs target.memory
    [] oldValue value ⟨hload, rfl, by simpa [hshape] using hwf', hshape⟩
  have haligned := PanGlobalsGlobalBlockAlignment.byteAligned_sub target.topAddr address hw htop ha
  have hbound := memStoresBoundedLengthHOL (target.topAddr - address) (flattenHOL value)
    target.memaddrs target.memory memory target.topAddr ⟨hstore, hnot, haligned, htop, hw⟩
  have hstrict : (flattenHOL value).length * (panBytesInWord width).toNat < 2 ^ width := by
    have hlt := (target.topAddr - (target.topAddr - address)).isLt
    rw [Nat.mul_comm] at hbound
    omega
  refine ⟨address, memory, ?_, hstore, ?_⟩
  · simpa [hshape] using hc
  · exact memStoresMemLoadBackHOL.1 value (target.topAddr - address) target.memaddrs
      target.memory memory [] ⟨hstore, hstrict, hwf', rfl, hw⟩

end Flapjack.PanGlobalsGlobalStoreReload
