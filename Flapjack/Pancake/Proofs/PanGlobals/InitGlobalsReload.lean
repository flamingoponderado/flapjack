import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsShape
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.MemStores

namespace Flapjack.PanGlobalsInitGlobalsReload
open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

/-- Flapjack-specific composition for the initializer's new-global lookup
obligation (HOL 2240-2260). Original source evaluation and state_rel derive
shape validity; the original combined-size bound implies the head's strict
reload bound. A store equation is an internal proof premise about its result
memory, not a target-run premise of initializer correctness. No independent
HOL declaration is claimed, and arbitrary structured values are retained. -/
theorem initializerHeadReload {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (expression : ExpHOL width)
    (value : ValueHOL width) (shape : ShapeHOL) (tailSize : Nat)
    (memory : BitVec width → HolWordLab width)
    (hrel : panGlobalsStateRelHOLExact false context source target)
    (heval : @evalHOLFinite width σ _ source.emptyLocalsHOLFinite
      (fun a => Classical.propDecidable (source.memaddrs a)) expression = some value)
    (hshape : shapeOfHOLExact value = shape)
    (hbound : (panBytesInWord width).toNat * (sizeOfShapeHOL shape + tailSize) < 2 ^ width)
    (hstore : @panMemStoresHOL width _
      (target.topAddr - (context.globalsSize + panBytesInWord width *
        BitVec.ofNat width (sizeOfShapeHOL shape))) (flattenHOL value) target.memaddrs
      (fun a => Classical.propDecidable (target.memaddrs a)) target.memory = some memory) :
    isWfShapeNilHOL shape = true ∧
    @memLoadHOLExact width _ shape
      (target.topAddr - (context.globalsSize + panBytesInWord width *
        BitVec.ofNat width (sizeOfShapeHOL shape))) target.memaddrs
      (fun a => Classical.propDecidable (target.memaddrs a)) memory [] = some value := by
  classical
  have hcleared :=
    (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context source target true).2 hrel
  have hwf := PanGlobalsInitGlobalsShape.evalStateRelIsWfShapeHOL
    source.emptyLocalsHOLFinite target.emptyLocalsHOLFinite expression value true context
    ⟨heval, hcleared, by
      intro name bound hlookup
      simp [emptyLocalsHOLFinite] at hlookup⟩
  have hlength := flattenHOL_length_eq_sizeOfShapeHOL value hwf
  have hheadBound : (flattenHOL value).length * (panBytesInWord width).toNat < 2 ^ width := by
    rw [hlength, hshape, Nat.mul_comm]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) hbound
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwidth⟩ := hrel
  have hreload := PanGlobalsMemStores.memStoresMemLoadBackHOL.1 value
    (target.topAddr - (context.globalsSize + panBytesInWord width *
      BitVec.ofNat width (sizeOfShapeHOL shape))) target.memaddrs target.memory memory []
    ⟨hstore, hheadBound, hwf, rfl, hwidth⟩
  exact ⟨by rw [← hshape]; exact hwf, by simpa only [hshape] using hreload⟩

end Flapjack.PanGlobalsInitGlobalsReload
