import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsShape
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.MemStores
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsRanges

namespace Flapjack.PanGlobalsInitGlobalsOldLoads
open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Flapjack-specific initializer old-global lookup certificate (HOL
2245-2285). The original old-global/free-range disjointness premise is used;
head-footprint containment and initializer shape validity are derived.
Store success is an internal equation about the memory being inspected,
not a compiler correctness premise. No independently named HOL theorem. -/
theorem initializerOldGlobalLoads {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (expression : ExpHOL width)
    (value : ValueHOL width) (shape : ShapeHOL) (tailSize : Nat)
    (memory : BitVec width → HolWordLab width)
    (hrel : panGlobalsStateRelHOLExact false context source target)
    (heval : @evalHOLFinite width σ _ source.emptyLocalsHOLFinite
      (fun a => Classical.propDecidable (source.memaddrs a)) expression = some value)
    (hshape : shapeOfHOLExact value = shape)
    (hdisjoint : ∀ name sh offset,
      (source.globals.lookup name).isSome = true ∧
        context.globals.lookup name = some (sh, offset) →
      ∀ address, addresses (target.topAddr - offset) (sizeOfShapeHOL sh) address →
        ¬ addresses (target.topAddr - panBytesInWord width *
          BitVec.ofNat width (sizeOfShapeHOL shape + tailSize) - context.globalsSize)
          (sizeOfShapeHOL shape + tailSize) address)
    (hstore : @panMemStoresHOL width _
      (target.topAddr - (context.globalsSize + panBytesInWord width *
        BitVec.ofNat width (sizeOfShapeHOL shape))) (flattenHOL value) target.memaddrs
      (fun a => Classical.propDecidable (target.memaddrs a)) target.memory = some memory) :
    ∀ name oldValue, source.globals.lookup name = some oldValue →
      ∃ offset, context.globals.lookup name = some (shapeOfHOLExact oldValue, offset) ∧
        @memLoadHOLExact width _ (shapeOfHOLExact oldValue) (target.topAddr - offset)
          target.memaddrs (fun a => Classical.propDecidable (target.memaddrs a))
          memory [] = some oldValue := by
  classical
  have hcleared :=
    (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context source target true).2 hrel
  have hwf := PanGlobalsInitGlobalsShape.evalStateRelIsWfShapeHOL
    source.emptyLocalsHOLFinite target.emptyLocalsHOLFinite expression value true context
    ⟨heval, hcleared, by intro name bound h; simp [emptyLocalsHOLFinite] at h⟩
  have hlength : (flattenHOL value).length = sizeOfShapeHOL shape := by
    rw [flattenHOL_length_eq_sizeOfShapeHOL value hwf, hshape]
  let freeBase := target.topAddr - panBytesInWord width *
    BitVec.ofNat width (sizeOfShapeHOL shape + tailSize) - context.globalsSize
  let headBase := target.topAddr - (context.globalsSize + panBytesInWord width *
    BitVec.ofNat width (sizeOfShapeHOL shape))
  have hbase : freeBase + panBytesInWord width * BitVec.ofNat width tailSize = headBase := by
    exact PanGlobalsInitGlobalsRanges.headAllocationBase
      target.topAddr context.globalsSize (sizeOfShapeHOL shape) tailSize
  have hfootprint : ∀ address, addresses headBase (flattenHOL value).length address →
      addresses freeBase (sizeOfShapeHOL shape + tailSize) address := by
    intro address h
    rw [hlength, ← hbase] at h
    have h' := (PanGlobalsMemStores.addresses_add tailSize (sizeOfShapeHOL shape)
      freeBase address).mpr (Or.inr (by simpa only [panBytesInWord] using h))
    simpa only [Nat.add_comm] using h'
  obtain ⟨_, _, _, _, _, _, _, _, hglobals, _⟩ := hrel
  intro name oldValue hlookup
  obtain ⟨offset, hcontext, holdWf, hload, _, _⟩ := hglobals name oldValue hlookup
  refine ⟨offset, hcontext, ?_⟩
  have hpreserved := PanGlobalsMemStores.memStoresLoadDisjointHOL.1
    (shapeOfHOLExact oldValue) headBase (flattenHOL value) target.memaddrs
    target.memory memory [] (target.topAddr - offset)
    ⟨hstore, rfl, holdWf, ?_⟩
  · exact hpreserved.trans hload
  · intro address hold hhead
    exact hdisjoint name (shapeOfHOLExact oldValue) offset
      ⟨by rw [hlookup]; rfl, hcontext⟩ address hold (hfootprint address hhead)

end Flapjack.PanGlobalsInitGlobalsOldLoads
