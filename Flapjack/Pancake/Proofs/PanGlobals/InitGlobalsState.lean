import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsStore
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsReload
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsOldLoads
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsContext
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsMapDisjoint

namespace Flapjack.PanGlobalsInitGlobalsState
open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Full initializer head allocation certificate assembled from the original
initializer hypotheses. This is a Flapjack composition step, not a separately
named HOL declaration. It derives store success and all state_rel conjuncts;
no target execution or post-state relation is assumed. -/
theorem initializerHeadStateRel {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (name : MlS)
    (expression : ExpHOL width) (value : ValueHOL width) (shape : ShapeHOL) (tailSize : Nat)
    (hrel : panGlobalsStateRelHOLExact false context source target)
    (heval : @evalHOLFinite width σ _ source.emptyLocalsHOLFinite
      (fun a => Classical.propDecidable (source.memaddrs a)) expression = some value)
    (hshape : shapeOfHOLExact value = shape)
    (hbound : (panBytesInWord width).toNat * (sizeOfShapeHOL shape + tailSize) < 2 ^ width)
    (haligned : panGlobalsByteAlignedHOL context.globalsSize)
    (hcodeEmpty : source.code = HolFiniteMapExact.empty)
    (hcoverage : ∀ address,
      addresses (target.topAddr - panBytesInWord width *
        BitVec.ofNat width (sizeOfShapeHOL shape + tailSize) - context.globalsSize)
        (sizeOfShapeHOL shape + tailSize) address → target.memaddrs address)
    (hexcluded : ∀ address, source.memaddrs address →
      ¬ addresses (target.topAddr - panBytesInWord width *
        BitVec.ofNat width (sizeOfShapeHOL shape + tailSize) - context.globalsSize)
        (sizeOfShapeHOL shape + tailSize) address)
    (hdisjoint : ∀ name sh offset,
      (source.globals.lookup name).isSome = true ∧
        context.globals.lookup name = some (sh, offset) →
      ∀ address, addresses (target.topAddr - offset) (sizeOfShapeHOL sh) address →
        ¬ addresses (target.topAddr - panBytesInWord width *
          BitVec.ofNat width (sizeOfShapeHOL shape + tailSize) - context.globalsSize)
          (sizeOfShapeHOL shape + tailSize) address)
    :
    let offset := context.globalsSize + panBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL shape)
    let nextContext := { context with globals := context.globals.updateEq (name, (shape, offset)), globalsSize := offset }
    ∃ memory,
      @panMemStoresHOL width _ (target.topAddr - offset) (flattenHOL value) target.memaddrs
        (fun a => Classical.propDecidable (target.memaddrs a)) target.memory = some memory ∧
      panGlobalsStateRelHOLExact false nextContext (setGlobalHOLFinite name value source)
        { target with memory := memory } := by
  classical
  dsimp only
  let offset := context.globalsSize + panBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL shape)
  have hcopy := hrel
  obtain ⟨htop, _, hbase, hbe, hesh, hclock, hsstruct, htstruct, hglobals, _, hsub,
    hshared, hmemory, hffi, _, _, htopOut, htopAligned, hwidth⟩ := hcopy
  have hcleared := (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context source target true).2 hrel
  have hwf := PanGlobalsInitGlobalsShape.evalStateRelIsWfShapeHOL
    source.emptyLocalsHOLFinite target.emptyLocalsHOLFinite expression value true context
    ⟨heval, hcleared, by intro key bound h; simp [emptyLocalsHOLFinite] at h⟩
  have hlength : (flattenHOL value).length = sizeOfShapeHOL shape := by
    rw [flattenHOL_length_eq_sizeOfShapeHOL value hwf, hshape]
  obtain ⟨_, hhead, _⟩ := PanGlobalsInitGlobalsRanges.allocationPartition
    target.topAddr context.globalsSize (sizeOfShapeHOL shape) tailSize hwidth hbound
  obtain ⟨memory, hstore, hagree⟩ := PanGlobalsInitGlobalsStore.initGlobalStorePreservesSourceMemory
    (target.topAddr - offset) (flattenHOL value) source.memaddrs target.memaddrs
    (addresses (target.topAddr - panBytesInWord width *
      BitVec.ofNat width (sizeOfShapeHOL shape + tailSize) - context.globalsSize)
      (sizeOfShapeHOL shape + tailSize)) source.memory target.memory
    (by simpa only [hlength] using hhead) hcoverage hexcluded hmemory
  obtain ⟨_hshapeWf, hnewLoad⟩ := PanGlobalsInitGlobalsReload.initializerHeadReload
    source target context expression value shape tailSize memory hrel heval hshape hbound hstore
  have holdLoads := PanGlobalsInitGlobalsOldLoads.initializerOldGlobalLoads
    source target context expression value shape tailSize memory hrel heval hshape hdisjoint hstore
  obtain ⟨hcontextWf, hoffset, _⟩ := PanGlobalsInitGlobalsContext.initializerContext
    source target context name expression value shape hrel heval hshape haligned
  have hmaps := PanGlobalsInitGlobalsMapDisjoint.initializerMapsDisjoint
    source target context name shape value tailSize hrel hdisjoint
  refine ⟨memory, hstore, ?_⟩
  change panGlobalsStateRelHOLExact false _ _ _
  refine ⟨htop, by simp, hbase, hbe, hesh, hclock, hsstruct, htstruct, ?_,
    hcontextWf, hsub, hshared, hagree, hffi, ?_, hmaps, htopOut, htopAligned, hwidth⟩
  · intro key v hlookup
    change (source.globals.update (name, value)).lookup key = some v at hlookup
    by_cases hkey : key = name
    · subst key
      have hv : value = v := by
        simpa [HolFiniteMapExact.lookup_update_pointwise, FUPDATE] using hlookup
      subst v
      refine ⟨offset, ?_, hwf, ?_, ?_, hoffset⟩
      · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hshape, offset]
      · simpa only [hshape] using hnewLoad
      · intro address hs ha
        apply hexcluded address hs
        exact hhead address (by simpa only [hshape] using ha)
    · have hold : source.globals.lookup key = some v := by
        simpa [HolFiniteMapExact.lookup_update_pointwise, FUPDATE, hkey, Ne.symm hkey] using hlookup
      obtain ⟨address, hc, hw, _, he, hal⟩ := hglobals key v hold
      obtain ⟨address', hc', hl⟩ := holdLoads key v hold
      have ha : address' = address := by
        rw [hc] at hc'
        exact (Prod.mk.inj (Option.some.inj hc')).2.symm
      subst address'
      refine ⟨address, ?_, hw, hl, he, hal⟩
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hkey] using hc
  · intro function parameters program returnShape hlookup
    change source.code.lookup function = some (parameters, program, returnShape) at hlookup
    simp [hcodeEmpty] at hlookup

end Flapjack.PanGlobalsInitGlobalsState
