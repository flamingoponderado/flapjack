import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsShape
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsAlignment
import Flapjack.Pancake.Proofs.PanGlobals.GlobalBlockAlignment

namespace Flapjack.PanGlobalsInitGlobalsContext
open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

/-- Flapjack arithmetic support for original initializer byte_aligned_add.
Derive addition from the accepted aligned subtraction theorem; this is not
a new port of an external HOL library declaration. -/
theorem byteAlignedAdd {width : Nat} [NeZero width]
    (a b : BitVec width) (hwidth : goodDimindex width)
    (ha : panGlobalsByteAlignedHOL a) (hb : panGlobalsByteAlignedHOL b) :
    panGlobalsByteAlignedHOL (a + b) := by
  have hzero : panGlobalsByteAlignedHOL (0 : BitVec width) := by
    simp [panGlobalsByteAlignedHOL, panByteAlignHOL]
  have hneg := PanGlobalsGlobalBlockAlignment.byteAligned_sub 0 b hwidth hzero hb
  have hsum := PanGlobalsGlobalBlockAlignment.byteAligned_sub a (0 - b) hwidth ha hneg
  have heq : a - (0 - b) = a + b := by
    change a - -b = a + b
    exact BitVec.sub_neg
  rw [heq] at hsum
  exact hsum

/-- Flapjack-specific initializer next-context certificate. Original source
evaluation and state_rel derive the new shape's validity; original globals_size
alignment and state_rel dimensions/top alignment derive the next offset and
head block alignment. Exact updateEq preserves all other shape entries and
permits name replacement. No store/run, fresh-name or new alignment premise;
no independently named HOL declaration. -/
theorem initializerContext {width : Nat} {σ : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width σ)
    (context : PanGlobalsContextExact width) (name : MlS)
    (expression : ExpHOL width) (value : ValueHOL width) (shape : ShapeHOL)
    (hrel : panGlobalsStateRelHOLExact false context source target)
    (heval : @evalHOLFinite width σ _ source.emptyLocalsHOLFinite
      (fun a => Classical.propDecidable (source.memaddrs a)) expression = some value)
    (hshape : shapeOfHOLExact value = shape)
    (haligned : panGlobalsByteAlignedHOL context.globalsSize) :
    let offset := context.globalsSize + panBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL shape)
    (∀ key sh address,
      (context.globals.updateEq (name, (shape, offset))).lookup key = some (sh, address) →
      isWfShapeNilHOL sh = true) ∧
    panGlobalsByteAlignedHOL offset ∧ panGlobalsByteAlignedHOL (target.topAddr - offset) := by
  classical
  have hcleared :=
    (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context source target true).2 hrel
  have hnewWf := PanGlobalsInitGlobalsShape.evalStateRelIsWfShapeHOL
    source.emptyLocalsHOLFinite target.emptyLocalsHOLFinite expression value true context
    ⟨heval, hcleared, by intro key bound h; simp [emptyLocalsHOLFinite] at h⟩
  rw [hshape] at hnewWf
  obtain ⟨_, _, _, _, _, _, _, _, _, hcontextWf, _, _, _, _, _, _, _, htop, hwidth⟩ := hrel
  have hstride := PanGlobalsInitGlobalsAlignment.byteAlignedBytesInWordMulHOL
    (BitVec.ofNat width (sizeOfShapeHOL shape)) hwidth
  have hoffset := byteAlignedAdd context.globalsSize
    (panBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL shape)) hwidth haligned hstride
  refine ⟨?_, hoffset, PanGlobalsGlobalBlockAlignment.byteAligned_sub _ _ hwidth htop hoffset⟩
  intro key sh address hlookup
  by_cases hkey : key = name
  · subst key
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hlookup
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hlookup)
    exact hnewWf
  · have hold : context.globals.lookup key = some (sh, address) := by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hkey] using hlookup
    exact hcontextWf key sh address hold

end Flapjack.PanGlobalsInitGlobalsContext
