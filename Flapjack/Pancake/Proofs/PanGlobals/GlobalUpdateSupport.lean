import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

namespace Flapjack.PanGlobalsGlobalUpdateSupport

/-- Flapjack infrastructure for the original Assign proof's FLOOKUP_UPDATE
reasoning: replacing an existing global preserves lookup support at every key.
This synthesized statement has no single HOL declaration. -/
theorem lookupSupport_update {width : Nat} [NeZero width]
    (globals : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS (ValueHOL width))
    (name : Flapjack.Pancake.PanLang.MlS) (value : ValueHOL width)
    (hexists : globals.lookup name ≠ none)
    (key : Flapjack.Pancake.PanLang.MlS) :
    (globals.update (name, value)).lookup key ≠ none ↔ globals.lookup key ≠ none := by
  classical
  rw [HolFiniteMapExact.lookup_update_pointwise]
  by_cases hkey : key = name
  · subst key
    simp [hexists]
  · simp [hkey]

/-- Flapjack infrastructure for original Assign575-590. The address-separation
relation observes global presence, so an existing-key replacement preserves it
for arbitrary values, including structured values. No scalar or shape premise
is needed, and no alternate state relation is introduced. -/
theorem disjointGlobals_update {width : Nat} [NeZero width]
    (topAddress : BitVec width)
    (context : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS
      (Flapjack.Pancake.PanLang.ShapeHOL × BitVec width))
    (globals : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS (ValueHOL width))
    (name : Flapjack.Pancake.PanLang.MlS) (value : ValueHOL width)
    (hexists : globals.lookup name ≠ none)
    (hdisjoint : disjointGlobalsHOLExact topAddress context globals) :
    disjointGlobalsHOLExact topAddress context (globals.update (name, value)) := by
  intro key key' shape address shape' address' hne hkey hkey' hc hc' slot
  exact hdisjoint key key' shape address shape' address' hne
    ((lookupSupport_update globals name value hexists key).mp hkey)
    ((lookupSupport_update globals name value hexists key').mp hkey') hc hc' slot

/-- Flapjack structural certificate for the original Global Assign update.
The existing exact evaluator shape-map theorem is reused; the memory simulation
still has to prove its separate load and domain obligations. -/
theorem globalUpdate_invariants {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (topAddress : BitVec width)
    (context : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS
      (Flapjack.Pancake.PanLang.ShapeHOL × BitVec width))
    (name : Flapjack.Pancake.PanLang.MlS) (oldValue value : ValueHOL width)
    (hlookup : source.globals.lookup name = some oldValue)
    (hshape : shapeOfHOLExact value = shapeOfHOLExact oldValue)
    (hdisjoint : disjointGlobalsHOLExact topAddress context source.globals) :
    (∀ key, (PanSemStateFiniteExact.setGlobalHOLFinite name value source).globals.lookup key ≠ none ↔
      source.globals.lookup key ≠ none) ∧
    disjointGlobalsHOLExact topAddress context
      (PanSemStateFiniteExact.setGlobalHOLFinite name value source).globals ∧
    PanSemStateFiniteExact.globalsShapes
      (PanSemStateFiniteExact.setGlobalHOLFinite name value source) =
      PanSemStateFiniteExact.globalsShapes source := by
  have hexists : source.globals.lookup name ≠ none := by simp [hlookup]
  refine ⟨lookupSupport_update source.globals name value hexists,
    disjointGlobals_update topAddress context source.globals name value hexists hdisjoint, ?_⟩
  apply PanSemStateFiniteExact.globalsShapes_setGlobalHOLFinite_of_shape
  simp [hlookup, hshape]

end Flapjack.PanGlobalsGlobalUpdateSupport
