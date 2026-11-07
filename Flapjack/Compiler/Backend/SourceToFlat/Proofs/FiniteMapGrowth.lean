import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalWeakening

/-! Finite-map growth lemmas for source-to-flat global environments. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Lookup characterization of finite-map submap, over the canonical
finite-support carrier. -/
def finiteSubmap {α β : Type} (f g : HolFiniteMapExact α β) : Prop :=
  ∀ key value, f.lookup key = some value → g.lookup key = some value

/-- Canonical finite-map update using HOL equality. -/
noncomputable def finiteUpdate {α β : Type} (f : HolFiniteMapExact α β) (key : α) (value : β) :
    HolFiniteMapExact α β := by
  classical
  exact f.updateEq (key, value)

/-- Canonical finite-map domain subtraction using HOL equality. -/
noncomputable def finiteErase {α β : Type} (f : HolFiniteMapExact α β) (key : α) :
    HolFiniteMapExact α β := by
  classical
  exact f.eraseEq key

/-- Broad lookup and support codec used by the canonical parameter witnesses. -/
private def maptoBroadlookup {α β : Type} (map : HolFiniteMapExact α β) : α → Option β := map.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_finiteSubmap_update_fresh_f {α β : Type}
    (f : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

theorem holFmapAsFiniteSupportParamWitness_finiteSubmap_update_fresh_g {α β : Type}
    (g : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by
  cases g
  rfl

theorem holFmapAsFiniteSupportParamWitness_finiteSubmap_update_f {α β : Type}
    (f : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

theorem holFmapAsFiniteSupportParamWitness_finiteSubmap_update_g {α β : Type}
    (g : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by
  cases g
  rfl

/-- Updating a fresh key preserves the earlier map when the updated map is a
submap. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "submap_distinct_fupdate_flookup"
  (fmap_as_finite_support_parameters := [f, g])]
theorem finiteSubmap_update_fresh {α β : Type} (key : α) (f : HolFiniteMapExact α β) (value : β) (g : HolFiniteMapExact α β)
    (fresh : f.lookup key = none) :
    finiteSubmap (finiteUpdate f key value) g ↔ g.lookup key = some value ∧ finiteSubmap f g := by
  classical
  constructor
  · intro h
    constructor
    · apply h key value
      simp [finiteUpdate, FUPDATE_HOL]
    · intro k v lookup
      have different : k ≠ key := by
        intro eq
        subst k
        rw [fresh] at lookup
        contradiction
      apply h k v
      simpa [finiteUpdate, FUPDATE_HOL, different] using lookup
  · rintro ⟨atKey, old⟩ k v lookup
    by_cases eq : k = key
    · subst k
      simp [finiteUpdate, FUPDATE_HOL] at lookup
      subst v
      exact atKey
    · apply old k v
      simpa [finiteUpdate, FUPDATE_HOL, eq] using lookup

/-- Updating a key replaces its prior binding; all other bindings must already
be preserved. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "submap_fupdate_flookup"
  (fmap_as_finite_support_parameters := [f, g])]
theorem finiteSubmap_update {α β : Type} (f : HolFiniteMapExact α β) (key : α) (value : β) (g : HolFiniteMapExact α β) :
    finiteSubmap (finiteUpdate f key value) g ↔
      g.lookup key = some value ∧ finiteSubmap (finiteErase f key) g := by
  classical
  constructor
  · intro h
    constructor
    · apply h key value
      simp [finiteUpdate, FUPDATE_HOL]
    · intro k v lookup
      by_cases eq : k = key
      · subst k
        simp [finiteErase, FDOMSUB_HOL] at lookup
      · apply h k v
        simpa [finiteUpdate, finiteErase, FUPDATE_HOL, FDOMSUB_HOL, eq] using lookup
  · rintro ⟨atKey, old⟩ k v lookup
    by_cases eq : k = key
    · subst k
      simp [finiteUpdate, FUPDATE_HOL] at lookup
      subst v
      exact atKey
    · apply old k v
      simpa [finiteUpdate, finiteErase, FUPDATE_HOL, FDOMSUB_HOL, eq] using lookup

/-- The original subglobal and submap hypotheses imply the concrete growth
condition used by the factored source-to-flat simulation. -/
theorem GlobalGrowth.ofSubmaps (old new : GlobalEnv) (slots : subglobals old.v new.v)
    (constructors : finiteSubmap old.c new.c) (types : finiteSubmap old.tys new.tys) :
    GlobalGrowth old new :=
  GlobalGrowth.ofSubglobals old new slots constructors types

end Flapjack.Compiler.Backend.SourceToFlat
