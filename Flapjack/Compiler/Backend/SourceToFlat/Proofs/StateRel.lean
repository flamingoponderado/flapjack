import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRel
import Flapjack.Misc.ListLookupRel

/-! Source-to-flat store and state relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.SemanticPrimitivesHOL

namespace StateRelPort

/-- Roundtrip for the global carrier's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env :=
  GlobalEnv.holFmapAsFiniteSupportWitness env

end StateRelPort

/-- Relate source and flat store entries pointwise through the value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "sv_rel"
  (fmap_as_finite_support := [c, tys])]
inductive StoreValueRel (genv : GlobalEnv) : StoreValue SemanticPrimitivesHOL.Value →
    StoreValue FlatSem.Value → Prop where
  | refv {v v'} (related : ValueRel genv v v') : StoreValueRel genv (.refv v) (.refv v')
  | w8array (bytes) : StoreValueRel genv (.w8array bytes) (.w8array bytes)
  | varray {vs vs'} (related : List.Forall₂ (ValueRel genv) vs vs') :
      StoreValueRel genv (.varray vs) (.varray vs')
  | thunk (mode) {v v'} (related : ValueRel genv v v') :
      StoreValueRel genv (.thunk mode v) (.thunk mode v')

/-- Store-entry compatibility is preserved by related entries. This is
Flapjack infrastructure over the factored value relation. -/
theorem storeValueSameType_related (genv : GlobalEnv)
    (old new : StoreValue SemanticPrimitivesHOL.Value) (flatOld flatNew : StoreValue FlatSem.Value)
    (oldRel : StoreValueRel genv old flatOld) (newRel : StoreValueRel genv new flatNew) :
    storeValueSameType old new = storeValueSameType flatOld flatNew := by
  cases oldRel with
  | refv related => cases newRel <;> rfl
  | w8array bytes => cases newRel <;> rfl
  | varray related => cases newRel <;> rfl
  | thunk mode related => cases mode <;> cases newRel <;> rfl

/-- Relate evaluator states; the flat store's reserved first entry is arbitrary. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "s_rel"
  (fmap_as_finite_support := [c, tys])]
inductive StateRel {C F : Type} (genv : GlobalEnv) :
    SemanticPrimitivesHOL.State F → FlatSem.State C F → Prop where
  | intro (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
      (nonempty : flat.refs ≠ [])
      (refs : List.Forall₂ (StoreValueRel genv) source.refs flat.refs.tail)
      (clock : source.clock = flat.clock)
      (ffi : source.ffi = flat.ffi) : StateRel genv source flat

/-- Unfold the state relation into the four conditions used by its rule. -/
theorem stateRel_iff {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) :
    StateRel genv source flat ↔
      flat.refs ≠ [] ∧ List.Forall₂ (StoreValueRel genv) source.refs flat.refs.tail ∧
        source.clock = flat.clock ∧ source.ffi = flat.ffi := by
  constructor
  · intro related
    cases related with
    | intro nonempty refs clock ffi => exact ⟨nonempty, refs, clock, ffi⟩
  · rintro ⟨nonempty, refs, clock, ffi⟩
    exact .intro source flat nonempty refs clock ffi

/-- Source and flat store lookups agree at the original one-slot offset. This
is infrastructure over the factored source-to-flat value relation. -/
theorem stateRel_lookup {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (related : StateRel genv source flat) (n : Nat) :
    Flapjack.optionRel (StoreValueRel genv) (storeLookup n source.refs) (storeLookup (n + 1) flat.refs) := by
  cases related with
  | intro nonempty refs _ _ =>
    obtain ⟨entry, rest, hflat⟩ := List.exists_cons_of_ne_nil nonempty
    have relatedRest : List.Forall₂ (StoreValueRel genv) source.refs rest := by simpa [hflat] using refs
    simpa [storeLookup, hflat, Nat.add_comm] using forall₂_lookupRel relatedRest n

/-- A source reference lookup has a related flat reference one slot later.
This is infrastructure over the factored source-to-flat value relation. -/
theorem stateRel_ref_lookup {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (related : StateRel genv source flat) (n : Nat) (value : SemanticPrimitivesHOL.Value)
    (lookup : storeLookup n source.refs = some (.refv value)) :
    ∃ value', storeLookup (n + 1) flat.refs = some (.refv value') ∧ ValueRel genv value value' := by
  cases related with
  | intro nonempty refs _ _ =>
    obtain ⟨entry, rest, hflat⟩ := List.exists_cons_of_ne_nil nonempty
    have relatedRest : List.Forall₂ (StoreValueRel genv) source.refs rest := by simpa [hflat] using refs
    obtain ⟨found, hfound, hrel⟩ := forall₂_lookup relatedRest n (.refv value) lookup
    cases hrel with
    | refv hvalue =>
      refine ⟨_, ?_, hvalue⟩
      simpa [storeLookup, hflat, Nat.add_comm] using hfound

/-- A source byte-array lookup finds the same bytes one slot later in the
flat store. This is infrastructure over the factored state relation. -/
theorem stateRel_byteArray_lookup {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (related : StateRel genv source flat) (n : Nat) (bytes : List (BitVec 8))
    (lookup : storeLookup n source.refs = some (.w8array bytes)) :
    storeLookup (n + 1) flat.refs = some (.w8array bytes) := by
  cases related with
  | intro nonempty refs _ _ =>
    obtain ⟨entry, rest, hflat⟩ := List.exists_cons_of_ne_nil nonempty
    have relatedRest : List.Forall₂ (StoreValueRel genv) source.refs rest := by simpa [hflat] using refs
    obtain ⟨found, hfound, hrel⟩ := forall₂_lookup relatedRest n (.w8array bytes) lookup
    cases hrel with
    | w8array bytes =>
      simpa [storeLookup, hflat, Nat.add_comm] using hfound

/-- A source value-array lookup has related elements at the shifted flat
address. This is infrastructure over the factored state relation. -/
theorem stateRel_array_lookup {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (related : StateRel genv source flat) (n : Nat) (values : List SemanticPrimitivesHOL.Value)
    (lookup : storeLookup n source.refs = some (.varray values)) :
    ∃ flatValues, storeLookup (n + 1) flat.refs = some (.varray flatValues) ∧
      List.Forall₂ (ValueRel genv) values flatValues := by
  cases related with
  | intro nonempty refs _ _ =>
    obtain ⟨entry, rest, hflat⟩ := List.exists_cons_of_ne_nil nonempty
    have relatedRest : List.Forall₂ (StoreValueRel genv) source.refs rest := by simpa [hflat] using refs
    obtain ⟨found, hfound, hrel⟩ := forall₂_lookup relatedRest n (.varray values) lookup
    cases hrel with
    | varray hvalues =>
      refine ⟨_, ?_, hvalues⟩
      simpa [storeLookup, hflat, Nat.add_comm] using hfound

end Flapjack.Compiler.Backend.SourceToFlat
