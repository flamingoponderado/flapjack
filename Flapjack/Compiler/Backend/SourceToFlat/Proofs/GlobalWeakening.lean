module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
public import Flapjack.FiniteMap.CardinalityExact
public import Flapjack.FiniteMap.MapKeys
public import Flapjack.FiniteMap.SubmapExact

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Weakening the factored source-to-flat relations across global growth. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Earlier initialized global slots retain their values, and the list may
only grow. The optional lookup has the same meaning as HOL's `EL` under the
explicit bounds premise. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "subglobals_def"]
def subglobals {α : Type} (old new : List (Option α)) : Prop :=
  old.length ≤ new.length ∧
    ∀ n, n < old.length ∧ (old[n]?.getD none).isSome → old[n]?.getD none = new[n]?.getD none

/-- Observation-based growth agrees with the bounded slot condition used in
`subglobals`. This is Flapjack infrastructure for the factored relation. -/
theorem subglobals_iff_observations {α : Type} (old new : List (Option α)) :
    subglobals old new ↔ old.length ≤ new.length ∧
      ∀ (n : Nat) (value : α), old[n]?.getD none = some value → new[n]?.getD none = some value := by
  constructor
  · rintro ⟨length, preserves⟩
    refine ⟨length, ?_⟩
    intro n value slot
    have bound : n < old.length := by
      by_contra notBound
      simp [List.getElem?_eq_none (Nat.le_of_not_gt notBound)] at slot
    have valid : (old[n]?.getD none).isSome := by simp [slot]
    exact (preserves n ⟨bound, valid⟩).symm.trans slot
  · rintro ⟨length, preserves⟩
    refine ⟨length, ?_⟩
    intro n ⟨_, valid⟩
    cases slot : old[n]?.getD none with
    | none => simp [slot] at valid
    | some value =>
      have next := preserves n value slot
      exact next.symm

/-- A global list preserves itself. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "subglobals_refl"]
theorem subglobals_refl {α : Type} (globals : List (Option α)) : subglobals globals globals :=
  (subglobals_iff_observations globals globals).mpr ⟨Nat.le_refl _, fun _ _ h => h⟩

/-- Slot preservation composes across successive global lists. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "subglobals_trans"]
theorem subglobals_trans {α : Type} (first middle last : List (Option α))
    (related : subglobals first middle ∧ subglobals middle last) : subglobals first last := by
  obtain ⟨len1, values1⟩ := (subglobals_iff_observations first middle).mp related.1
  obtain ⟨len2, values2⟩ := (subglobals_iff_observations middle last).mp related.2
  exact (subglobals_iff_observations first last).mpr
    ⟨Nat.le_trans len1 len2, fun n value slot => values2 n value (values1 n value slot)⟩

/-- A list of uninitialized slots is a subglobal list exactly when the target
has room for those slots. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "subglobals_NONE"]
theorem subglobals_none {α : Type} (n : Nat) (globals : List (Option α)) :
    subglobals (List.replicate n none) globals ↔ n ≤ globals.length := by
  rw [subglobals_iff_observations]
  simp [List.getElem?_replicate]
  intro _ i value slot
  split at slot <;> simp_all

/-- Allocating uninitialized global slots preserves all existing globals. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "subglobals_add_NONE"]
theorem subglobals_add_none {α : Type} (globals : List (Option α)) (n : Nat) :
    subglobals globals (globals ++ List.replicate n none) := by
  apply (subglobals_iff_observations _ _).mpr
  refine ⟨by simp, ?_⟩
  intro i value slot
  have bound : i < globals.length := by
    by_contra notBound
    simp [List.getElem?_eq_none (Nat.le_of_not_gt notBound)] at slot
  simpa [List.getElem?_append_left bound] using slot

/-- A common prefix can be removed from the subglobal relation; a common
suffix can also be removed when the differing parts have equal lengths. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "subglobals_refl_append"]
theorem subglobals_refl_append {α : Type} (g1 g2 g3 : List (Option α)) :
    (subglobals (g1 ++ g2) (g1 ++ g3) ↔ subglobals g2 g3) ∧
    (g2.length = g3.length → (subglobals (g2 ++ g1) (g3 ++ g1) ↔ subglobals g2 g3)) := by
  constructor
  · induction g1 with
    | nil => simp
    | cons head tail ih =>
      change subglobals (head :: (tail ++ g2)) (head :: (tail ++ g3)) ↔ subglobals g2 g3
      rw [← ih]
      rw [subglobals_iff_observations, subglobals_iff_observations]
      constructor
      · rintro ⟨length, values⟩
        refine ⟨by simpa using length, ?_⟩
        intro n value slot
        simpa using values (n + 1) value (by simpa using slot)
      · rintro ⟨length, values⟩
        refine ⟨by simpa using length, ?_⟩
        intro n value slot
        cases n with
        | zero => simpa using slot
        | succ n => simpa using values n value (by simpa using slot)
  · intro sameLength
    rw [subglobals_iff_observations, subglobals_iff_observations]
    constructor
    · rintro ⟨_, values⟩
      refine ⟨by omega, ?_⟩
      intro n value slot
      have bound : n < g2.length := by
        by_contra notBound
        simp [List.getElem?_eq_none (Nat.le_of_not_gt notBound)] at slot
      have newBound : n < g3.length := by omega
      have preserved := values n value (by simpa [List.getElem?_append_left bound] using slot)
      simpa [List.getElem?_append_left newBound] using preserved
    · rintro ⟨_, values⟩
      refine ⟨by simp [sameLength], ?_⟩
      intro n value slot
      by_cases bound : n < g2.length
      · have newBound : n < g3.length := by omega
        have original : g2[n]?.getD none = some value := by
          simpa [List.getElem?_append_left bound] using slot
        simpa [List.getElem?_append_left newBound] using values n value original
      · have newBound : ¬ n < g3.length := by omega
        simpa [List.getElem?_append, bound, newBound, sameLength] using slot

/-- Filling a contiguous block of blank slots preserves all previously
initialized slots, including those after the block. This is Flapjack
infrastructure for declaration simulation. -/
theorem subglobals_fill_none {α : Type} (pre values post : List (Option α)) :
    subglobals (pre ++ (List.replicate values.length none ++ post))
      (pre ++ (values ++ post)) := by
  apply (subglobals_refl_append pre _ _).1.mpr
  apply ((subglobals_refl_append post _ _).2 (by simp)).mpr
  exact (subglobals_none values.length values).mpr (Nat.le_refl _)

/-- Existing global slots and constructor/type lookups survive growth. This
Flapjack relation exposes the observations needed by the factored relations;
the slot component agrees with `subglobals` above. -/
structure GlobalGrowth (old new : GlobalEnv) : Prop where
  length : old.v.length ≤ new.v.length
  values : ∀ (n : Nat) (v : FlatSem.Value), old.v[n]?.getD none = some v → new.v[n]?.getD none = some v
  constructors : ∀ key value, old.c.lookup key = some value → new.c.lookup key = some value
  types : ∀ key value, old.tys.lookup key = some value → new.tys.lookup key = some value

/-- Related values remain related when existing globals and map entries are
preserved. This is infrastructure over the unreviewed factored relations. -/
theorem valueRel_growth (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (source : Value) (flat : FlatSem.Value) (related : ValueRel old source flat) :
    ValueRel new source flat := by
  induction related using ValueRel.rec
    (motive_2 := fun xs ys _ => ValueListRel new xs ys)
    (motive_3 := fun env xs _ => EnvRel new env xs)
    (motive_4 := fun map shadows env _ => GlobalEnvInv new map shadows env)
    (motive_5 := fun map id v _ => GlobalLookupRel new map id v)
  case literal lit => exact .literal new lit
  case constructor stamp ctor sourceValues flatValues related lookup ih =>
    exact .constructor new stamp ctor sourceValues flatValues ih (growth.constructors _ _ lookup)
  case tuple sourceValues flatValues related ih => exact .tuple new sourceValues flatValues ih
  case closure compMap env sourceLocal name body flatLocal t ts localRel globalInv length localIH globalIH =>
    exact .closure new compMap env sourceLocal name body flatLocal t ts localIH globalIH length
  case recclosure compMap env sourceLocal funs name flatLocal t ts localRel globalInv length localIH globalIH =>
    exact .recclosure new compMap env sourceLocal funs name flatLocal t ts localIH globalIH length
  case topRecclosure compMap env funs flatEnv name arg body newVars t1 t2 names globalInv empty find closures globalIH =>
    apply ValueRel.topRecclosure new compMap env funs flatEnv name arg body newVars t1 t2 names globalIH empty find
    intro x member
    obtain ⟨n, y, e, trace, t, trace', lookup, bound, found, slot⟩ := closures x member
    exact ⟨n, y, e, trace, t, trace', lookup, Nat.lt_of_lt_of_le bound growth.length, found, growth.values n _ slot⟩
  case location loc b => exact .location new loc b
  case vector sourceValues flatValues related ih => exact .vector new sourceValues flatValues ih
  case nil => exact .nil new
  case cons source flat sources flats head tail headIH tailIH => exact .cons new source flat sources flats headIH tailIH
  case empty => exact .empty new
  case bind name source env flatEnv flat hEnv hValue envIH valueIH => exact .bind new name source env flatEnv flat envIH valueIH
  case intro compMap shadowers env values constructors valuesIH =>
    apply GlobalEnvInv.intro new compMap shadowers env valuesIH
    intro id arity stamp lookup
    obtain ⟨cn, group, compiled, stampLookup, typesLookup⟩ := constructors id arity stamp lookup
    exact ⟨cn, group, compiled, growth.constructors _ _ stampLookup,
      fun tyId ctors h => growth.types _ _ (typesLookup tyId ctors h)⟩
  case intro compMap id source n flat t =>
    intro lookup bound slot related ih
    exact .intro new compMap id source n flat t lookup (Nat.lt_of_lt_of_le bound growth.length) (growth.values n _ slot) ih

/-- Construct the observation-based growth condition from `subglobals` and
pointwise finite-map extension. -/
theorem GlobalGrowth.ofSubglobals (old new : GlobalEnv)
    (slots : subglobals old.v new.v)
    (constructors : ∀ key value, old.c.lookup key = some value → new.c.lookup key = some value)
    (types : ∀ key value, old.tys.lookup key = some value → new.tys.lookup key = some value) :
    GlobalGrowth old new := by
  obtain ⟨length, values⟩ := (subglobals_iff_observations old.v new.v).mp slots
  exact ⟨length, values, constructors, types⟩

/-- The observation-based condition is exactly the subglobal condition plus
pointwise preservation of existing map entries. -/
theorem globalGrowth_iff (old new : GlobalEnv) : GlobalGrowth old new ↔
    subglobals old.v new.v ∧
    (∀ key value, old.c.lookup key = some value → new.c.lookup key = some value) ∧
    (∀ key value, old.tys.lookup key = some value → new.tys.lookup key = some value) := by
  constructor
  · intro growth
    exact ⟨(subglobals_iff_observations old.v new.v).mpr ⟨growth.length, growth.values⟩,
      growth.constructors, growth.types⟩
  · rintro ⟨slots, constructors, types⟩
    exact GlobalGrowth.ofSubglobals old new slots constructors types

/-- Growth is reflexive and composes across successive declarations. -/
theorem GlobalGrowth.refl (env : GlobalEnv) : GlobalGrowth env env :=
  ⟨Nat.le_refl _, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem GlobalGrowth.trans {first middle last : GlobalEnv}
    (h1 : GlobalGrowth first middle) (h2 : GlobalGrowth middle last) : GlobalGrowth first last :=
  ⟨Nat.le_trans h1.length h2.length,
    fun n v h => h2.values n v (h1.values n v h),
    fun key value h => h2.constructors key value (h1.constructors key value h),
    fun key value h => h2.types key value (h1.types key value h)⟩

/-- Appending new global slots preserves every existing slot. -/
theorem GlobalGrowth.append (env : GlobalEnv) (extra : List (Option FlatSem.Value)) :
    GlobalGrowth env { env with v := env.v ++ extra } := by
  refine ⟨by simp, ?_, fun _ _ h => h, fun _ _ h => h⟩
  intro n v slot
  have bound : n < env.v.length := by
    by_contra notBound
    simp [List.getElem?_eq_none (Nat.le_of_not_gt notBound)] at slot
  simpa [List.getElem?_append_left bound] using slot

/-- Global variable lookup relations survive growth. -/
theorem globalLookupRel_growth (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (map : Environment) (id : Flapjack.NamespaceHOL.Ident ModN VarN) (source : Value)
    (related : GlobalLookupRel old map id source) : GlobalLookupRel new map id source := by
  cases related with
  | intro _ _ _ n flat t lookup bound slot valueRel =>
    exact .intro new map id source n flat t lookup (Nat.lt_of_lt_of_le bound growth.length)
      (growth.values n flat slot) (valueRel_growth old new growth source flat valueRel)

/-- The global environment invariant survives growth. -/
theorem globalEnvInv_growth (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (map : Environment) (shadowers : VarN → Prop) (env : SemEnv Value)
    (related : GlobalEnvInv old map shadowers env) : GlobalEnvInv new map shadowers env := by
  cases related with
  | intro _ _ _ values constructors =>
    apply GlobalEnvInv.intro new map shadowers env
    · intro id value notShadowed lookup
      exact globalLookupRel_growth old new growth map id value (values id value notShadowed lookup)
    · intro id arity stamp lookup
      obtain ⟨cn, group, compiled, stampLookup, typesLookup⟩ := constructors id arity stamp lookup
      exact ⟨cn, group, compiled, growth.constructors _ _ stampLookup,
        fun tyId ctors h => growth.types _ _ (typesLookup tyId ctors h)⟩

/-- Local environment relations survive growth. -/
theorem envRel_growth (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (env : Flapjack.NamespaceHOL.Namespace ModN VarN Value) (locals : List (VarN × FlatSem.Value))
    (related : EnvRel old env locals) : EnvRel new env locals := by
  induction locals generalizing env with
  | nil => cases related; exact .empty new
  | cons head tail ih =>
    cases related with
    | bind name source env flatEnv flat envRel valueRel =>
      exact .bind new name source env tail flat (ih env envRel) (valueRel_growth old new growth source flat valueRel)

/-- Store entries remain related when the global environment is extended. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "sv_rel_weak"
  (fmap_as_finite_support := [c, tys])]
theorem storeValueRel_weak (old : GlobalEnv) (source : StoreValue Value)
    (flat : StoreValue FlatSem.Value) (new : GlobalEnv)
    (premises : StoreValueRel old source flat ∧ old.c.submap new.c ∧
      old.tys.submap new.tys ∧ subglobals old.v new.v) :
    StoreValueRel new source flat := by
  obtain ⟨related, constructors, types, slots⟩ := premises
  have growth := GlobalGrowth.ofSubglobals old new slots constructors types
  cases related with
  | refv rel => exact .refv (valueRel_growth old new growth _ _ rel)
  | w8array bytes => exact .w8array bytes
  | varray rel => exact .varray (rel.imp (valueRel_growth old new growth))
  | thunk mode rel => exact .thunk mode (valueRel_growth old new growth _ _ rel)

namespace StoreListWeakPort
/-- Canonical global finite-map carrier roundtrip. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end StoreListWeakPort

/-- Related values remain related under the original global-extension conditions. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_rel_weak"
  (fmap_as_finite_support := [c, tys])]
theorem valueRel_weak (old : GlobalEnv) (source : Value) (flat : FlatSem.Value)
    (new : GlobalEnv)
    (premises : ValueRel old source flat ∧ old.c.submap new.c ∧
      old.tys.submap new.tys ∧ subglobals old.v new.v) : ValueRel new source flat := by
  obtain ⟨related, constructors, types, slots⟩ := premises
  exact valueRel_growth old new (GlobalGrowth.ofSubglobals old new slots constructors types)
    source flat related

/-- Related environments remain related under global extension. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_rel_weak"
  (fmap_as_finite_support := [c, tys])]
theorem envRel_weak (old : GlobalEnv) (env : Flapjack.NamespaceHOL.Namespace ModN VarN Value)
    (locals : List (VarN × FlatSem.Value)) (new : GlobalEnv)
    (premises : EnvRel old env locals ∧ old.c.submap new.c ∧
      old.tys.submap new.tys ∧ subglobals old.v new.v) : EnvRel new env locals := by
  obtain ⟨related, constructors, types, slots⟩ := premises
  exact envRel_growth old new (GlobalGrowth.ofSubglobals old new slots constructors types)
    env locals related

/-- The global environment invariant is preserved by global extension. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "global_env_inv_weak"
  (fmap_as_finite_support := [c, tys])]
theorem globalEnvInv_weak (old : GlobalEnv) (map : Environment) (shadowers : VarN → Prop)
    (env : SemEnv Value) (new : GlobalEnv)
    (premises : GlobalEnvInv old map shadowers env ∧ old.c.submap new.c ∧
      old.tys.submap new.tys ∧ subglobals old.v new.v) : GlobalEnvInv new map shadowers env := by
  obtain ⟨related, constructors, types, slots⟩ := premises
  exact globalEnvInv_growth old new (GlobalGrowth.ofSubglobals old new slots constructors types)
    map shadowers env related

/-- Mutual weakening with unchanged constructor/type maps and growing global slots. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_rel_weakening"
  (fmap_as_finite_support := [c, tys])]
theorem valueRel_weakening :
    (∀ (old : GlobalEnv) source flat, ValueRel old source flat → ∀ new,
      old.c = new.c ∧ old.tys = new.tys ∧ subglobals old.v new.v → ValueRel new source flat) ∧
    (∀ (old : GlobalEnv) env locals, EnvRel old env locals → ∀ new,
      old.c = new.c ∧ old.tys = new.tys ∧ subglobals old.v new.v → EnvRel new env locals) ∧
    (∀ (old : GlobalEnv) map shadowers env, GlobalEnvInv old map shadowers env → ∀ new,
      old.c = new.c ∧ old.tys = new.tys ∧ subglobals old.v new.v →
        GlobalEnvInv new map shadowers env) := by
  refine ⟨?_, ?_, ?_⟩
  · intro old source flat related new ⟨constructors, types, slots⟩
    exact valueRel_weak old source flat new
      ⟨related, by simp [← constructors, HolFiniteMapExact.submap], by simp [← types, HolFiniteMapExact.submap], slots⟩
  · intro old env locals related new ⟨constructors, types, slots⟩
    exact envRel_weak old env locals new
      ⟨related, by simp [← constructors, HolFiniteMapExact.submap], by simp [← types, HolFiniteMapExact.submap], slots⟩
  · intro old map shadowers env related new ⟨constructors, types, slots⟩
    exact globalEnvInv_weak old map shadowers env new
      ⟨related, by simp [← constructors, HolFiniteMapExact.submap], by simp [← types, HolFiniteMapExact.submap], slots⟩

/-- Mutual value, local-environment, and global-environment weakening when
the value slots agree and the constructor/type maps grow. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "v_rel_weakening2"
  (fmap_as_finite_support := [c, tys])]
theorem valueRel_weakening2 {A B C : Type}
    (new : GlobalEnv) :
    (∀ old source flat, ValueRel old source flat → ∀ (_unused : A),
      old.c.submap new.c ∧ old.tys.submap new.tys ∧ old.v = new.v →
        ValueRel new source flat) ∧
    (∀ old env locals, EnvRel old env locals → ∀ (_unused : B),
      old.c.submap new.c ∧ old.tys.submap new.tys ∧ old.v = new.v →
        EnvRel new env locals) ∧
    (∀ old map shadowers env, GlobalEnvInv old map shadowers env → ∀ (_unused : C),
      old.c.submap new.c ∧ old.tys.submap new.tys ∧ old.v = new.v →
        GlobalEnvInv new map shadowers env) := by
  refine ⟨?_, ?_, ?_⟩
  · intro old source flat related _ ⟨constructors, types, slots⟩
    exact valueRel_weak old source flat new
      ⟨related, constructors, types, slots ▸ subglobals_refl old.v⟩
  · intro old env locals related _ ⟨constructors, types, slots⟩
    exact envRel_weak old env locals new
      ⟨related, constructors, types, slots ▸ subglobals_refl old.v⟩
  · intro old map shadowers env related _ ⟨constructors, types, slots⟩
    exact globalEnvInv_weak old map shadowers env new
      ⟨related, constructors, types, slots ▸ subglobals_refl old.v⟩

/-- Canonical finite-map domain restriction, used for HOL's `DRESTRICT`. -/
noncomputable def finiteRestrict {α β : Type} (map : HolFiniteMapExact α β)
    (keep : Set α) : HolFiniteMapExact α β := by
  classical
  refine ⟨fun key => if key ∈ keep then map.lookup key else none, ?_⟩
  obtain ⟨keys, support⟩ := map.finiteSupport
  refine ⟨keys, ?_⟩
  intro key present
  apply support key
  by_cases member : key ∈ keep <;> simp_all

private def maptoBroadlookup {α β : Type} (map : HolFiniteMapExact α β) : α → Option β := map.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

/-- Canonical lookup/support roundtrip for the first finite-map argument. -/
theorem holFmapAsFiniteSupportParamWitness_drestrict_lem_f1 {α β : Type}
    (f1 : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup f1) f1.finiteSupport = f1 := by
  cases f1
  rfl

/-- Canonical lookup/support roundtrip for the second finite-map argument. -/
theorem holFmapAsFiniteSupportParamWitness_drestrict_lem_f2 {α β : Type}
    (f2 : HolFiniteMapExact α β) : mapofBroad (maptoBroadlookup f2) f2.finiteSupport = f2 := by
  cases f2
  rfl

/-- Restricting a larger map outside a submap's domain reconstructs the map. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "drestrict_lem"
  (fmap_as_finite_support_parameters := [f1, f2])]
theorem drestrict_lem {α β : Type} (f1 : HolFiniteMapExact α β) (f2 : HolFiniteMapExact α β)
    (submap : f1.submap f2) :
    (finiteRestrict f2 f1.domainᶜ).union f1 = f2 := by
  classical
  apply HolFiniteMapExact.ext_lookup
  intro key
  cases lookup : f1.lookup key with
  | none =>
    cases h : f2.lookup key <;>
      simp [HolFiniteMapExact.lookup_union, finiteRestrict, HolFiniteMapExact.domain, lookup, h]
  | some value =>
    have retained := submap key value lookup
    simp [HolFiniteMapExact.lookup_union, finiteRestrict, HolFiniteMapExact.domain, lookup, retained]

/-- The combined local and global environment relation survives global extension. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_all_rel_weak"
  (fmap_as_finite_support := [c, tys])]
theorem envAllRel_weak (old : GlobalEnv) (map : Environment) (locals : List VarN)
    (env : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value) (new : GlobalEnv)
    (premises : FactoredEnvAllRel old map env flatEnv locals ∧ old.c.submap new.c ∧
      old.tys.submap new.tys ∧ subglobals old.v new.v) :
    FactoredEnvAllRel new map env flatEnv locals := by
  obtain ⟨⟨base, sourceLocal, bindings, envEq, localEq, names, globals, localRel⟩,
    constructors, types, slots⟩ := premises
  exact ⟨base, sourceLocal, bindings, envEq, localEq, names,
    globalEnvInv_weak old map _ base new ⟨globals, constructors, types, slots⟩,
    envRel_weak old sourceLocal flatEnv.v new ⟨localRel, constructors, types, slots⟩⟩

/-- Related store lists remain related when the global environment grows. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "LIST_REL_sv_rel_weak"
  (fmap_as_finite_support := [c, tys])]
theorem storeList_weak (old : GlobalEnv) (source : List (StoreValue Value))
    (flat : List (StoreValue FlatSem.Value)) (new : GlobalEnv)
    (premises : List.Forall₂ (StoreValueRel old) source flat ∧ subglobals old.v new.v ∧
      old.c.submap new.c ∧ old.tys.submap new.tys) :
    List.Forall₂ (StoreValueRel new) source flat := by
  obtain ⟨related, slots, constructors, types⟩ := premises
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (storeValueRel_weak old _ _ new ⟨head, constructors, types, slots⟩) ih

/-- State relations survive growth without changing either evaluated state. -/
theorem stateRel_growth {C F : Type} (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (related : StateRel old source flat) : StateRel new source flat := by
  cases related with
  | intro nonempty refs clock ffi =>
    have conditions := (globalGrowth_iff old new).mp growth
    exact .intro source flat nonempty
      (storeList_weak old _ _ new ⟨refs, conditions.1, conditions.2.1, conditions.2.2⟩) clock ffi

end Flapjack.Compiler.Backend.SourceToFlat
