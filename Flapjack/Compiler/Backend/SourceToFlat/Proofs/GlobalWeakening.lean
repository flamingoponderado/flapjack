import Flapjack.Compiler.Backend.SourceToFlat.Proofs.StateRel

/-! Weakening the factored source-to-flat relations across global growth. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Existing global slots and constructor/type lookups survive growth. This
Flapjack relation exposes the observations needed by the factored relations;
correspondence to the original subglobal/submap conditions is still open. -/
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

/-- Pointwise value relationships survive growth. -/
theorem valueList_growth (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (source : List Value) (flat : List FlatSem.Value)
    (related : List.Forall₂ (ValueRel old) source flat) : List.Forall₂ (ValueRel new) source flat := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (valueRel_growth old new growth _ _ head) ih

/-- Store entries survive growth, including arrays and thunk contents. -/
theorem storeValueRel_growth (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (source : StoreValue Value) (flat : StoreValue FlatSem.Value)
    (related : StoreValueRel old source flat) : StoreValueRel new source flat := by
  cases related with
  | refv rel => exact .refv (valueRel_growth old new growth _ _ rel)
  | w8array bytes => exact .w8array bytes
  | varray rel => exact .varray (valueList_growth old new growth _ _ rel)
  | thunk mode rel => exact .thunk mode (valueRel_growth old new growth _ _ rel)

/-- Pointwise store-entry relationships survive growth. -/
theorem storeList_growth (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (source : List (StoreValue Value)) (flat : List (StoreValue FlatSem.Value))
    (related : List.Forall₂ (StoreValueRel old) source flat) : List.Forall₂ (StoreValueRel new) source flat := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (storeValueRel_growth old new growth _ _ head) ih

/-- State relations survive growth without changing either evaluated state. -/
theorem stateRel_growth {C F : Type} (old new : GlobalEnv) (growth : GlobalGrowth old new)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (related : StateRel old source flat) : StateRel new source flat := by
  cases related with
  | intro nonempty refs clock ffi =>
    exact .intro source flat nonempty (storeList_growth old new growth _ _ refs) clock ffi

end Flapjack.Compiler.Backend.SourceToFlat
