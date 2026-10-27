import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalEnv
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.BindLocals
import Flapjack.Compiler.Backend.SourceToFlat.CompileExp
import Mathlib.Data.List.Forall2

/-! Source-to-flat value and environment relation infrastructure. Nested HOL
list and lookup premises are factored through mutual inductive helpers for
Lean's positivity checker. Exact HOL correspondence and compiler simulation
are not yet established. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendCommon

mutual
/-- Flapjack representation of the source-to-flat value relation. Nested HOL
premises use the helpers below; correspondence to HOL is still under review. -/
inductive ValueRel : GlobalEnv → SemanticPrimitivesHOL.Value → FlatSem.Value → Prop where
  | literal (genv : GlobalEnv) (lit : Lit) :
      ValueRel genv (.litv lit) (.litv lit)
  | constructor (genv : GlobalEnv) (stamp : Stamp) (ctor : FlatLang.CtorId × FlatLang.TypeId)
      (sourceValues : List SemanticPrimitivesHOL.Value) (flatValues : List FlatSem.Value)
      (related : ValueListRel genv sourceValues flatValues)
      (lookup : genv.c.lookup (ctor, sourceValues.length) = some stamp) :
      ValueRel genv (.conv (some stamp) sourceValues) (.conv (some ctor) flatValues)
  | tuple (genv : GlobalEnv) (sourceValues : List SemanticPrimitivesHOL.Value)
      (flatValues : List FlatSem.Value) (related : ValueListRel genv sourceValues flatValues) :
      ValueRel genv (.conv none sourceValues) (.conv none flatValues)
  | closure (genv : GlobalEnv) (compMap : Environment) (env : SemEnv SemanticPrimitivesHOL.Value)
      (sourceLocal : Namespace ModN VarN SemanticPrimitivesHOL.Value) (name : VarN) (body : AstHOL.Exp)
      (flatLocal : FlatSem.Environment FlatSem.Value) (t : List MlString) (ts : List Tra)
      (localRel : EnvRel genv sourceLocal flatLocal.v)
      (globalInv : GlobalEnvInv genv compMap (fun n => n ∈ flatLocal.v.map Prod.fst) env)
      (length : ts.length = flatLocal.v.length + 1) :
      ValueRel genv (.closure { env with v := nsAppend sourceLocal env.v } name body)
        (.closure flatLocal name
          (compileExp t { compMap with v := bindLocals ts (name :: flatLocal.v.map Prod.fst) compMap.v } body))
  | recclosure (genv : GlobalEnv) (compMap : Environment) (env : SemEnv SemanticPrimitivesHOL.Value)
      (sourceLocal : Namespace ModN VarN SemanticPrimitivesHOL.Value)
      (funs : List (VarN × VarN × AstHOL.Exp)) (name : VarN)
      (flatLocal : FlatSem.Environment FlatSem.Value) (t : List MlString) (ts : List Tra)
      (localRel : EnvRel genv sourceLocal flatLocal.v)
      (globalInv : GlobalEnvInv genv compMap (fun n => n ∈ flatLocal.v.map Prod.fst) env)
      (length : ts.length = funs.length + flatLocal.v.length) :
      ValueRel genv (.recclosure { env with v := nsAppend sourceLocal env.v } funs name)
        (.recclosure flatLocal
          (compileFuns t { compMap with v := bindLocals ts (funs.map Prod.fst ++ flatLocal.v.map Prod.fst) compMap.v } funs) name)
  | topRecclosure (genv : GlobalEnv) (compMap : Environment) (env : SemEnv SemanticPrimitivesHOL.Value)
      (funs : List (VarN × VarN × AstHOL.Exp)) (flatEnv : FlatSem.Environment FlatSem.Value)
      (name arg : VarN) (body : AstHOL.Exp) (newVars : List (VarN × VarName)) (t1 : List MlString) (t2 : Tra)
      (names : newVars.map Prod.fst = funs.reverse.map Prod.fst)
      (globalInv : GlobalEnvInv genv compMap (fun _ => False) env)
      (empty : flatEnv.v = []) (find : findRecFun name funs = some (arg, body))
      (closures : ∀ x, x ∈ funs.map Prod.fst →
        ∃ n y e trace t trace', newVars.lookup x = some (.glob trace n) ∧
          n < genv.v.length ∧ findRecFun x funs = some (y, e) ∧
          genv.v[n]?.getD none = some (.closure flatEnv y
            (compileExp t { compMap with v := nsBindList ((y, .localName trace' y) :: newVars) compMap.v } e))) :
      ValueRel genv (.recclosure env funs name)
        (.closure flatEnv arg
          (compileExp t1 { compMap with v := nsBindList ((arg, .localName t2 arg) :: newVars) compMap.v } body))
  | location (genv : GlobalEnv) (loc : Nat) (b : Bool) :
      ValueRel genv (.loc b loc) (.loc b (loc + 1))
  | vector (genv : GlobalEnv) (sourceValues : List SemanticPrimitivesHOL.Value)
      (flatValues : List FlatSem.Value) (related : ValueListRel genv sourceValues flatValues) :
      ValueRel genv (.vectorv sourceValues) (.vectorv flatValues)

/-- Flapjack helper for the pointwise value-list premise. -/
inductive ValueListRel : GlobalEnv → List SemanticPrimitivesHOL.Value → List FlatSem.Value → Prop where
  | nil (genv : GlobalEnv) : ValueListRel genv [] []
  | cons (genv : GlobalEnv) (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value)
      (sources : List SemanticPrimitivesHOL.Value) (flats : List FlatSem.Value)
      (head : ValueRel genv source flat) (tail : ValueListRel genv sources flats) :
      ValueListRel genv (source :: sources) (flat :: flats)

/-- Flapjack representation of the source-to-flat local environment relation. -/
inductive EnvRel : GlobalEnv → Namespace ModN VarN SemanticPrimitivesHOL.Value → List (VarN × FlatSem.Value) → Prop where
  | empty (genv : GlobalEnv) : EnvRel genv nsEmpty []
  | bind (genv : GlobalEnv) (name : VarN) (source : SemanticPrimitivesHOL.Value)
      (env : Namespace ModN VarN SemanticPrimitivesHOL.Value) (flatEnv : List (VarN × FlatSem.Value))
      (flat : FlatSem.Value) (hEnv : EnvRel genv env flatEnv) (hValue : ValueRel genv source flat) :
      EnvRel genv (nsBind name source env) ((name, flat) :: flatEnv)

/-- Flapjack representation of the source-to-flat global environment invariant. -/
inductive GlobalEnvInv : GlobalEnv → Environment → (VarN → Prop) → SemEnv SemanticPrimitivesHOL.Value → Prop where
  | intro (genv : GlobalEnv) (compMap : Environment) (shadowers : VarN → Prop)
      (env : SemEnv SemanticPrimitivesHOL.Value)
      (values : ∀ id v, ¬(∃ name, shadowers name ∧ id = Ident.short name) →
        nsLookup env.v id = some v → GlobalLookupRel genv compMap id v)
      (constructors : ∀ id arity stamp, nsLookup env.c id = some (arity, stamp) →
        ∃ cn tyGroup, nsLookup compMap.c id = some (cn, tyGroup) ∧
          genv.c.lookup ((cn, tyGroup.map Prod.fst), arity) = some stamp ∧
          ∀ tyId ctors, tyGroup = some (tyId, ctors) → genv.tys.lookup tyId = some ctors) :
      GlobalEnvInv genv compMap shadowers env

/-- Flapjack helper for the existential global-value lookup premise. -/
inductive GlobalLookupRel : GlobalEnv → Environment → Ident ModN VarN → SemanticPrimitivesHOL.Value → Prop where
  | intro (genv : GlobalEnv) (compMap : Environment) (id : Ident ModN VarN)
      (source : SemanticPrimitivesHOL.Value) (n : Nat) (flat : FlatSem.Value) (t : Tra)
      (lookup : nsLookup compMap.v id = some (.glob t n)) (bound : n < genv.v.length)
      (slot : genv.v[n]?.getD none = some flat) (related : ValueRel genv source flat) :
      GlobalLookupRel genv compMap id source
end

/-- Under the original bounds premise, the optional lookup reads exactly the
indexed global slot. -/
theorem globalSlot_eq_get (globals : List (Option FlatSem.Value)) (n : Nat)
    (bound : n < globals.length) : globals[n]?.getD none = globals[n] := by
  simp [bound]

/-- The list helper expresses the usual pointwise list relation. -/
theorem valueListRel_iff (genv : GlobalEnv) (sources : List SemanticPrimitivesHOL.Value)
    (flats : List FlatSem.Value) :
    ValueListRel genv sources flats ↔ List.Forall₂ (ValueRel genv) sources flats := by
  induction sources generalizing flats with
  | nil =>
    cases flats with
    | nil => constructor <;> intro _ <;> constructor
    | cons flat rest => constructor <;> intro h <;> cases h
  | cons source sources ih =>
    cases flats with
    | nil => constructor <;> intro h <;> cases h
    | cons flat flats =>
      constructor
      · intro h
        cases h with
        | cons _ _ _ _ head tail => exact .cons head (ih flats |>.mp tail)
      · intro h
        cases h with
        | cons head tail => exact .cons genv source flat sources flats head (ih flats |>.mpr tail)

/-- Introduce a constructor relation from the pointwise premise used by HOL. -/
theorem valueRel_constructor (genv : GlobalEnv) (stamp : Stamp) (ctor : FlatLang.CtorId × FlatLang.TypeId)
    (sources : List SemanticPrimitivesHOL.Value) (flats : List FlatSem.Value)
    (related : List.Forall₂ (ValueRel genv) sources flats)
    (lookup : genv.c.lookup (ctor, sources.length) = some stamp) :
    ValueRel genv (.conv (some stamp) sources) (.conv (some ctor) flats) :=
  .constructor genv stamp ctor sources flats ((valueListRel_iff genv sources flats).mpr related) lookup

/-- Introduce a tuple relation from the pointwise premise used by HOL. -/
theorem valueRel_tuple (genv : GlobalEnv) (sources : List SemanticPrimitivesHOL.Value)
    (flats : List FlatSem.Value) (related : List.Forall₂ (ValueRel genv) sources flats) :
    ValueRel genv (.conv none sources) (.conv none flats) :=
  .tuple genv sources flats ((valueListRel_iff genv sources flats).mpr related)

/-- Introduce a vector relation from the pointwise premise used by HOL. -/
theorem valueRel_vector (genv : GlobalEnv) (sources : List SemanticPrimitivesHOL.Value)
    (flats : List FlatSem.Value) (related : List.Forall₂ (ValueRel genv) sources flats) :
    ValueRel genv (.vectorv sources) (.vectorv flats) :=
  .vector genv sources flats ((valueListRel_iff genv sources flats).mpr related)

/-- The lookup helper is equivalent to the original existential premise. -/
theorem globalLookupRel_iff (genv : GlobalEnv) (compMap : Environment) (id : Ident ModN VarN)
    (source : SemanticPrimitivesHOL.Value) :
    GlobalLookupRel genv compMap id source ↔
      ∃ n flat t, nsLookup compMap.v id = some (.glob t n) ∧ n < genv.v.length ∧
        genv.v[n]?.getD none = some flat ∧ ValueRel genv source flat := by
  constructor
  · intro h
    cases h with
    | intro _ _ _ n flat t lookup bound slot related =>
      exact ⟨n, flat, t, lookup, bound, slot, related⟩
  · rintro ⟨n, flat, t, lookup, bound, slot, related⟩
    exact .intro genv compMap id source n flat t lookup bound slot related

/-- Expanding the auxiliary lookup predicate recovers the two global
environment conditions. The list-index correspondence to HOL is still subject
to source review. -/
theorem globalEnvInv_iff (genv : GlobalEnv) (compMap : Environment) (shadowers : VarN → Prop)
    (env : SemEnv SemanticPrimitivesHOL.Value) :
    GlobalEnvInv genv compMap shadowers env ↔
      (∀ id v, ¬(∃ name, shadowers name ∧ id = Ident.short name) →
        nsLookup env.v id = some v → ∃ n v' t,
          nsLookup compMap.v id = some (.glob t n) ∧ n < genv.v.length ∧
          genv.v[n]?.getD none = some v' ∧ ValueRel genv v v') ∧
      (∀ id arity stamp, nsLookup env.c id = some (arity, stamp) →
        ∃ cn tyGroup, nsLookup compMap.c id = some (cn, tyGroup) ∧
          genv.c.lookup ((cn, tyGroup.map Prod.fst), arity) = some stamp ∧
          ∀ tyId ctors, tyGroup = some (tyId, ctors) → genv.tys.lookup tyId = some ctors) := by
  constructor
  · intro h
    cases h with
    | intro _ _ _ values constructors =>
      exact ⟨fun id v notShadowed lookup =>
        (globalLookupRel_iff genv compMap id v).mp (values id v notShadowed lookup), constructors⟩
  · rintro ⟨values, constructors⟩
    exact .intro genv compMap shadowers env
      (fun id v notShadowed lookup =>
        (globalLookupRel_iff genv compMap id v).mpr (values id v notShadowed lookup)) constructors

end Flapjack.Compiler.Backend.SourceToFlat
