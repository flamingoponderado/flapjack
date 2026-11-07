import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRel

/-! Inversion facts for the source-to-flat value relation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Compiler.Backend.BackendCommon

namespace EnvRelListReview

/-- The global environment uses the reviewed finite-map representation. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env

end EnvRelListReview

/-- A related source closure must be a compiled flat closure with related
captured locals and a compatible global environment. This is an inversion
lemma for the factored relation, not a separate HOL theorem port. -/
theorem valueRel_closure_iff (genv : GlobalEnv) (sourceEnv : SemEnv Value)
    (name : VarN) (body : AstHOL.Exp) (flat : FlatSem.Value) :
    ValueRel genv (.closure sourceEnv name body) flat ↔
      ∃ compMap globalEnv sourceLocal flatLocal trace traces,
        sourceEnv = { globalEnv with v := nsAppend sourceLocal globalEnv.v } ∧
        flat = .closure flatLocal name
          (compileExp trace { compMap with v := bindLocals traces (name :: flatLocal.v.map Prod.fst) compMap.v } body) ∧
        EnvRel genv sourceLocal flatLocal.v ∧
        GlobalEnvInv genv compMap (fun n => n ∈ flatLocal.v.map Prod.fst) globalEnv ∧
        traces.length = flatLocal.v.length + 1 := by
  constructor
  · intro related
    cases related with
    | closure compMap globalEnv sourceLocal _ _ flatLocal trace traces locals globals length =>
      exact ⟨compMap, globalEnv, sourceLocal, flatLocal, trace, traces, rfl, rfl, locals, globals, length⟩
  · rintro ⟨compMap, globalEnv, sourceLocal, flatLocal, trace, traces, rfl, rfl, locals, globals, length⟩
    exact .closure genv compMap globalEnv sourceLocal name body flatLocal trace traces locals globals length

/-- Recursive closures relate either to a compiled local recursive closure or
to the top-level global-closure representation. -/
theorem valueRel_recclosure_iff (genv : GlobalEnv) (sourceEnv : SemEnv Value)
    (funs : List (VarN × VarN × AstHOL.Exp)) (name : VarN) (flat : FlatSem.Value) :
    ValueRel genv (.recclosure sourceEnv funs name) flat ↔
      (∃ compMap globalEnv sourceLocal flatLocal trace traces,
        sourceEnv = { globalEnv with v := nsAppend sourceLocal globalEnv.v } ∧
        flat = .recclosure flatLocal
          (compileFuns trace { compMap with v := bindLocals traces (funs.map Prod.fst ++ flatLocal.v.map Prod.fst) compMap.v } funs) name ∧
        EnvRel genv sourceLocal flatLocal.v ∧
        GlobalEnvInv genv compMap (fun n => n ∈ flatLocal.v.map Prod.fst) globalEnv ∧
        traces.length = funs.length + flatLocal.v.length) ∨
      (∃ compMap flatEnv arg body newVars trace localTrace,
        newVars.map Prod.fst = funs.reverse.map Prod.fst ∧
        GlobalEnvInv genv compMap (fun _ => False) sourceEnv ∧ flatEnv.v = [] ∧
        findRecFun name funs = some (arg, body) ∧
        (∀ x, x ∈ funs.map Prod.fst → ∃ n y e storedTrace bodyTrace argTrace,
          newVars.lookup x = some (.glob storedTrace n) ∧ n < genv.v.length ∧
          findRecFun x funs = some (y, e) ∧
          genv.v[n]?.getD none = some (.closure flatEnv y
            (compileExp bodyTrace { compMap with v := nsBindList ((y, .localName argTrace y) :: newVars) compMap.v } e))) ∧
        flat = .closure flatEnv arg
          (compileExp trace { compMap with v := nsBindList ((arg, .localName localTrace arg) :: newVars) compMap.v } body)) := by
  constructor
  · intro related
    cases related with
    | recclosure compMap globalEnv sourceLocal _ _ flatLocal trace traces locals globals length =>
      exact Or.inl ⟨compMap, globalEnv, sourceLocal, flatLocal, trace, traces, rfl, rfl, locals, globals, length⟩
    | topRecclosure =>
      rename_i compMap flatEnv arg body newVars trace localTrace empty globals names closures found
      exact Or.inr ⟨compMap, flatEnv, arg, body, newVars, trace, localTrace, names, globals, empty, found, closures, rfl⟩
  · rintro (⟨compMap, globalEnv, sourceLocal, flatLocal, trace, traces, rfl, rfl, locals, globals, length⟩ |
      ⟨compMap, flatEnv, arg, body, newVars, trace, localTrace, names, globals, empty, found, closures, rfl⟩)
    · exact .recclosure genv compMap globalEnv sourceLocal funs name flatLocal trace traces locals globals length
    · exact .topRecclosure genv compMap sourceEnv funs flatEnv name arg body newVars trace localTrace
        names globals empty found closures

/-- Related literal values have the same literal. -/
theorem valueRel_literal_iff (genv : GlobalEnv) (lit : Lit) (flat : FlatSem.Value) :
    ValueRel genv (.litv lit) flat ↔ flat = .litv lit := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    exact .literal genv lit

/-- Related locations retain the flag and offset the flat address by one. -/
theorem valueRel_location_iff (genv : GlobalEnv) (flag : Bool) (loc : Nat) (flat : FlatSem.Value) :
    ValueRel genv (.loc flag loc) flat ↔ flat = .loc flag (loc + 1) := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    exact .location genv loc flag

/-- A related source vector corresponds to a flat vector whose elements are
pointwise related. -/
theorem valueRel_vector_iff (genv : GlobalEnv) (sources : List SemanticPrimitivesHOL.Value)
    (flat : FlatSem.Value) :
    ValueRel genv (.vectorv sources) flat ↔
      ∃ flats, flat = .vectorv flats ∧ List.Forall₂ (ValueRel genv) sources flats := by
  constructor
  · intro h
    cases h with
    | vector _ flats related =>
      exact ⟨flats, rfl, (valueListRel_iff genv sources flats).mp related⟩
  · rintro ⟨flats, rfl, related⟩
    exact valueRel_vector genv sources flats related

/-- A source constructor value relates to a flat constructor value with
pointwise related fields and the corresponding constructor-map lookup. -/
theorem valueRel_conv_iff (genv : GlobalEnv) (stamp : Option Stamp)
    (sources : List SemanticPrimitivesHOL.Value) (flat : FlatSem.Value) :
    ValueRel genv (.conv stamp sources) flat ↔
      ∃ flats ctor, List.Forall₂ (ValueRel genv) sources flats ∧ flat = .conv ctor flats ∧
        match stamp with
        | none => ctor = none
        | some sourceCtor => ∃ flatCtor, ctor = some flatCtor ∧
            genv.c.lookup (flatCtor, sources.length) = some sourceCtor := by
  constructor
  · intro h
    cases h with
    | constructor _ ctor _ flats related lookup =>
      exact ⟨flats, some ctor, (valueListRel_iff genv sources flats).mp related,
        rfl, ⟨ctor, rfl, lookup⟩⟩
    | tuple _ flats related =>
      exact ⟨flats, none, (valueListRel_iff genv sources flats).mp related, rfl, rfl⟩
  · rintro ⟨flats, ctor, related, rfl, condition⟩
    cases stamp with
    | none =>
      cases condition
      exact valueRel_tuple genv sources flats related
    | some sourceCtor =>
      obtain ⟨flatCtor, rfl, lookup⟩ := condition
      exact valueRel_constructor genv sourceCtor flatCtor sources flats related lookup

/-- An empty source local namespace relates only to an empty flat environment. -/
theorem envRel_empty_iff (genv : GlobalEnv) (flatEnv : List (VarN × FlatSem.Value)) :
    EnvRel genv nsEmpty flatEnv ↔ flatEnv = [] := by
  constructor
  · intro h
    generalize he : (nsEmpty : Namespace ModN VarN SemanticPrimitivesHOL.Value) = sourceEnv at h
    cases h with
    | empty => rfl
    | bind _ _ env _ _ _ _ => cases env; simp [nsEmpty, nsBind] at he
  · intro h
    cases h
    exact .empty genv

/-- Inverting a local binding exposes the related head and remaining local
environment. -/
theorem envRel_bind_iff (genv : GlobalEnv) (name : VarN) (source : SemanticPrimitivesHOL.Value)
    (env : Namespace ModN VarN SemanticPrimitivesHOL.Value) (flatEnv : List (VarN × FlatSem.Value)) :
    EnvRel genv (nsBind name source env) flatEnv ↔
      ∃ flat tail, ValueRel genv source flat ∧ EnvRel genv env tail ∧ flatEnv = (name, flat) :: tail := by
  constructor
  · intro h
    generalize he : nsBind name source env = sourceEnv at h
    cases h with
    | empty => cases env; simp [nsEmpty, nsBind] at he
    | bind name' source' env' tail flat hEnv hValue =>
      cases env with
      | bind values modules =>
        cases env' with
        | bind values' modules' =>
          simp only [nsBind, Namespace.bind.injEq, List.cons.injEq, Prod.mk.injEq] at he
          rcases he with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
          exact ⟨flat, tail, hValue, hEnv, rfl⟩
  · rintro ⟨flat, tail, hValue, hEnv, rfl⟩
    exact .bind genv name source env tail flat hEnv hValue

/-- An association-list source environment relates exactly when corresponding
names agree and corresponding values satisfy the factored relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_rel_LIST_REL"
  (fmap_as_finite_support := [c, tys])]
theorem envRel_alist_iff (genv : GlobalEnv)
    (sourceEnv : List (VarN × SemanticPrimitivesHOL.Value)) (flatEnv : List (VarN × FlatSem.Value)) :
    EnvRel genv (alistToNs sourceEnv) flatEnv ↔
      List.Forall₂ (fun a b => a.1 = b.1 ∧ ValueRel genv a.2 b.2) sourceEnv flatEnv := by
  induction sourceEnv generalizing flatEnv with
  | nil =>
    change EnvRel genv nsEmpty flatEnv ↔ _
    rw [envRel_empty_iff]
    simp
  | cons entry rest ih =>
    cases entry with
    | mk name source =>
      change EnvRel genv (nsBind name source (alistToNs rest)) flatEnv ↔ _
      rw [envRel_bind_iff, List.forall₂_cons_left_iff]
      constructor
      · rintro ⟨flat, tail, hValue, hEnv, rfl⟩
        exact ⟨(name, flat), tail, ⟨rfl, hValue⟩, (ih tail).mp hEnv, rfl⟩
      · rintro ⟨⟨flatName, flat⟩, tail, ⟨hName, hValue⟩, hEnv, rfl⟩
        cases hName
        exact ⟨flat, tail, hValue, (ih tail).mpr hEnv, rfl⟩

/-- Related environments have association lists with the same names. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_rel_dom"
  (fmap_as_finite_support := [c, tys])]
theorem envRel_dom (genv : GlobalEnv) (env : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flatEnv : List (VarN × FlatSem.Value)) (related : EnvRel genv env flatEnv) :
    ∃ entries, env = alistToNs entries ∧ entries.map Prod.fst = flatEnv.map Prod.fst := by
  induction flatEnv generalizing env with
  | nil =>
    cases related
    exact ⟨[], rfl, rfl⟩
  | cons first rest ih =>
    cases related with
    | bind name value env flatEnv flat hEnv hValue =>
      obtain ⟨entries, rfl, names⟩ := ih env hEnv
      exact ⟨(name, value) :: entries, rfl, by simp [names]⟩

/-- Appending related environments preserves their relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_rel_append"
  (fmap_as_finite_support := [c, tys])]
theorem envRel_nsAppend (genv : GlobalEnv)
    (left right : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flatLeft flatRight : List (VarN × FlatSem.Value))
    (leftRel : EnvRel genv left flatLeft) (rightRel : EnvRel genv right flatRight) :
    EnvRel genv (nsAppend left right) (flatLeft ++ flatRight) := by
  induction flatLeft generalizing left with
  | nil =>
    cases leftRel
    cases right
    simpa [nsAppend, nsEmpty] using rightRel
  | cons head tail ih =>
    cases leftRel with
    | bind name value env flatEnv flat hEnv hValue =>
      have extended := EnvRel.bind genv name value (nsAppend env right) (tail ++ flatRight) flat (ih env hEnv) hValue
      cases env
      cases right
      simpa [nsAppend, nsBind] using extended

/-- A one-binding source environment relates exactly to a related singleton. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_rel_one"
  (fmap_as_finite_support := [c, tys])]
theorem envRel_one (genv : GlobalEnv) (name : VarN) (source : SemanticPrimitivesHOL.Value)
    (flatEnv : List (VarN × FlatSem.Value)) :
    EnvRel genv (nsBind name source nsEmpty) flatEnv ↔
      ∃ flat, flatEnv = [(name, flat)] ∧ ValueRel genv source flat := by
  rw [envRel_bind_iff]
  simp [envRel_empty_iff, and_comm]

/-- Extending related environments with related values preserves the relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_rel_bind_one"
  (fmap_as_finite_support := [c, tys])]
theorem envRel_bind_one (genv : GlobalEnv) (env : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flat : FlatSem.Value) (name : VarN) (source : SemanticPrimitivesHOL.Value)
    (flatEnv : List (VarN × FlatSem.Value))
    (valueRel : ValueRel genv source flat) (envRel : EnvRel genv env flatEnv) :
    EnvRel genv (nsBind name source env) ((name, flat) :: flatEnv) :=
  .bind genv name source env flatEnv flat envRel valueRel

namespace EnvAllRelPort

/-- Roundtrip for the global carrier's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env :=
  GlobalEnv.holFmapAsFiniteSupportWitness env

end EnvAllRelPort

/-- Combined local and global environment relation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_all_rel"
  (fmap_as_finite_support := [c, tys])]
def FactoredEnvAllRel (genv : GlobalEnv) (compMap : Environment) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN) : Prop :=
  ∃ (baseEnv : SemEnv Value) (sourceLocal : Namespace ModN VarN Value) (bindings : List (VarN × Value)),
    sourceEnv = { baseEnv with v := nsAppend sourceLocal baseEnv.v } ∧
    sourceLocal = alistToNs bindings ∧ bindings.map Prod.fst = locals ∧
    GlobalEnvInv genv compMap (fun name => name ∈ locals) baseEnv ∧ EnvRel genv sourceLocal flatEnv.v

/-- The combined environment relation exposes its original case structure. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_all_rel_cases"
  (fmap_as_finite_support := [c, tys])]
theorem factoredEnvAllRel_source_cases (genv : GlobalEnv) (compMap : Environment)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN) :
    FactoredEnvAllRel genv compMap sourceEnv flatEnv locals ↔
      ∃ sourceLocal baseEnv flatValues,
        sourceEnv = { baseEnv with v := nsAppend sourceLocal baseEnv.v } ∧
        flatEnv = ⟨flatValues⟩ ∧
        (∃ bindings, sourceLocal = alistToNs bindings ∧ bindings.map Prod.fst = locals) ∧
        GlobalEnvInv genv compMap (fun name => name ∈ locals) baseEnv ∧
        EnvRel genv sourceLocal flatValues := by
  constructor
  · rintro ⟨base, sourceLocal, bindings, sourceEq, localEq, names, globals, localsRel⟩
    exact ⟨sourceLocal, base, flatEnv.v, sourceEq, by cases flatEnv; rfl,
      ⟨bindings, localEq, names⟩, globals, localsRel⟩
  · rintro ⟨sourceLocal, base, values, sourceEq, rfl, ⟨bindings, localEq, names⟩, globals, localsRel⟩
    exact ⟨base, sourceLocal, bindings, sourceEq, localEq, names, globals, localsRel⟩

/-- The factored combined environment relation determines the flat local
names. -/
theorem factoredEnvAllRel_names (genv : GlobalEnv) (compMap : Environment) (sourceEnv : SemEnv Value)
    (flatEnv : FlatSem.Environment FlatSem.Value) (locals : List VarN)
    (related : FactoredEnvAllRel genv compMap sourceEnv flatEnv locals) :
    locals = flatEnv.v.map Prod.fst := by
  obtain ⟨_, _, bindings, _, localEq, names, _, localRel⟩ := related
  rw [localEq] at localRel
  have pairs := (envRel_alist_iff genv bindings flatEnv.v).mp localRel
  have namesOfPairs : ∀ (xs : List (VarN × Value)) (ys : List (VarN × FlatSem.Value)),
      List.Forall₂ (fun a b => a.1 = b.1 ∧ ValueRel genv a.2 b.2) xs ys →
      xs.map Prod.fst = ys.map Prod.fst := by
    intro xs ys pairs
    induction pairs with
    | nil => rfl
    | cons head tail ih =>
      simp only [List.map_cons]
      rw [head.1, ih]
  exact names.symm.trans (namesOfPairs bindings flatEnv.v pairs)

end Flapjack.Compiler.Backend.SourceToFlat
