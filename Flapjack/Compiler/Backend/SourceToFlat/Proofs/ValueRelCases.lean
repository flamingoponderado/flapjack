import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRel

/-! Inversion facts for Flapjack's factored source-to-flat value relation.
These are infrastructure, not reviewed ports of the HOL relation equations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

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

/-- The source Eval environment value has no corresponding flat value in the
current relation. -/
theorem valueRel_source_env_false (genv : GlobalEnv) (env : SemEnv SemanticPrimitivesHOL.Value)
    (id : Nat × Nat) (flat : FlatSem.Value) : ¬ ValueRel genv (.env env id) flat := by
  intro h
  cases h

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

/-- Constructor inversion in the two-disjunct shape used by the original
proof. This is an infrastructure theorem over the still-unreviewed relation. -/
theorem valueRel_conv_cases (genv : GlobalEnv) (stamp : Option Stamp)
    (sources : List SemanticPrimitivesHOL.Value) (flat : FlatSem.Value) :
    ValueRel genv (.conv stamp sources) flat ↔
      (∃ sourceCtor flatCtor flats, stamp = some sourceCtor ∧ flat = .conv (some flatCtor) flats ∧
        List.Forall₂ (ValueRel genv) sources flats ∧
        genv.c.lookup (flatCtor, sources.length) = some sourceCtor) ∨
      (∃ flats, stamp = none ∧ flat = .conv none flats ∧ List.Forall₂ (ValueRel genv) sources flats) := by
  constructor
  · intro h
    cases h with
    | constructor _ ctor _ flats related lookup =>
      exact Or.inl ⟨_, ctor, flats, rfl, rfl, (valueListRel_iff genv sources flats).mp related, lookup⟩
    | tuple _ flats related =>
      exact Or.inr ⟨flats, rfl, rfl, (valueListRel_iff genv sources flats).mp related⟩
  · rintro (⟨sourceCtor, flatCtor, flats, rfl, rfl, related, lookup⟩ |
      ⟨flats, rfl, rfl, related⟩)
    · exact valueRel_constructor genv sourceCtor flatCtor sources flats related lookup
    · exact valueRel_tuple genv sources flats related

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

end Flapjack.Compiler.Backend.SourceToFlat
