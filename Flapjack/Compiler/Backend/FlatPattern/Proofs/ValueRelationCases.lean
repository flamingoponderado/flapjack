module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.StateRelation
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Operations

@[expose] public section

/-! Elimination and monotonicity for the proof-side pattern relations. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Compiler.Backend.FlatSem Flapjack.Compiler.Backend.FlatProps

/-- Literal relatedness is exact equality. The following case lemmas are
consequences of the source value relation. -/
theorem valueRel_lit (lit : Flapjack.AstHOL.Lit) (right : Value) :
    ValueRel (.litv lit) right ↔ right = .litv lit := by
  constructor
  · intro h
    cases h with
    | basic shape _ => exact shape
  · intro h
    subst right
    exact .basic rfl .nil

/-- Location relatedness preserves both the reference flag and index. -/
theorem valueRel_loc (flag : Bool) (index : Nat) (right : Value) :
    ValueRel (.loc flag index) right ↔ right = .loc flag index := by
  constructor
  · intro h
    cases h with
    | basic shape _ => exact shape
  · intro h
    subst right
    exact .basic rfl .nil

/-- Constructor relatedness preserves the tag and relates each field. -/
theorem valueRel_conv (stamp : Option (FlatLang.CtorId × FlatLang.TypeId))
    (values : List Value) (right : Value) :
    ValueRel (.conv stamp values) right ↔
      ∃ values', right = .conv stamp values' ∧ List.Forall₂ ValueRel values values' := by
  constructor
  · intro h
    cases h with
    | basic shape contents =>
      obtain ⟨values', rfl⟩ := shape
      exact ⟨values', rfl, contents⟩
  · rintro ⟨values', rfl, contents⟩
    exact .basic ⟨values', rfl⟩ contents

/-- A related closure has the corresponding compiled body and a related
captured environment. -/
theorem valueRel_closure (left : Environment Value) (name : Flapjack.AstHOL.VarN)
    (body : FlatLang.Exp) (right : Value) :
    ValueRel (.closure left name body) right ↔
      ∃ n env cfg, EnvRel n left env ∧ (compileExp cfg body).1 < n ∧
        right = .closure env name (compileDec cfg body) := by
  constructor
  · intro h
    cases h with
    | basic shape _ => exact False.elim shape
    | @closure n _ _ _ env cfg related bound => exact ⟨n, env, cfg, related, bound, rfl⟩
  · rintro ⟨n, env, cfg, related, bound, rfl⟩
    exact .closure related bound

/-- Related recursive closures retain their function names and have compiled
bodies with the original per-body name bounds. -/
theorem valueRel_recclosure (left : Environment Value)
    (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
    (name : Flapjack.AstHOL.VarN) (right : Value) :
    ValueRel (.recclosure left funs name) right ↔
      ∃ n env cfg, EnvRel n left env ∧
        (∀ entry ∈ funs, (compileExp cfg entry.2.2).1 < n) ∧
        right = .recclosure env (funs.map fun (f, x, body) => (f, x, compileDec cfg body)) name := by
  constructor
  · intro h
    cases h with
    | basic shape _ => exact False.elim shape
    | @recclosure n _ _ _ env cfg related bounds => exact ⟨n, env, cfg, related, bounds, rfl⟩
  · rintro ⟨n, env, cfg, related, bounds, rfl⟩
    exact .recclosure related bounds

/-- The six source value constructors characterize related right-hand values. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "v_rel_l_cases"]
theorem valueRel_leftCases (right : Value) :
    (∀ lit, ValueRel (.litv lit) right ↔
      right = .litv lit ∧ valueContainerXs right = []) ∧
    (∀ stamp values, ValueRel (.conv stamp values) right ↔
      (∃ values', right = .conv stamp values') ∧ List.Forall₂ ValueRel values (valueContainerXs right)) ∧
    (∀ env name body, ValueRel (.closure env name body) right ↔
      ∃ n env' cfg, right = .closure env' name (compileExp cfg body).2.2 ∧
        EnvRel n env env' ∧ (compileExp cfg body).1 < n) ∧
    (∀ env funs name, ValueRel (.recclosure env funs name) right ↔
      ∃ n env' cfg, right = .recclosure env'
        (funs.map fun (f, x, body) => (f, x, (compileExp cfg body).2.2)) name ∧
        EnvRel n env env' ∧ ∀ entry ∈ funs, (compileExp cfg entry.2.2).1 < n) ∧
    (∀ flag index, ValueRel (.loc flag index) right ↔
      right = .loc flag index ∧ valueContainerXs right = []) ∧
    (∀ values, ValueRel (.vectorv values) right ↔
      (∃ values', right = .vectorv values') ∧ List.Forall₂ ValueRel values (valueContainerXs right)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro lit
    rw [valueRel_lit]
    constructor
    · intro h; subst right; simp [valueContainerXs]
    · exact And.left
  · intro stamp values
    rw [valueRel_conv]
    constructor
    · rintro ⟨values', rfl, rel⟩
      exact ⟨⟨values', rfl⟩, rel⟩
    · rintro ⟨⟨values', rfl⟩, rel⟩
      exact ⟨values', rfl, rel⟩
  · intro env name body
    rw [valueRel_closure]
    simp only [compileDec]
    constructor <;> rintro ⟨n, env', cfg, h₁, h₂, h₃⟩
    · exact ⟨n, env', cfg, h₃, h₁, h₂⟩
    · exact ⟨n, env', cfg, h₂, h₃, h₁⟩
  · intro env funs name
    rw [valueRel_recclosure]
    simp only [compileDec]
    constructor <;> rintro ⟨n, env', cfg, h₁, h₂, h₃⟩
    · exact ⟨n, env', cfg, h₃, h₁, h₂⟩
    · exact ⟨n, env', cfg, h₂, h₃, h₁⟩
  · intro flag index
    rw [valueRel_loc]
    constructor
    · intro h; subst right; simp [valueContainerXs]
    · exact And.left
  · intro values
    constructor
    · intro related
      cases related with
      | basic shape contents =>
        obtain ⟨values', rfl⟩ := shape
        exact ⟨⟨values', rfl⟩, contents⟩
    · rintro ⟨⟨values', rfl⟩, contents⟩
      exact .basic ⟨values', rfl⟩ contents

/-- Bounded environment relatedness is monotone in the name bound. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "env_rel_mono"]
theorem envRel_mono (i : Nat) (left right : Environment Value) (j : Nat)
    (premises : EnvRel i left right ∧ j ≤ i) : EnvRel j left right := by
  obtain ⟨related, bound⟩ := premises
  rw [envRel_iff_lookup] at related ⊢
  intro name small
  exact related name (Nat.lt_of_lt_of_le small bound)

/-- Lookup of an in-range name yields related optional values. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "env_rel_ALOOKUP"]
theorem envRel_lookup (n : Nat) (left right : Environment Value) (name : Flapjack.AstHOL.VarN)
    (premises : EnvRel n left right ∧ decNameToNum name < n) :
    optionRel ValueRel (holALookup left.v name) (holALookup right.v name) :=
  (envRel_iff_lookup n left right).1 premises.1 name premises.2

/-- Adding a pair of related bindings preserves the bounded environment
relation. This is Flapjack infrastructure for closure application. -/
theorem envRel_cons (n : Nat) (left right : Environment Value) (name : Flapjack.AstHOL.VarN)
    (value value' : Value) (related : EnvRel n left right) (values : ValueRel value value') :
    EnvRel n { left with v := (name, value) :: left.v } { right with v := (name, value') :: right.v } := by
  apply (envRel_iff_lookup _ _ _).2
  apply aLookupRel_cons
  constructor
  · intro _
    exact values
  · exact (envRel_iff_lookup n left right).1 related

/-- The closure case of the application simulation: applying related closure
and argument values produces a compiled body and related environments. -/
theorem doOpApp_closure (leftEnv : Environment Value) (name : Flapjack.AstHOL.VarN)
    (body : FlatLang.Exp) (targetClosure arg targetArg : Value)
    (closures : ValueRel (.closure leftEnv name body) targetClosure) (args : ValueRel arg targetArg) :
    ∃ i sg body' targetEnv cfg,
      compileExp cfg body = (i, sg, body') ∧
      EnvRel (i + 1) { leftEnv with v := (name, arg) :: leftEnv.v } targetEnv ∧
      FlatSem.doOpApp [targetClosure, targetArg] = some (targetEnv, body') := by
  obtain ⟨n, targetEnv, cfg, envs, bound, rfl⟩ := (valueRel_closure leftEnv name body targetClosure).1 closures
  cases compiled : compileExp cfg body with
  | mk i rest =>
    cases rest with
    | mk sg body' =>
      have smaller : i + 1 ≤ n := by
        have h : i < n := by simpa [compiled] using bound
        exact Nat.succ_le_of_lt h
      have envs' := envRel_cons (i + 1) leftEnv targetEnv name arg targetArg (envRel_mono n leftEnv targetEnv (i + 1) ⟨envs, smaller⟩) args
      refine ⟨i, sg, body', { targetEnv with v := (name, targetArg) :: targetEnv.v }, cfg, compiled, envs', ?_⟩
      simp [FlatSem.doOpApp, compileDec, compiled]

/-- Decrementing both clocks preserves the proof-side state relation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "state_rel_dec_clock"]
theorem stateRel_decClock {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (related : StateRel cfg source target) :
    StateRel cfg (FlatSem.decClock source) (FlatSem.decClock target) := by
  rcases related with ⟨clock, refs, ffi, globals, configs⟩
  exact ⟨by simp [FlatSem.decClock, clock], refs, ffi, globals, configs⟩

end Flapjack.Compiler.Backend.FlatPattern
