import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDenv

/-! Declaration simulation for simple source aliases. The factored value and
state relations remain subject to HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- An alias whose declaration does not abort with a type error must refer to
an existing source value. This discharges the lookup from the usual source
safety premise. -/
theorem dlet_alias_lookup_of_safe {F : Type} (source : SemanticPrimitivesHOL.State F)
    (sourceEnv : SemEnv Value) (location : Flapjack.Misc.Location.Locs)
    (name : VarN) (id : Ident ModN VarN)
    (safe : ∀ next, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) (.var id)] ≠
      (next, .err (.abort .typeError))) :
    ∃ value, nsLookup sourceEnv.v id = some value := by
  cases lookup : nsLookup sourceEnv.v id with
  | some value => exact ⟨value, rfl⟩
  | none =>
    have bad : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) (.var id)] =
        (source, .err (.abort .typeError)) := by
      simp [EvaluateHOL.evaluateDecs, EvaluateHOL.evaluate, AstHOL.patBindings, AstHOL.everyExp,
        oneConCheck, lookup, EvaluateHOL.typeError]
    exact False.elim (safe source bad)

/-- A singleton source alias and compiler binding share a global slot. -/
theorem globalEnvInv_alias (genv : GlobalEnv) (name : VarN) (idx : Nat) (trace : Tra)
    (value : Value) (stored : FlatSem.Value) (bound : idx < genv.v.length)
    (slot : genv.v[idx]?.getD none = some stored) (related : ValueRel genv value stored) :
    GlobalEnvInv genv { v := nsSing name (.glob trace idx), c := nsEmpty }
      (fun _ => False) { v := nsSing name value, c := nsEmpty } := by
  apply GlobalEnvInv.intro
  · intro id v _ lookup
    cases id with
    | short key =>
      by_cases keyEq : key = name
      · subst key
        simp [nsLookup, nsSing] at lookup
        subst v
        exact .intro _ _ _ _ idx stored trace (by simp [nsLookup, nsSing]) bound slot related
      · simp [nsLookup, nsSing, List.lookup, BEq.beq, keyEq] at lookup
    | long moduleName inner => simp [nsLookup, nsSing] at lookup
  · intro id arity stamp lookup
    cases id <;> simp [nsLookup, nsEmpty] at lookup

/-- A simple variable declaration reuses the original global binding and
emits no flat declarations. The source and flat states stay related; the
returned environments retain the factored global invariant. -/
theorem evaluateDlet_alias {C F : Type} (genv : GlobalEnv)
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (name : VarN) (id : Ident ModN VarN) (value : Value)
    (lookup : nsLookup sourceEnv.v id = some value)
    (invariant : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (states : StateRel genv source flat) :
    ∃ stored idx nameTrace,
      EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) (.var id)] =
        (source, .val { v := nsSing name value, c := nsEmpty }) ∧
      compileDecs trace n next compMap gen [.dlet location (.pvar name) (.var id)] =
        (n, next, { v := nsSing name (.glob nameTrace idx), c := nsEmpty }, gen, []) ∧
      FlatSem.evaluateDecs flat
        (compileDecs trace n next compMap gen [.dlet location (.pvar name) (.var id)]).2.2.2.2 =
        (flat, none) ∧
      ValueRel genv value stored ∧ StateRel genv source flat ∧
      GlobalEnvInv genv { v := nsSing name (.glob nameTrace idx), c := nsEmpty }
        (fun _ => False) { v := nsSing name value, c := nsEmpty } := by
  cases invariant with
  | intro _ _ _ values _ =>
    have unshadowed : ¬ (∃ x, False ∧ id = .short x) := by simp
    obtain ⟨_, _, _, idx, stored, nameTrace, compiledLookup, bound, slot, related⟩ :=
      values id value unshadowed lookup
    refine ⟨stored, idx, nameTrace, ?_, ?_, ?_, related, states, ?_⟩
    · simp [EvaluateHOL.evaluateDecs, EvaluateHOL.evaluate, AstHOL.patBindings, AstHOL.everyExp,
        oneConCheck, lookup, pmatch, EvaluateHOL.headValue, Flapjack.holHd, nsSing, alistToNs]
    · simp [compileDecs, simpleDlet, compiledLookup, nsSing, alistToNs]
    · simp [compileDecs, simpleDlet, compiledLookup, FlatSem.evaluateDecs]
    · exact globalEnvInv_alias genv name idx nameTrace value stored bound slot related

/-- The alias declaration preserves the full factored invariant and index
block without allocating globals or advancing the generation store. -/
theorem evaluateDlet_alias_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (name : VarN) (id : Ident ModN VarN) (value : Value)
    (lookup : nsLookup sourceEnv.v id = some value)
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : OracleInvariant.factoredInvariant interp transform gen genv idxs source flat) :
    ∃ stored idx nameTrace,
      EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) (.var id)] =
        (source, .val { v := nsSing name value, c := nsEmpty }) ∧
      compileDecs trace n next compMap gen [.dlet location (.pvar name) (.var id)] =
        (n, next, { v := nsSing name (.glob nameTrace idx), c := nsEmpty }, gen, []) ∧
      FlatSem.evaluateDecs flat
        (compileDecs trace n next compMap gen [.dlet location (.pvar name) (.var id)]).2.2.2.2 =
        (flat, none) ∧ ValueRel genv value stored ∧
      GlobalEnvInv genv { v := nsSing name (.glob nameTrace idx), c := nsEmpty }
        (fun _ => False) { v := nsSing name value, c := nsEmpty } ∧
      OracleInvariant.factoredInvariant interp transform gen genv idxs source flat ∧
      GlobalGrowth genv genv ∧ idxPrev next next := by
  obtain ⟨stored, idx, nameTrace, sourceRun, compiled, flatRun, valueRel, _, newInv⟩ :=
    evaluateDlet_alias genv source flat sourceEnv trace n next compMap gen location name id value
      lookup envInv invariant.2.2.1
  exact ⟨stored, idx, nameTrace, sourceRun, compiled, flatRun, valueRel, newInv, invariant,
    GlobalGrowth.refl genv, idxPrev_refl next⟩

/-- A source-safe alias declaration satisfies the factored declaration
simulation without assuming that its identifier lookup succeeds. -/
theorem evaluateDlet_alias_safe {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (name : VarN) (id : Ident ModN VarN)
    (safe : ∀ nextState, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) (.var id)] ≠
      (nextState, .err (.abort .typeError)))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : OracleInvariant.factoredInvariant interp transform gen genv idxs source flat) :
    ∃ value stored idx nameTrace,
      EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) (.var id)] =
        (source, .val { v := nsSing name value, c := nsEmpty }) ∧
      compileDecs trace n next compMap gen [.dlet location (.pvar name) (.var id)] =
        (n, next, { v := nsSing name (.glob nameTrace idx), c := nsEmpty }, gen, []) ∧
      FlatSem.evaluateDecs flat
        (compileDecs trace n next compMap gen [.dlet location (.pvar name) (.var id)]).2.2.2.2 =
        (flat, none) ∧ ValueRel genv value stored ∧
      GlobalEnvInv genv { v := nsSing name (.glob nameTrace idx), c := nsEmpty }
        (fun _ => False) { v := nsSing name value, c := nsEmpty } ∧
      OracleInvariant.factoredInvariant interp transform gen genv idxs source flat ∧
      GlobalGrowth genv genv ∧ idxPrev next next := by
  obtain ⟨value, lookup⟩ := dlet_alias_lookup_of_safe source sourceEnv location name id safe
  exact ⟨value, evaluateDlet_alias_factored interp transform genv idxs source flat sourceEnv trace n next
    compMap gen location name id value lookup envInv invariant⟩

end Flapjack.Compiler.Backend.SourceToFlat
