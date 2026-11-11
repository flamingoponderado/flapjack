module

import Flapjack.Compiler.Backend.SourceToFlat.Proofs.BindingCount

public import Flapjack.FiniteMap.AlistExact.Lookup
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDenv
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternRows
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.AllocDefsLookup
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateEmptyDeclarations

@[expose] public section

/-! Declaration simulation for simple source aliases. The factored value and
state relations remain subject to HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon
open OracleInvariant

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

/-- The source non-type-error premise enforces distinct pattern names and
the declaration's constructor check. -/
theorem dlet_conditions_of_safe {F : Type} (source : SemanticPrimitivesHOL.State F)
    (sourceEnv : SemEnv Value) (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (safe : ∀ next, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (next, .err (.abort .typeError))) :
    (AstHOL.patBindings pattern).Nodup ∧ AstHOL.everyExp (oneConCheck sourceEnv.c) expr = true := by
  by_cases distinct : (AstHOL.patBindings pattern).Nodup
  · cases checked : AstHOL.everyExp (oneConCheck sourceEnv.c) expr with
    | true => exact ⟨distinct, rfl⟩
    | false =>
      have bad : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
          (source, .err (.abort .typeError)) := by
        simp [EvaluateHOL.evaluateDecs, distinct, checked, EvaluateHOL.typeError]
      exact False.elim (safe source bad)
  · have bad : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
        (source, .err (.abort .typeError)) := by
      simp [EvaluateHOL.evaluateDecs, distinct, EvaluateHOL.typeError]
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

/-- A failing expression propagates through a non-alias declaration before
the generated pattern match can initialize any globals. -/
theorem evaluateDlet_pattern_flat_error {C F : Type}
    (flat middle : FlatSem.State C F) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap : Environment) (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (pattern : Pat) (expr : AstHOL.Exp) (error : ErrorResult FlatSem.Value)
    (notAlias : simpleDlet pattern expr = none)
    (expressionRun : FlatSem.evaluate ⟨[]⟩ flat
      [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] = (middle, .err error)) :
    FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location pattern expr]).2.2.2.2 =
      (middle, some error) := by
  have bound : middle.clock ≤ flat.clock := FlatSem.evaluate_clock_spec.1 _ _ _ _ _ expressionRun
  simp only [compileDecs, notAlias]
  simp [FlatSem.evaluateDecs, FlatSem.evaluate, expressionRun, FlatSem.fixClock, Nat.min_eq_right bound]

/-- A successful non-alias declaration preserves the full factored invariant
after all pattern bindings are initialized. Reserved slots are derived from
the pre-initialization invariant and the index-block bound. -/
theorem evaluateDlet_pattern_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source sourceMiddle : SemanticPrimitivesHOL.State F) (flat flatMiddle : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (compMap compMap2 : Environment)
    (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (value : Value) (flatValue : FlatSem.Value) (bindings : List (VarN × Value))
    (notAlias : simpleDlet pattern expr = none) (distinct : (AstHOL.patBindings pattern).Nodup)
    (wellformed : AstHOL.everyExp (oneConCheck sourceEnv.c) expr = true)
    (sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] = (sourceMiddle, .val [value]))
    (flatRun : FlatSem.evaluate ⟨[]⟩ flat
      [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] = (flatMiddle, .val [flatValue]))
    (matched : pmatch sourceEnv.c sourceMiddle.refs pattern value [] = .match bindings)
    (shadowers : VarN → Prop) (envInv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (mapsEq : compMap2.c = compMap.c) (valueRel : ValueRel genv value flatValue)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) sourceMiddle flatMiddle)
    (fits : start.vidx + (AstHOL.patBindings pattern).length ≤ finish.vidx) :
    ∃ (finalGenv : GlobalEnv) (finalFlat : FlatSem.State C F),
      let finalNext := { start with vidx := start.vidx + (AstHOL.patBindings pattern).length }
      EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
        (sourceMiddle, .val ⟨alistToNs bindings, nsEmpty⟩) ∧
      compileDecs trace n start compMap gen [.dlet location pattern expr] =
        (n + 4 + (AstHOL.patBindings pattern).length, finalNext,
          { emptyEnv with v := alistToNs (allocDefs (n + 4) start.vidx (AstHOL.patBindings pattern).reverse) }, gen,
          [.mat .none (compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr)
            [(compilePat compMap pattern, makeVarls 0 .none start.vidx (AstHOL.patBindings pattern).reverse)]]) ∧
      FlatSem.evaluateDecs flat (compileDecs trace n start compMap gen [.dlet location pattern expr]).2.2.2.2 =
        (finalFlat, none) ∧
      GlobalGrowth genv finalGenv ∧ StateRel finalGenv sourceMiddle finalFlat ∧
      EnvDomainEq
        { emptyEnv with v := alistToNs (allocDefs (n + 4) start.vidx (AstHOL.patBindings pattern).reverse) }
        ⟨alistToNs bindings, nsEmpty⟩ ∧
      GlobalEnvInv finalGenv
        { emptyEnv with v := alistToNs (allocDefs (n + 4) start.vidx (AstHOL.patBindings pattern).reverse) }
        (fun _ => False) ⟨alistToNs bindings, nsEmpty⟩ ∧
      factoredInvariant interp transform gen finalGenv (finalNext, finish, other) sourceMiddle finalFlat := by
  have invariantCopy := invariant
  obtain ⟨ok, typesOk, states, _, _, _, _, _, _, _⟩ := invariantCopy
  obtain ⟨flatBindings, flatMatch, related, names⟩ :=
    pmatch_success_sourceBindings genv compMap compMap2 sourceEnv sourceMiddle flatMiddle shadowers envInv
      mapsEq ok typesOk states pattern value flatValue valueRel bindings matched
  have flatDistinct : (flatBindings.map Prod.fst).Nodup := by simpa [names] using distinct
  obtain ⟨finalGenv, finalFlat, initRun, finalInv, constructors, types, slots, envResult⟩ :=
    invariantMakeVarls interp transform gen genv start finish other sourceMiddle flatMiddle start.vidx
      (flatBindings.map Prod.fst).reverse ⟨flatBindings⟩ 0 .none
      ⟨invariant, rfl, by simpa [names] using fits, rfl, flatDistinct⟩
  have growth : GlobalGrowth genv finalGenv := by
    apply GlobalGrowth.ofSubglobals genv finalGenv slots
    · rw [constructors]; exact fun _ _ h => h
    · rw [types]; exact fun _ _ h => h
  have related' := envRel_growth genv finalGenv growth _ _ related
  have finalEnv := envResult bindings (n + 4) related'
  have domain : EnvDomainEq
      { emptyEnv with v := alistToNs (allocDefs (n + 4) start.vidx (AstHOL.patBindings pattern).reverse) }
      ⟨alistToNs bindings, nsEmpty⟩ := by
    obtain ⟨entries, entriesEq, entriesNames⟩ := envRel_dom genv (alistToNs bindings) flatBindings related
    simp only [alistToNs, Namespace.bind.injEq, and_true] at entriesEq
    subst entries
    obtain ⟨values, valueModules⟩ := alistToNs_domains_eq (M := ModN)
      (allocDefs (n + 4) start.vidx (AstHOL.patBindings pattern).reverse) bindings (by
        intro key
        simp [fst_allocDefs, entriesNames, names])
    exact ⟨values, valueModules, envDomainEq_empty.2.2⟩
  refine ⟨finalGenv, finalFlat, ?_, ?_, ?_, growth, finalInv.2.2.1, domain, ?_, ?_⟩
  · simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun, matched,
      EvaluateHOL.headValue, Flapjack.holHd]
  · simp [compileDecs, notAlias, emptyEnv]
  · have initializerRun : FlatSem.evaluate ⟨flatBindings⟩ flatMiddle
        [makeVarls 0 .none start.vidx (AstHOL.patBindings pattern).reverse] =
        (finalFlat, .val [FlatSem.unitValue]) := by simpa [names] using initRun
    simp only [compileDecs, notAlias, FlatSem.evaluateDecs_cons, FlatSem.evaluateDec]
    rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations _ _ _
      (compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr) []).1, flatRun]
    simp (config := { zeta := false })
    have selection : FlatSem.selectRow flatMiddle
        [(compilePat compMap pattern, makeVarls 0 .none start.vidx (AstHOL.patBindings pattern).reverse)]
        flatValue FlatSem.bindExnV =
        .ok (flatBindings, makeVarls 0 .none start.vidx (AstHOL.patBindings pattern).reverse) := by
      simp [FlatSem.selectRow, FlatSem.pmatchRows, flatMatch, compilePat_bindings, distinct]
    rw [selection]
    simp [initializerRun, FlatSem.evaluateDecs, FlatSem.unitValue]
  · simpa [emptyEnv, names] using finalEnv
  · simpa [names] using finalInv

/-- An internal stage of the `Dlet` case of `compile_correct`. Oracle and
generation relations are added by `DletOutcome.toGrowing` before conversion
to the shared declaration case; this is not a separate HOL statement. -/
def DletOutcome {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n : Nat) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) : Prop :=
  let sourceResult := EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr]
  let compiled := compileDecs trace n start compMap gen [.dlet location pattern expr]
  ∃ flatLast newGenv flatError,
    FlatSem.evaluateDecs flat compiled.2.2.2.2 = (flatLast, flatError) ∧
    StateRel newGenv sourceResult.1 flatLast ∧ GlobalGrowth genv newGenv ∧
    match sourceResult.2 with
    | .val env => flatError = none ∧ EnvDomainEq compiled.2.2.1 env ∧
        GlobalEnvInv newGenv compiled.2.2.1 (fun _ => False) env ∧
        factoredInvariant interp transform compiled.2.2.2.1 newGenv
          (compiled.2.1, finish, other) sourceResult.1 flatLast
    | .err error => ∃ flatErr, flatError = some flatErr ∧ EvalResultRel newGenv (.err error) (.err flatErr) ∧
        match error with
        | .abort _ => True
        | .raise _ => factoredInvariant interp transform gen newGenv (start, finish, other) sourceResult.1 flatLast

/-- Assemble the non-alias `Dlet` cases from the expression induction
hypothesis. The hypothesis preserves the factored invariant for successful
and raised expression results; aborts need only the state relation. -/
theorem evaluateDlet_pattern_cases {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n : Nat) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (notAlias : simpleDlet pattern expr = none)
    (safe : ∀ next, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (next, .err (.abort .typeError)))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (expressionSim : ExprSim genv compMap ((AstHOL.patBindings pattern).reverse ++ trace)
      sourceEnv ⟨[]⟩ source flat expr)
    (expressionInvariant :
      let result := EvaluateHOL.evaluate source sourceEnv [expr]
      let flatResult := FlatSem.evaluate ⟨[]⟩ flat
        [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr]
      match result.2 with
      | .err (.abort _) => True
      | _ => factoredInvariant interp transform gen genv (start, finish, other) result.1 flatResult.1)
    (fits : start.vidx + (AstHOL.patBindings pattern).length ≤ finish.vidx) :
    DletOutcome interp transform genv start finish other source flat sourceEnv trace n compMap gen location pattern expr := by
  obtain ⟨distinct, wellformed⟩ := dlet_conditions_of_safe source sourceEnv location pattern expr safe
  have expressionRel := expressionSim
  unfold ExprSim at expressionRel
  cases sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] with
  | mk sourceMiddle sourceResult =>
    rw [sourceRun] at expressionRel expressionInvariant
    cases flatRun : FlatSem.evaluate ⟨[]⟩ flat
        [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] with
    | mk flatMiddle flatResult =>
      rw [flatRun] at expressionRel expressionInvariant
      obtain ⟨resultRel, states⟩ := expressionRel
      cases sourceResult with
      | err error =>
        cases resultRel with
        | @raise sourceValue flatValue related =>
          have sourceDec : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
              (sourceMiddle, .err (.raise sourceValue)) := by
            simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun]
          have flatDec := evaluateDlet_pattern_flat_error flat flatMiddle trace n start compMap gen location
            pattern expr (.raise flatValue) notAlias flatRun
          unfold DletOutcome
          rw [sourceDec]
          refine ⟨flatMiddle, genv, some (.raise flatValue), flatDec, states, GlobalGrowth.refl genv, ?_⟩
          exact ⟨.raise flatValue, rfl, .raise related, by simpa using expressionInvariant⟩
        | abort kind =>
          have sourceDec : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
              (sourceMiddle, .err (.abort kind)) := by
            simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun]
          have flatDec := evaluateDlet_pattern_flat_error flat flatMiddle trace n start compMap gen location
            pattern expr (.abort kind) notAlias flatRun
          unfold DletOutcome
          rw [sourceDec]
          exact ⟨flatMiddle, genv, some (.abort kind), flatDec, states, GlobalGrowth.refl genv,
            _, rfl, .abort kind, trivial⟩
      | val values =>
        obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv expr sourceMiddle values sourceRun
        cases resultRel with
        | value valueRelations =>
          cases valueRelations with
          | cons valueRel tail =>
            cases tail with
            | nil =>
              rename_i flatValue
              have current : factoredInvariant interp transform gen genv (start, finish, other)
                  sourceMiddle flatMiddle := by simpa using expressionInvariant
              cases matched : pmatch sourceEnv.c sourceMiddle.refs pattern value [] with
              | typeError =>
                apply (safe sourceMiddle).elim
                simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun, EvaluateHOL.headValue,
                  Flapjack.holHd, matched, EvaluateHOL.typeError]
              | noMatch =>
                have matchRel := patternSimulation genv compMap compMap sourceEnv sourceMiddle flatMiddle
                  [] (fun _ => False) envInv rfl current.1 current.2.1 states pattern value flatValue [] []
                  (by simpa [alistToNs, nsEmpty] using EnvRel.empty genv) valueRel
                simp only [List.nil_append, matched] at matchRel
                have flatMatched : FlatSem.pmatch flatMiddle (compilePat compMap pattern) flatValue [] =
                    .noMatch := by
                  simpa using matchResultRel_cases genv [] .noMatch _ matchRel
                have sourceDec : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
                    (sourceMiddle, .err (.raise SemanticPrimitivesHOL.bindExnV)) := by
                  simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun, matched,
                    EvaluateHOL.headValue, Flapjack.holHd]
                have flatDec : FlatSem.evaluateDecs flat
                    (compileDecs trace n start compMap gen [.dlet location pattern expr]).2.2.2.2 =
                    (flatMiddle, some (.raise FlatSem.bindExnV)) := by
                  simp only [compileDecs, notAlias, FlatSem.evaluateDecs_cons, FlatSem.evaluateDec]
                  rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations _ _ _
                    (compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr) []).1, flatRun]
                  simp (config := { zeta := false })
                  have selection : FlatSem.selectRow flatMiddle
                      [(compilePat compMap pattern, makeVarls 0 .none start.vidx (AstHOL.patBindings pattern).reverse)]
                      flatValue FlatSem.bindExnV = .error (.raise FlatSem.bindExnV) := by
                    simp [FlatSem.selectRow, FlatSem.pmatchRows, flatMatched]
                  rw [selection]
                have errorRel := (valueRel_lemmas genv current.1).2.2.2.1
                unfold DletOutcome
                rw [sourceDec]
                exact ⟨flatMiddle, genv, some (.raise FlatSem.bindExnV), flatDec, states,
                  GlobalGrowth.refl genv, _, rfl, .raise errorRel, current⟩
              | «match» bindings =>
                obtain ⟨finalGenv, finalFlat, sourceDec, compiled, flatDec, growth, finalStates,
                  domain, finalEnv, finalInvariant⟩ :=
                  evaluateDlet_pattern_factored interp transform genv start finish other source sourceMiddle flat
                    flatMiddle sourceEnv trace n compMap compMap gen location pattern expr value flatValue bindings
                    notAlias distinct wellformed sourceRun flatRun matched (fun _ => False) envInv rfl valueRel current fits
                rw [compiled] at flatDec
                unfold DletOutcome
                rw [sourceDec, compiled]
                exact ⟨_, _, none, flatDec, finalStates, growth, rfl, domain, finalEnv, finalInvariant⟩

/-- The simple-declaration optimization only recognizes a variable pattern
whose expression is itself a variable. -/
theorem simpleDlet_some_shape (pattern : Pat) (expr : AstHOL.Exp) (aliasValue : VarN × Ident ModN VarN)
    (found : simpleDlet pattern expr = some aliasValue) :
    ∃ name id, pattern = .pvar name ∧ expr = .var id := by
  cases pattern <;> cases expr <;> simp_all [simpleDlet]

/-- A `Dlet` retains the expression's oracle-forward and generation relations
on success and raised errors. Abort results impose no postcondition. -/
theorem dlet_effects_of_expression {C F : Type}
    (interp : Option (Value → Option (Config × C))) (gen : EnvironmentGenerationStore)
    (source : SemanticPrimitivesHOL.State F) (sourceEnv : SemEnv Value)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (expressionEffects :
      let result := EvaluateHOL.evaluate source sourceEnv [expr]
      match result.2 with
      | .err (.abort _) => True
      | _ => envGenRel gen result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState) :
    let result := EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr]
    match result.2 with
    | .err (.abort _) => True
    | _ => envGenRel gen result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState := by
  by_cases distinct : (AstHOL.patBindings pattern).Nodup
  · cases checked : AstHOL.everyExp (oneConCheck sourceEnv.c) expr with
    | false => simp [EvaluateHOL.evaluateDecs, distinct, checked, EvaluateHOL.typeError]
    | true =>
      cases run : EvaluateHOL.evaluate source sourceEnv [expr] with
      | mk middle result =>
        rw [run] at expressionEffects
        cases result with
        | err error =>
          cases error <;> simp_all [EvaluateHOL.evaluateDecs]
        | val values =>
          cases matched : pmatch sourceEnv.c middle.refs pattern (EvaluateHOL.headValue values) [] <;>
            simp_all [EvaluateHOL.evaluateDecs, EvaluateHOL.typeError]
  · simp [EvaluateHOL.evaluateDecs, distinct, EvaluateHOL.typeError]

/-- Compiling one value declaration leaves the environment-generation store
unchanged, including its identifier counter and stored maps. -/
theorem compileDlet_generationStore (trace : List VarN) (n : Nat) (start : NextIndices)
    (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) :
    (compileDecs trace n start compMap gen [.dlet location pattern expr]).2.2.2.1 = gen := by
  cases found : simpleDlet pattern expr with
  | none => simp [compileDecs, found]
  | some pair =>
    cases pair with
    | mk name id =>
      cases lookup : nsLookup compMap.v id <;> simp [compileDecs, found, lookup]
      case some binding => cases binding <;> rfl

/-- Expression induction hypothesis allowing the global environment to grow.
The growth and oracle postconditions are required only for non-abort results,
as in the original correctness theorem. The factored relations still need
HOL correspondence review. -/
def DletExpressionStep {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (expr : AstHOL.Exp) : Prop :=
  let result := EvaluateHOL.evaluate source sourceEnv [expr]
  let flatResult := FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap expr]
  ∃ nextGenv, ExprSim nextGenv compMap trace sourceEnv ⟨[]⟩ source flat expr ∧
    match result.2 with
    | .err (.abort _) => True
    | _ => GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform gen nextGenv (start, finish, other) result.1 flatResult.1 ∧
        envGenRel gen result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState

/-- An internal `Dlet` outcome with the original abort-sensitive growth,
generation, and oracle-forward conditions. -/
def DletOutcomeGrowing {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n : Nat) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) : Prop :=
  let result := EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr]
  let compiled := compileDecs trace n start compMap gen [.dlet location pattern expr]
  ∃ flatLast nextGenv flatError,
    FlatSem.evaluateDecs flat compiled.2.2.2.2 = (flatLast, flatError) ∧
    StateRel nextGenv result.1 flatLast ∧
    match result.2 with
    | .val env => flatError = none ∧ EnvDomainEq compiled.2.2.1 env ∧
        GlobalEnvInv nextGenv compiled.2.2.1 (fun _ => False) env ∧ GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform compiled.2.2.2.1 nextGenv (compiled.2.1, finish, other) result.1 flatLast ∧
        envGenRel compiled.2.2.2.1 result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState
    | .err error => ∃ flatErr, flatError = some flatErr ∧ EvalResultRel nextGenv (.err error) (.err flatErr) ∧
        match error with
        | .abort _ => True
        | .raise _ => GlobalGrowth genv nextGenv ∧
            factoredInvariant interp transform gen nextGenv (start, finish, other) result.1 flatLast ∧
            envGenRel gen result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState

/-- An internal stage adding the compiled index and generation store on
successful and raised results before forming the shared declaration case. -/
def DletOutcomeAdvanced {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n : Nat) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp) : Prop :=
  let result := EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr]
  let compiled := compileDecs trace n start compMap gen [.dlet location pattern expr]
  ∃ flatLast nextGenv flatError,
    FlatSem.evaluateDecs flat compiled.2.2.2.2 = (flatLast, flatError) ∧
    StateRel nextGenv result.1 flatLast ∧
    match result.2 with
    | .val env => flatError = none ∧ EnvDomainEq compiled.2.2.1 env ∧
        GlobalEnvInv nextGenv compiled.2.2.1 (fun _ => False) env ∧ GlobalGrowth genv nextGenv ∧
        factoredInvariant interp transform compiled.2.2.2.1 nextGenv (compiled.2.1, finish, other) result.1 flatLast ∧
        envGenRel compiled.2.2.2.1 result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState
    | .err error => ∃ flatErr, flatError = some flatErr ∧ EvalResultRel nextGenv (.err error) (.err flatErr) ∧
        match error with
        | .abort _ => True
        | .raise _ => GlobalGrowth genv nextGenv ∧
            factoredInvariant interp transform compiled.2.2.2.1 nextGenv (compiled.2.1, finish, other) result.1 flatLast ∧
            envGenRel compiled.2.2.2.1 result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState

/-- Advance the reserved block after a raised declaration result. -/
theorem DletOutcomeGrowing.advance {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n : Nat) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (bounded : idxPrev (compileDecs trace n start compMap gen [.dlet location pattern expr]).2.1 finish)
    (outcome : DletOutcomeGrowing interp transform genv start finish other source flat sourceEnv trace n
      compMap gen location pattern expr) :
    DletOutcomeAdvanced interp transform genv start finish other source flat sourceEnv trace n
      compMap gen location pattern expr := by
  unfold DletOutcomeGrowing at outcome
  unfold DletOutcomeAdvanced
  obtain ⟨flatLast, nextGenv, flatError, run, states, post⟩ := outcome
  refine ⟨flatLast, nextGenv, flatError, run, states, ?_⟩
  cases sourceRun : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] with
  | mk sourceLast result =>
    rw [sourceRun] at post
    cases result with
    | val env => exact post
    | err error =>
      obtain ⟨flatErr, isError, related, rest⟩ := post
      refine ⟨flatErr, isError, related, ?_⟩
      cases error with
      | abort kind => trivial
      | raise value =>
        obtain ⟨growth, invariant, generation, forward⟩ := rest
        have advanced := invariantIdxRangeShrink interp transform gen nextGenv start
          (compileDecs trace n start compMap gen [.dlet location pattern expr]).2.1 finish other
          sourceLast flatLast ⟨invariant, OracleInvariant.compileDecs_idxPrev trace n start compMap gen [.dlet location pattern expr] _ _ _ _ _ rfl, bounded⟩
        exact ⟨growth, by simpa [compileDlet_generationStore] using advanced,
          by simpa [compileDlet_generationStore] using generation, forward⟩

/-- A fixed-global declaration result and its oracle effects can be weakened
from an earlier global environment. -/
theorem DletOutcome.toGrowing {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (old middle : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n : Nat) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (growth : GlobalGrowth old middle)
    (outcome : DletOutcome interp transform middle start finish other source flat sourceEnv trace n compMap gen
      location pattern expr)
    (effects : let result := EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr]
      match result.2 with
      | .err (.abort _) => True
      | _ => envGenRel gen result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState) :
    DletOutcomeGrowing interp transform old start finish other source flat sourceEnv trace n compMap gen
      location pattern expr := by
  unfold DletOutcome at outcome
  unfold DletOutcomeGrowing
  obtain ⟨flatLast, nextGenv, flatError, run, states, nextGrowth, post⟩ := outcome
  refine ⟨flatLast, nextGenv, flatError, run, states, ?_⟩
  cases sourceRun : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] with
  | mk sourceLast result =>
    rw [sourceRun] at post effects
    cases result with
    | val env =>
      obtain ⟨noError, domain, envInv, invariant⟩ := post
      exact ⟨noError, domain, envInv, growth.trans nextGrowth, invariant,
        by simpa [compileDlet_generationStore] using effects.1, effects.2⟩
    | err error =>
      obtain ⟨flatErr, isError, related, rest⟩ := post
      refine ⟨flatErr, isError, related, ?_⟩
      cases error with
      | abort kind => trivial
      | raise value => exact ⟨growth.trans nextGrowth, rest, effects.1, effects.2⟩

/-- Simulate a non-alias `Dlet` when its expression may grow the global
environment. The abort branch does not assume global growth; successful and
raised branches compose the expression's growth with declaration allocation. -/
theorem evaluateDlet_pattern_growing {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n : Nat) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (notAlias : simpleDlet pattern expr = none)
    (safe : ∀ next, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (next, .err (.abort .typeError)))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (expressionStep : DletExpressionStep interp transform genv start finish other source flat sourceEnv
      ((AstHOL.patBindings pattern).reverse ++ trace) compMap gen expr)
    (fits : start.vidx + (AstHOL.patBindings pattern).length ≤ finish.vidx) :
    DletOutcomeGrowing interp transform genv start finish other source flat sourceEnv trace n compMap gen
      location pattern expr := by
  obtain ⟨distinct, wellformed⟩ := dlet_conditions_of_safe source sourceEnv location pattern expr safe
  unfold DletExpressionStep at expressionStep
  obtain ⟨middleGenv, expressionSim, expressionPost⟩ := expressionStep
  cases sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] with
  | mk sourceMiddle result =>
    rw [sourceRun] at expressionPost
    by_cases aborted : ∃ kind, result = .err (.abort kind)
    · obtain ⟨kind, rfl⟩ := aborted
      have sourceDec : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
          (sourceMiddle, .err (.abort kind)) := by
        simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun]
      unfold ExprSim at expressionSim
      rw [sourceRun] at expressionSim
      cases flatRun : FlatSem.evaluate ⟨[]⟩ flat
          [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] with
      | mk flatMiddle flatResult =>
        rw [flatRun] at expressionSim
        obtain ⟨resultRel, states⟩ := expressionSim
        cases resultRel with
        | abort kind =>
          have flatDec := evaluateDlet_pattern_flat_error flat flatMiddle trace n start compMap gen location
            pattern expr (.abort kind) notAlias flatRun
          unfold DletOutcomeGrowing
          rw [sourceDec]
          exact ⟨flatMiddle, middleGenv, some (.abort kind), flatDec, states, _, rfl, .abort kind, trivial⟩
    · have growth : GlobalGrowth genv middleGenv := by
        cases result with
        | val values => exact expressionPost.1
        | err error =>
          cases error with
          | abort kind => exact (aborted ⟨kind, rfl⟩).elim
          | raise value => exact expressionPost.1
      have postInvariant :
          let result := EvaluateHOL.evaluate source sourceEnv [expr]
          let flatResult := FlatSem.evaluate ⟨[]⟩ flat
            [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr]
          match result.2 with
          | .err (.abort _) => True
          | _ => factoredInvariant interp transform gen middleGenv (start, finish, other) result.1 flatResult.1 := by
        rw [sourceRun]
        cases result with
        | val values => exact expressionPost.2.1
        | err error =>
          cases error with
          | abort kind => trivial
          | raise value => exact expressionPost.2.1
      have expressionEffects :
          let result := EvaluateHOL.evaluate source sourceEnv [expr]
          match result.2 with
          | .err (.abort _) => True
          | _ => envGenRel gen result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState := by
        rw [sourceRun]
        cases result with
        | val values => exact expressionPost.2.2
        | err error =>
          cases error with
          | abort kind => trivial
          | raise value => exact expressionPost.2.2
      have envInv' := globalEnvInv_growth genv middleGenv growth compMap (fun _ => False) sourceEnv envInv
      have outcome := evaluateDlet_pattern_cases interp transform middleGenv start finish other source flat sourceEnv
        trace n compMap gen location pattern expr notAlias safe envInv' expressionSim postInvariant fits
      exact DletOutcome.toGrowing interp transform genv middleGenv start finish other source flat sourceEnv trace n
        compMap gen location pattern expr growth outcome
        (dlet_effects_of_expression interp gen source sourceEnv location pattern expr expressionEffects)

/-- The optimized alias case preserves its original generation and oracle
relations because evaluating the source variable leaves the state unchanged. -/
theorem evaluateDlet_alias_growing {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n : Nat) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (name : VarN) (id : Ident ModN VarN)
    (safe : ∀ next, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) (.var id)] ≠
      (next, .err (.abort .typeError)))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState) :
    DletOutcomeGrowing interp transform genv start finish other source flat sourceEnv trace n compMap gen
      location (.pvar name) (.var id) := by
  obtain ⟨value, lookup⟩ := dlet_alias_lookup_of_safe source sourceEnv location name id safe
  have effects : let result := EvaluateHOL.evaluate source sourceEnv [.var id]
      match result.2 with
      | .err (.abort _) => True
      | _ => envGenRel gen result.1.evalState ∧ oracForwardRel interp source.evalState result.1.evalState := by
    simpa [EvaluateHOL.evaluate, lookup] using ⟨generation, oracForwardRel_refl interp source.evalState⟩
  obtain ⟨_, idx, nameTrace, sourceDec, compiled, flatDec, _, states, newEnv⟩ :=
    evaluateDlet_alias genv source flat sourceEnv trace n start compMap gen location name id value
      lookup envInv invariant.2.2.1
  have outcome : DletOutcome interp transform genv start finish other source flat sourceEnv trace n compMap gen
      location (.pvar name) (.var id) := by
    rw [compiled] at flatDec
    unfold DletOutcome
    rw [sourceDec, compiled]
    obtain ⟨values, valueModules⟩ := alistToNs_domains_eq (M := ModN)
      [(name, VarName.glob nameTrace idx)] [(name, value)] (fun _ => Iff.rfl)
    obtain ⟨ctors, ctorModules⟩ := alistToNs_domains_eq (M := ModN) (N := ConN)
      (V := Nat × Option (Nat × List (Nat × Nat))) (W := Nat × Stamp) [] [] (fun _ => Iff.rfl)
    exact ⟨flat, genv, none, flatDec, states, GlobalGrowth.refl genv, rfl,
      ⟨values, valueModules, ctors, ctorModules⟩, newEnv, invariant⟩
  exact DletOutcome.toGrowing interp transform genv genv start finish other source flat sourceEnv trace n compMap gen
    location (.pvar name) (.var id) (GlobalGrowth.refl genv) outcome
    (dlet_effects_of_expression interp gen source sourceEnv location (.pvar name) (.var id) effects)

/-- The internal abort-sensitive `Dlet` outcome follows from the expression
induction hypothesis for both alias and general pattern compilation. -/
theorem evaluateDlet_growing {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n : Nat) (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (safe : ∀ next, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (next, .err (.abort .typeError)))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (expressionStep : DletExpressionStep interp transform genv start finish other source flat sourceEnv
      ((AstHOL.patBindings pattern).reverse ++ trace) compMap gen expr)
    (fits : start.vidx + (match simpleDlet pattern expr with
      | some _ => 0 | none => (AstHOL.patBindings pattern).length) ≤ finish.vidx) :
    DletOutcomeGrowing interp transform genv start finish other source flat sourceEnv trace n compMap gen
      location pattern expr := by
  cases aliasEq : simpleDlet pattern expr with
  | none =>
    exact evaluateDlet_pattern_growing interp transform genv start finish other source flat sourceEnv trace n
      compMap gen location pattern expr aliasEq safe envInv expressionStep (by simpa [aliasEq] using fits)
  | some found =>
    obtain ⟨name, id, rfl, rfl⟩ := simpleDlet_some_shape pattern expr found aliasEq
    exact evaluateDlet_alias_growing interp transform genv start finish other source flat sourceEnv trace n compMap gen
      location name id safe envInv invariant generation

/-- The internal simulation carries compiled indices on every non-abort
result, using the expression induction hypothesis. -/
theorem evaluateDlet_advanced_compiled {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish next : NextIndices) (other : Set (Nat × IndexKind))
    (source sourceLast : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n n' : Nat)
    (compMap nextMap : Environment) (gen nextGen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value)
    (compiled : compileDecs trace n start compMap gen [.dlet location pattern expr] =
      (n', next, nextMap, nextGen, flatDecs))
    (bounded : idxPrev next finish)
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
      (sourceLast, result))
    (notTypeError : result ≠ .err (.abort .typeError))
    (envInv : GlobalEnvInv genv compMap (fun _ => False) sourceEnv)
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (generation : envGenRel gen source.evalState)
    (expressionStep : DletExpressionStep interp transform genv start finish other source flat sourceEnv
      ((AstHOL.patBindings pattern).reverse ++ trace) compMap gen expr) :
    DletOutcomeAdvanced interp transform genv start finish other source flat sourceEnv trace n compMap gen
      location pattern expr := by
  apply DletOutcomeGrowing.advance interp transform genv start finish other source flat sourceEnv trace n
    compMap gen location pattern expr
  · simpa [compiled] using bounded
  · have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
        (last, .err (.abort .typeError)) := by
      intro last bad
      exact notTypeError (congrArg Prod.snd (sourceRun.symm.trans bad))
    have count := compileDecs_numBindings trace n start compMap gen [.dlet location pattern expr]
      n' next nextMap nextGen flatDecs compiled
    have slots : start.vidx + numBindings (.dlet location pattern expr) ≤ finish.vidx := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at count
      have finalBound := bounded.1
      omega
    apply evaluateDlet_growing interp transform genv start finish other source flat sourceEnv trace n
      compMap gen location pattern expr safe envInv invariant generation expressionStep
    cases found : simpleDlet pattern expr <;> simpa [numBindings.eq_1, found] using slots

/-- Convert the advanced value-declaration simulation into the shared
factored declaration case, including both abort and raised-error outcomes. -/
theorem DletOutcomeAdvanced.toFactoredDecCase {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish next : NextIndices) (other : Set (Nat × IndexKind))
    (source sourceLast : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n n' : Nat) (env nextEnv : Environment)
    (gen nextGen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (pattern : Pat) (expr : AstHOL.Exp) (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value)
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] = (sourceLast, result))
    (compiled : compileDecs trace n start env gen [.dlet location pattern expr] =
      (n', next, nextEnv, nextGen, flatDecs))
    (outcome : DletOutcomeAdvanced interp transform genv start finish other source flat sourceEnv trace n env gen
      location pattern expr) :
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen nextEnv flatDecs result := by
  unfold DletOutcomeAdvanced at outcome
  rw [sourceRun, compiled] at outcome
  obtain ⟨flatLast, finalGenv, flatError, flatRun, states, post⟩ := outcome
  refine ⟨flatLast, finalGenv, flatError, flatRun, states, ?_⟩
  cases result with
  | val resultEnv =>
    obtain ⟨noError, domain, envInv, growth, invariant, generation, forward⟩ := post
    refine ⟨?_, ?_, ?_⟩
    · intro _
      exact ⟨invariant, forward, growth⟩
    · intro env same
      cases same
      exact ⟨noError, domain, generation, envInv⟩
    · intro error impossible
      cases impossible
  | err error =>
    obtain ⟨flatErr, isError, related, effects⟩ := post
    refine ⟨?_, ?_, ?_⟩
    · intro notAbort
      cases error with
      | abort kind => exact False.elim notAbort
      | raise value => exact ⟨effects.2.1, effects.2.2.2, effects.1⟩
    · intro env impossible
      cases impossible
    · intro error' same
      cases same
      refine ⟨flatErr, isError, ?_⟩
      cases related with
      | raise valueRel => exact .raise valueRel
      | abort kind => exact .abort kind

/-- The `Dlet` declaration case in the shared factored result shape, using
the expression simulation and oracle effects supplied by its induction step. -/
theorem evaluateDlet_case_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish next : NextIndices) (other : Set (Nat × IndexKind))
    (source sourceLast : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (n n' : Nat) (env nextEnv : Environment)
    (gen nextGen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (pattern : Pat) (expr : AstHOL.Exp) (flatDecs : List FlatLang.Exp) (result : Result (SemEnv Value) Value)
    (sourceRun : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] = (sourceLast, result))
    (invariant : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (compiled : compileDecs trace n start env gen [.dlet location pattern expr] =
      (n', next, nextEnv, nextGen, flatDecs))
    (envInv : GlobalEnvInv genv env (fun _ => False) sourceEnv)
    (notTypeError : result ≠ .err (.abort .typeError))
    (generation : envGenRel gen source.evalState)
    (_future : envGenFutureRel interp nextGen source.evalState)
    (bounded : idxPrev next finish)
    (expressionStep : DletExpressionStep interp transform genv start finish other source flat sourceEnv
      ((AstHOL.patBindings pattern).reverse ++ trace) env gen expr) :
    FactoredDecCase interp transform genv source sourceLast flat finish next other nextGen nextEnv flatDecs result := by
  apply DletOutcomeAdvanced.toFactoredDecCase interp transform genv start finish next other source sourceLast flat
    sourceEnv trace n n' env nextEnv gen nextGen location pattern expr flatDecs result sourceRun compiled
  exact evaluateDlet_advanced_compiled interp transform genv start finish next other source sourceLast flat
    sourceEnv trace n n' env nextEnv gen nextGen location pattern expr flatDecs result compiled bounded
    sourceRun notTypeError envInv invariant generation expressionStep

end Flapjack.Compiler.Backend.SourceToFlat
