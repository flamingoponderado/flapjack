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

/-- The simple-declaration optimization only recognizes a variable pattern
whose expression is itself a variable. -/
theorem simpleDlet_some_shape (pattern : Pat) (expr : AstHOL.Exp) (aliasValue : VarN × Ident ModN VarN)
    (found : simpleDlet pattern expr = some aliasValue) :
    ∃ name id, pattern = .pvar name ∧ expr = .var id := by
  cases pattern <;> cases expr <;> simp_all [simpleDlet]

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
  obtain ⟨middleGenv, expressionRel, expressionPost⟩ := expressionStep
  unfold ExprSim at expressionRel
  cases sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] with
  | mk sourceMiddle sourceResult =>
    rw [sourceRun] at expressionRel expressionPost
    cases flatRun : FlatSem.evaluate ⟨[]⟩ flat
        [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] with
    | mk flatMiddle flatResult =>
      rw [flatRun] at expressionRel expressionPost
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
          unfold DletOutcomeGrowing
          rw [sourceDec]
          exact ⟨flatMiddle, middleGenv, some (.raise flatValue), flatDec, states, .raise flatValue,
            rfl, .raise related, expressionPost.1, expressionPost.2.1, expressionPost.2.2⟩
        | abort kind =>
          have sourceDec : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
              (sourceMiddle, .err (.abort kind)) := by
            simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun]
          have flatDec := evaluateDlet_pattern_flat_error flat flatMiddle trace n start compMap gen location
            pattern expr (.abort kind) notAlias flatRun
          unfold DletOutcomeGrowing
          rw [sourceDec]
          exact ⟨flatMiddle, middleGenv, some (.abort kind), flatDec, states, _, rfl, .abort kind, trivial⟩
      | val values =>
        obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv expr sourceMiddle values sourceRun
        cases resultRel with
        | value valueRelations =>
          cases valueRelations with
          | cons valueRel tail =>
            cases tail with
            | nil =>
              rename_i flatValue
              obtain ⟨growth, current, generation, forward⟩ := expressionPost
              have envInv' := globalEnvInv_growth genv middleGenv growth compMap (fun _ => False) sourceEnv envInv
              cases matched : pmatch sourceEnv.c sourceMiddle.refs pattern value [] with
              | typeError =>
                apply (safe sourceMiddle).elim
                simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun, EvaluateHOL.headValue,
                  Flapjack.holHd, matched, EvaluateHOL.typeError]
              | noMatch =>
                have matchRel := patternSimulation middleGenv compMap compMap sourceEnv sourceMiddle flatMiddle
                  [] (fun _ => False) envInv' rfl current.1 current.2.1 states pattern value flatValue [] []
                  (by simpa [alistToNs, nsEmpty] using EnvRel.empty middleGenv) valueRel
                simp only [List.nil_append, matched] at matchRel
                have flatMatched : FlatSem.pmatch flatMiddle (compilePat compMap pattern) flatValue [] =
                    .noMatch := by
                  simpa using matchResultRel_cases middleGenv [] .noMatch _ matchRel
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
                have errorRel := (valueRel_lemmas middleGenv current.1).2.2.2.1
                unfold DletOutcomeGrowing
                rw [sourceDec]
                exact ⟨flatMiddle, middleGenv, some (.raise FlatSem.bindExnV), flatDec, states,
                  _, rfl, .raise errorRel, growth, current, generation, forward⟩
              | «match» bindings =>
                obtain ⟨finalGenv, finalFlat, sourceDec, compiled, flatDec, allocationGrowth, finalStates,
                  domain, finalEnv, finalInvariant⟩ :=
                  evaluateDlet_pattern_factored interp transform middleGenv start finish other source sourceMiddle flat
                    flatMiddle sourceEnv trace n compMap compMap gen location pattern expr value flatValue bindings
                    notAlias distinct wellformed sourceRun flatRun matched (fun _ => False) envInv' rfl valueRel current fits
                rw [compiled] at flatDec
                unfold DletOutcomeGrowing
                rw [sourceDec, compiled]
                exact ⟨_, _, none, flatDec, finalStates, rfl, domain, finalEnv,
                  growth.trans allocationGrowth, finalInvariant, generation, forward⟩

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
  obtain ⟨value, lookup⟩ : ∃ value, nsLookup sourceEnv.v id = some value := by
    cases found : nsLookup sourceEnv.v id with
    | some value => exact ⟨value, rfl⟩
    | none =>
      apply (safe source).elim
      simp [EvaluateHOL.evaluateDecs, EvaluateHOL.evaluate, AstHOL.patBindings, AstHOL.everyExp,
        oneConCheck, found, EvaluateHOL.typeError]
  have sourceDec : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) (.var id)] =
      (source, .val { v := nsSing name value, c := nsEmpty }) := by
    simp [EvaluateHOL.evaluateDecs, EvaluateHOL.evaluate, AstHOL.patBindings, AstHOL.everyExp,
      oneConCheck, lookup, pmatch, EvaluateHOL.headValue, Flapjack.holHd, nsSing, alistToNs]
  cases envInv with
  | intro _ _ _ values _ =>
    have unshadowed : ¬ (∃ x, False ∧ id = .short x) := by simp
    obtain ⟨_, _, _, idx, stored, nameTrace, compiledLookup, bound, slot, related⟩ :=
      values id value unshadowed lookup
    have compiled : compileDecs trace n start compMap gen [.dlet location (.pvar name) (.var id)] =
        (n, start, { v := nsSing name (.glob nameTrace idx), c := nsEmpty }, gen, []) := by
      simp [compileDecs, simpleDlet, compiledLookup, nsSing, alistToNs]
    obtain ⟨valueDomain, valueModules⟩ := alistToNs_domains_eq (M := ModN)
      [(name, VarName.glob nameTrace idx)] [(name, value)] (fun _ => Iff.rfl)
    unfold DletOutcomeGrowing
    rw [sourceDec, compiled]
    exact ⟨flat, genv, none, by simp [FlatSem.evaluateDecs], invariant.2.2.1, rfl,
      ⟨valueDomain, valueModules, envDomainEq_empty.2.2⟩,
      globalEnvInv_alias genv name idx nameTrace value stored bound slot related,
      GlobalGrowth.refl genv, invariant, generation, oracForwardRel_refl interp source.evalState⟩

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
  have safe : ∀ last, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (last, .err (.abort .typeError)) := by
    intro last bad
    exact notTypeError (congrArg Prod.snd (sourceRun.symm.trans bad))
  have count := compileDecs_numBindings trace n start env gen [.dlet location pattern expr]
    n' next nextEnv nextGen flatDecs compiled
  have slots : start.vidx + numBindings (.dlet location pattern expr) ≤ finish.vidx := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at count
    have finalBound := bounded.1
    omega
  have fits : start.vidx + (match simpleDlet pattern expr with
      | some _ => 0 | none => (AstHOL.patBindings pattern).length) ≤ finish.vidx := by
    cases found : simpleDlet pattern expr <;> simpa [numBindings.eq_1, found] using slots
  have outcome := evaluateDlet_growing interp transform genv start finish other source flat sourceEnv trace n
    env gen location pattern expr safe envInv invariant generation expressionStep fits
  unfold DletOutcomeGrowing at outcome
  rw [sourceRun, compiled] at outcome
  obtain ⟨flatLast, finalGenv, flatError, flatRun, states, post⟩ := outcome
  refine ⟨flatLast, finalGenv, flatError, flatRun, states, ?_⟩
  cases result with
  | val resultEnv =>
    obtain ⟨noError, domain, finalEnvInv, growth, finalInvariant, finalGeneration, forward⟩ := post
    refine ⟨fun _ => ⟨finalInvariant, forward, growth⟩, ?_, ?_⟩
    · intro returnedEnv same
      cases same
      exact ⟨noError, domain, finalGeneration, finalEnvInv⟩
    · intro error impossible
      cases impossible
  | err error =>
    obtain ⟨flatErr, isError, related, effects⟩ := post
    refine ⟨?_, ?_, ?_⟩
    · intro notAbort
      cases error with
      | abort kind => exact False.elim notAbort
      | raise value =>
        obtain ⟨growth, postInvariant, _, forward⟩ := effects
        have progress := OracleInvariant.compileDecs_idxPrev trace n start env gen
          [.dlet location pattern expr] n' next nextEnv nextGen flatDecs compiled
        have advanced := invariantIdxRangeShrink interp transform gen finalGenv start next finish other
          sourceLast flatLast ⟨postInvariant, progress, bounded⟩
        have store : nextGen = gen := by
          simpa only [compiled] using compileDlet_generationStore trace n start env gen location pattern expr
        exact ⟨by simpa only [store] using advanced, forward, growth⟩
    · intro returnedEnv impossible
      cases impossible
    · intro error' same
      cases same
      refine ⟨flatErr, isError, ?_⟩
      cases related with
      | raise valueRel => exact .raise valueRel
      | abort kind => exact .abort kind

end Flapjack.Compiler.Backend.SourceToFlat
