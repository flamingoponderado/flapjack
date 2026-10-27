import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDenv
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternRows
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.AllocDefsLookup

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

/-- A safe declaration whose expression succeeds cannot have a pattern
matching type error. -/
theorem dlet_match_noTypeError_of_safe {F : Type} (source middle : SemanticPrimitivesHOL.State F)
    (sourceEnv : SemEnv Value) (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (value : Value)
    (safe : ∀ next, EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] ≠
      (next, .err (.abort .typeError)))
    (sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] = (middle, .val [value])) :
    pmatch sourceEnv.c middle.refs pattern value [] ≠ .typeError := by
  obtain ⟨distinct, wellformed⟩ := dlet_conditions_of_safe source sourceEnv location pattern expr safe
  intro failed
  have bad : EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
      (middle, .err (.abort .typeError)) := by
    simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun, EvaluateHOL.headValue,
      Flapjack.holHd, failed, EvaluateHOL.typeError]
  exact safe middle bad

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

/-- A non-alias variable pattern stores a successfully evaluated expression
in its reserved global slot. The expression run is the induction hypothesis. -/
theorem evaluateDlet_var_flat {C F : Type} (flat middle : FlatSem.State C F)
    (trace : List VarN) (n : Nat) (next : NextIndices) (compMap : Environment)
    (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (name : VarN) (expr : AstHOL.Exp) (value : FlatSem.Value)
    (notAlias : simpleDlet (.pvar name) expr = none)
    (expressionRun : FlatSem.evaluate ⟨[]⟩ flat [compileExp (name :: trace) compMap expr] =
      (middle, .val [value]))
    (empty : middle.globals[next.vidx]? = some none) :
    FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location (.pvar name) expr]).2.2.2.2 =
      ({ middle with globals := middle.globals.set next.vidx (some value) }, none) := by
  let initialEnv : FlatSem.Environment FlatSem.Value := ⟨[]⟩
  let body : FlatLang.Exp := .app .none (.globalVarInit next.vidx) [.varLocal .none name]
  have bound : middle.clock ≤ flat.clock := FlatSem.evaluate_clock_spec.1 _ _ _ _ _ expressionRun
  have fixed : FlatSem.fixClock flat (middle, (Result.val [value] : Result (List FlatSem.Value) FlatSem.Value)) =
      (middle, .val [value]) := by simp [FlatSem.fixClock, Nat.min_eq_right bound]
  have selection : FlatSem.selectRow middle [(.pvar name, body)] value FlatSem.bindExnV =
      .ok ([(name, value)], body) := by
    simp [FlatSem.selectRow, FlatSem.pmatchRows, FlatSem.pmatch, FlatLang.patBindings]
  have initRun : FlatSem.evaluate ⟨[(name, value)]⟩ middle [body] =
      ({ middle with globals := middle.globals.set next.vidx (some value) }, .val [FlatSem.unitValue]) := by
    exact evaluate_globalVarInit _ middle name value next.vidx (by simp) empty
  have matRun : FlatSem.evaluate initialEnv flat
      [.mat .none (compileExp (name :: trace) compMap expr) [(.pvar name, body)]] =
      ({ middle with globals := middle.globals.set next.vidx (some value) }, .val [FlatSem.unitValue]) := by
    rw [FlatSem.evaluate, expressionRun, fixed]
    simp (config := { zeta := false })
    have selection' := selection
    dsimp only [body] at selection'
    rw [selection']
    simpa [body, initialEnv] using initRun
  simp only [compileDecs, notAlias, AstHOL.patBindings, List.reverse_cons, List.reverse_nil,
    List.nil_append, allocDefs, compilePat, makeVarls]
  rw [FlatSem.evaluateDecs]
  simp only [List.cons_append, List.nil_append]
  dsimp only [initialEnv, body] at matRun
  rw [matRun]
  simp [FlatSem.fixClock, FlatSem.unitValue, FlatSem.evaluateDecs, Nat.min_eq_right bound]

/-- If the compiled expression fails, the declaration stops before any
global initialization and preserves the expression's error and state. -/
theorem evaluateDlet_var_flat_error {C F : Type} (flat middle : FlatSem.State C F)
    (trace : List VarN) (n : Nat) (next : NextIndices) (compMap : Environment)
    (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (name : VarN) (expr : AstHOL.Exp) (error : ErrorResult FlatSem.Value)
    (notAlias : simpleDlet (.pvar name) expr = none)
    (expressionRun : FlatSem.evaluate ⟨[]⟩ flat [compileExp (name :: trace) compMap expr] =
      (middle, .err error)) :
    FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location (.pvar name) expr]).2.2.2.2 =
      (middle, some error) := by
  have bound : middle.clock ≤ flat.clock := FlatSem.evaluate_clock_spec.1 _ _ _ _ _ expressionRun
  simp only [compileDecs, notAlias, AstHOL.patBindings, List.reverse_cons, List.reverse_nil,
    List.nil_append, allocDefs, compilePat, makeVarls, List.cons_append]
  simp [FlatSem.evaluateDecs, FlatSem.evaluate, expressionRun, FlatSem.fixClock, Nat.min_eq_right bound]

/-- A failing source expression and its expression induction hypothesis give
related declaration errors, with no global slot initialized. -/
theorem evaluateDlet_var_error {C F : Type} (genv : GlobalEnv)
    (source sourceMiddle : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (name : VarN) (expr : AstHOL.Exp) (error : ErrorResult Value)
    (notAlias : simpleDlet (.pvar name) expr = none)
    (wellformed : AstHOL.everyExp (oneConCheck sourceEnv.c) expr = true)
    (sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] = (sourceMiddle, .err error))
    (expressionSim : ExprSim genv compMap (name :: trace) sourceEnv ⟨[]⟩ source flat expr) :
    ∃ flatMiddle flatError,
      EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) expr] =
        (sourceMiddle, .err error) ∧
      FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location (.pvar name) expr]).2.2.2.2 =
        (flatMiddle, some flatError) ∧
      EvalResultRel genv (.err error) (.err flatError) ∧ StateRel genv sourceMiddle flatMiddle := by
  unfold ExprSim at expressionSim
  rw [sourceRun] at expressionSim
  cases flatRun : FlatSem.evaluate ⟨[]⟩ flat [compileExp (name :: trace) compMap expr] with
  | mk flatMiddle flatResult =>
    rw [flatRun] at expressionSim
    obtain ⟨resultRel, states⟩ := expressionSim
    cases resultRel with
    | raise valueRel =>
      refine ⟨flatMiddle, .raise _, ?_, ?_, .raise valueRel, states⟩
      · simp [EvaluateHOL.evaluateDecs, AstHOL.patBindings, wellformed, sourceRun]
      · exact evaluateDlet_var_flat_error flat flatMiddle trace n next compMap gen location name expr _ notAlias flatRun
    | abort kind =>
      refine ⟨flatMiddle, .abort kind, ?_, ?_, .abort kind, states⟩
      · simp [EvaluateHOL.evaluateDecs, AstHOL.patBindings, wellformed, sourceRun]
      · exact evaluateDlet_var_flat_error flat flatMiddle trace n next compMap gen location name expr _ notAlias flatRun

/-- A non-alias variable declaration simulates a successful expression run,
then adds the related value to its reserved global slot. The expression runs
and post-expression invariant are the expression induction hypothesis. -/
theorem evaluateDlet_var_success {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source sourceMiddle : SemanticPrimitivesHOL.State F) (flat flatMiddle : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (compMap : Environment)
    (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (name : VarN) (expr : AstHOL.Exp) (value : Value) (flatValue : FlatSem.Value)
    (notAlias : simpleDlet (.pvar name) expr = none)
    (wellformed : AstHOL.everyExp (oneConCheck sourceEnv.c) expr = true)
    (sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] = (sourceMiddle, .val [value]))
    (flatRun : FlatSem.evaluate ⟨[]⟩ flat [compileExp (name :: trace) compMap expr] =
      (flatMiddle, .val [flatValue]))
    (related : ValueRel genv value flatValue)
    (invariant : OracleInvariant.factoredInvariant interp transform gen genv
      (start, finish, other) sourceMiddle flatMiddle)
    (fits : start.vidx + 1 ≤ finish.vidx) :
    let newGenv := { genv with v := genv.v.set start.vidx (some flatValue) }
    let newFlat := { flatMiddle with globals := flatMiddle.globals.set start.vidx (some flatValue) }
    let newNext := { start with vidx := start.vidx + 1 }
    EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) expr] =
      (sourceMiddle, .val { v := nsSing name value, c := nsEmpty }) ∧
    FlatSem.evaluateDecs flat (compileDecs trace n start compMap gen
      [.dlet location (.pvar name) expr]).2.2.2.2 = (newFlat, none) ∧
    GlobalEnvInv newGenv { v := nsSing name (.glob omTra start.vidx), c := nsEmpty }
      (fun _ => False) { v := nsSing name value, c := nsEmpty } ∧
    OracleInvariant.factoredInvariant interp transform gen newGenv (newNext, finish, other) sourceMiddle newFlat ∧
    GlobalGrowth genv newGenv := by
  have empty := factoredInvariant_nextSlot_blank interp transform gen genv start finish other
    sourceMiddle flatMiddle invariant fits
  have bound : start.vidx < flatMiddle.globals.length := (List.getElem?_eq_some_iff.mp empty).1
  have globals : genv.v = flatMiddle.globals := invariant.2.2.2.2.2.2.1
  have genBound : start.vidx < genv.v.length := by simpa [globals] using bound
  have growth := GlobalGrowth.fillSlot genv start.vidx flatValue (by simpa [globals] using empty)
  have slot : (genv.v.set start.vidx (some flatValue))[start.vidx]?.getD none = some flatValue := by
    simp [genBound]
  have nextRelated := valueRel_growth genv _ growth value flatValue related
  refine ⟨?_, evaluateDlet_var_flat flat flatMiddle trace n start compMap gen location name expr flatValue
    notAlias flatRun empty, globalEnvInv_alias _ name start.vidx omTra value flatValue (by simpa using genBound)
    slot nextRelated, ?_, growth⟩
  · simp [EvaluateHOL.evaluateDecs, AstHOL.patBindings, wellformed, sourceRun, pmatch,
      EvaluateHOL.headValue, Flapjack.holHd, nsSing, alistToNs]
  · exact factoredInvariant_fillSlot interp transform gen genv start finish other sourceMiddle flatMiddle
      flatValue invariant fits

/-- A successful source pattern match supplies the bindings used by the
generated declaration initializer. After the reserved block is filled, those
bindings satisfy the global environment invariant. -/
theorem evaluateDlet_pattern_initializer {C F : Type} (genv : GlobalEnv)
    (compMap compMap2 : Environment) (sourceEnv : SemEnv Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (shadowers : VarN → Prop) (envInv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (mapsEq : compMap2.c = compMap.c) (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (states : StateRel genv sourceState flatState) (globals : flatState.globals = genv.v)
    (pattern : Pat) (sourceValue : Value) (flatValue : FlatSem.Value)
    (valueRel : ValueRel genv sourceValue flatValue) (bindings : List (VarN × Value))
    (matched : pmatch sourceEnv.c sourceState.refs pattern sourceValue [] = .match bindings)
    (distinct : (AstHOL.patBindings pattern).Nodup) (pre post : List (Option FlatSem.Value))
    (slots : flatState.globals = pre ++ (List.replicate (AstHOL.patBindings pattern).length none ++ post))
    (n : Nat) :
    ∃ flatBindings,
      FlatSem.pmatch flatState (compilePat compMap pattern) flatValue [] = .match flatBindings ∧
      EnvRel genv (alistToNs bindings) flatBindings ∧
      flatBindings.map Prod.fst = AstHOL.patBindings pattern ∧
      let finalSlots := pre ++ (flatBindings.reverse.map (fun p => some p.2) ++ post)
      let finalGenv := { genv with v := finalSlots }
      let finalFlat := { flatState with globals := finalSlots }
      FlatSem.evaluate ⟨flatBindings⟩ flatState
        [makeVarls 0 .none pre.length (AstHOL.patBindings pattern).reverse] =
          (finalFlat, .val [FlatSem.unitValue]) ∧
      GlobalGrowth genv finalGenv ∧ StateRel finalGenv sourceState finalFlat ∧
      GlobalEnvInv finalGenv
        { emptyEnv with v := alistToNs (allocDefs (n + 4) pre.length (AstHOL.patBindings pattern).reverse) }
        (fun _ => False) ⟨alistToNs bindings, nsEmpty⟩ := by
  obtain ⟨flatBindings, flatMatch, related, names⟩ :=
    pmatch_success_sourceBindings genv compMap compMap2 sourceEnv sourceState flatState shadowers envInv
      mapsEq ok typesOk states pattern sourceValue flatValue valueRel bindings matched
  have namesRelated : bindings.map Prod.fst = flatBindings.map Prod.fst := by
    have pairs := (envRel_alist_iff genv bindings flatBindings).mp related
    clear matched flatMatch related names
    induction pairs with
    | nil => rfl
    | cons head tail ih => simp only [List.map_cons, head.1, ih]
  have bindingsDistinct : (bindings.map Prod.fst).Nodup := by simpa [namesRelated, names] using distinct
  have lengthEq : flatBindings.length = (AstHOL.patBindings pattern).length := by
    simpa using congrArg List.length names
  have flatSlots : flatState.globals = pre ++ (List.replicate flatBindings.length none ++ post) := by
    simpa [lengthEq] using slots
  have initialized := evaluate_makeVarls_globalEnvInv genv bindings flatBindings related bindingsDistinct
    sourceState flatState states globals pre post flatSlots 0 .none
  refine ⟨flatBindings, flatMatch, related, names, ?_⟩
  dsimp only
  rw [allocDefs_ignoreCounter (AstHOL.patBindings pattern).reverse (n + 4) 0 pre.length]
  simpa [List.map_reverse, names, Function.comp_def] using initialized

/-- A successful flat expression and pattern match run the generated
initializer as the body of the declaration's match expression. -/
theorem evaluateDlet_pattern_flat_success {C F : Type}
    (flat middle last : FlatSem.State C F) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap : Environment) (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (pattern : Pat) (expr : AstHOL.Exp) (value : FlatSem.Value) (bindings : List (VarN × FlatSem.Value))
    (notAlias : simpleDlet pattern expr = none) (distinct : (AstHOL.patBindings pattern).Nodup)
    (expressionRun : FlatSem.evaluate ⟨[]⟩ flat
      [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] = (middle, .val [value]))
    (matched : FlatSem.pmatch middle (compilePat compMap pattern) value [] = .match bindings)
    (initializerRun : FlatSem.evaluate ⟨bindings⟩ middle
      [makeVarls 0 .none next.vidx (AstHOL.patBindings pattern).reverse] = (last, .val [FlatSem.unitValue])) :
    FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location pattern expr]).2.2.2.2 =
      (last, none) := by
  let initialEnv : FlatSem.Environment FlatSem.Value := ⟨[]⟩
  let body := makeVarls 0 .none next.vidx (AstHOL.patBindings pattern).reverse
  have bound : middle.clock ≤ flat.clock := FlatSem.evaluate_clock_spec.1 _ _ _ _ _ expressionRun
  have lastBound : last.clock ≤ flat.clock :=
    Nat.le_trans (FlatSem.evaluate_clock_spec.1 _ _ _ _ _ initializerRun) bound
  have fixed : FlatSem.fixClock flat (middle, (Result.val [value] : Result (List FlatSem.Value) FlatSem.Value)) =
      (middle, .val [value]) := by simp [FlatSem.fixClock, Nat.min_eq_right bound]
  have selection : FlatSem.selectRow middle [(compilePat compMap pattern, body)] value FlatSem.bindExnV =
      .ok (bindings, body) := by
    simp [FlatSem.selectRow, FlatSem.pmatchRows, matched, compilePat_bindings, distinct]
  have matRun : FlatSem.evaluate initialEnv flat
      [.mat .none (compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr)
        [(compilePat compMap pattern, body)]] = (last, .val [FlatSem.unitValue]) := by
    rw [FlatSem.evaluate, expressionRun, fixed]
    simp (config := { zeta := false })
    have selection' := selection
    dsimp only [body] at selection'
    rw [selection']
    simpa [body, initialEnv] using initializerRun
  simp only [compileDecs, notAlias]
  rw [FlatSem.evaluateDecs]
  dsimp only [initialEnv, body] at matRun
  rw [matRun]
  simp [FlatSem.fixClock, FlatSem.unitValue, FlatSem.evaluateDecs, Nat.min_eq_right lastBound]

/-- A nonmatching flat declaration pattern raises the bind exception before
running the global initializer. -/
theorem evaluateDlet_pattern_flat_noMatch {C F : Type}
    (flat middle : FlatSem.State C F) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap : Environment) (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (pattern : Pat) (expr : AstHOL.Exp) (value : FlatSem.Value)
    (notAlias : simpleDlet pattern expr = none)
    (expressionRun : FlatSem.evaluate ⟨[]⟩ flat
      [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] = (middle, .val [value]))
    (matched : FlatSem.pmatch middle (compilePat compMap pattern) value [] = .noMatch) :
    FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location pattern expr]).2.2.2.2 =
      (middle, some (.raise FlatSem.bindExnV)) := by
  let body := makeVarls 0 .none next.vidx (AstHOL.patBindings pattern).reverse
  have bound : middle.clock ≤ flat.clock := FlatSem.evaluate_clock_spec.1 _ _ _ _ _ expressionRun
  have fixed : FlatSem.fixClock flat (middle, (Result.val [value] : Result (List FlatSem.Value) FlatSem.Value)) =
      (middle, .val [value]) := by simp [FlatSem.fixClock, Nat.min_eq_right bound]
  have selection : FlatSem.selectRow middle [(compilePat compMap pattern, body)] value FlatSem.bindExnV =
      .error (.raise FlatSem.bindExnV) := by
    simp [FlatSem.selectRow, FlatSem.pmatchRows, matched]
  have matRun : FlatSem.evaluate ⟨[]⟩ flat
      [.mat .none (compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr)
        [(compilePat compMap pattern, body)]] = (middle, .err (.raise FlatSem.bindExnV)) := by
    rw [FlatSem.evaluate, expressionRun, fixed]
    simp (config := { zeta := false })
    have selection' := selection
    dsimp only [body] at selection'
    rw [selection']
  simp only [compileDecs, notAlias]
  rw [FlatSem.evaluateDecs]
  dsimp only [body] at matRun
  rw [matRun]
  simp [FlatSem.fixClock, Nat.min_eq_right bound]

/-- A source pattern mismatch produces related bind exceptions and retains
the post-expression factored invariant in both evaluators. -/
theorem evaluateDlet_pattern_noMatch {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (idxs : NextIndices × NextIndices × Set (Nat × IndexKind))
    (source sourceMiddle : SemanticPrimitivesHOL.State F) (flat flatMiddle : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap compMap2 : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (value : Value) (flatValue : FlatSem.Value)
    (notAlias : simpleDlet pattern expr = none) (distinct : (AstHOL.patBindings pattern).Nodup)
    (wellformed : AstHOL.everyExp (oneConCheck sourceEnv.c) expr = true)
    (sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] = (sourceMiddle, .val [value]))
    (flatRun : FlatSem.evaluate ⟨[]⟩ flat
      [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] = (flatMiddle, .val [flatValue]))
    (matched : pmatch sourceEnv.c sourceMiddle.refs pattern value [] = .noMatch)
    (shadowers : VarN → Prop) (envInv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (mapsEq : compMap2.c = compMap.c) (valueRel : ValueRel genv value flatValue)
    (invariant : factoredInvariant interp transform gen genv idxs sourceMiddle flatMiddle) :
    EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
      (sourceMiddle, .err (.raise SemanticPrimitivesHOL.bindExnV)) ∧
    FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location pattern expr]).2.2.2.2 =
      (flatMiddle, some (.raise FlatSem.bindExnV)) ∧
    ValueRel genv SemanticPrimitivesHOL.bindExnV FlatSem.bindExnV ∧
    StateRel genv sourceMiddle flatMiddle ∧
    factoredInvariant interp transform gen genv idxs sourceMiddle flatMiddle := by
  have ok := invariant.1
  have typesOk := invariant.2.1
  have states := invariant.2.2.1
  have matchRel := patternSimulation genv compMap compMap2 sourceEnv sourceMiddle flatMiddle [] shadowers
    envInv mapsEq ok typesOk states pattern value flatValue [] []
    (by simpa [alistToNs, nsEmpty] using EnvRel.empty genv) valueRel
  simp only [List.nil_append, matched] at matchRel
  have flatMatched : FlatSem.pmatch flatMiddle (compilePat compMap pattern) flatValue [] = .noMatch := by
    cases flatMatch : FlatSem.pmatch flatMiddle (compilePat compMap pattern) flatValue [] <;>
      simp_all [MatchResultRel]
  refine ⟨?_, evaluateDlet_pattern_flat_noMatch flat flatMiddle trace n next compMap gen location pattern expr
    flatValue notAlias flatRun flatMatched, (exceptionValues_related genv ok).2.2.1, states, invariant⟩
  simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun, matched,
    EvaluateHOL.headValue, Flapjack.holHd]

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

/-- The expression induction hypothesis supplies related errors for a
non-alias declaration with any source-safe pattern. -/
theorem evaluateDlet_pattern_error {C F : Type} (genv : GlobalEnv)
    (source sourceMiddle : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap : Environment) (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (pattern : Pat) (expr : AstHOL.Exp) (error : ErrorResult Value)
    (notAlias : simpleDlet pattern expr = none) (distinct : (AstHOL.patBindings pattern).Nodup)
    (wellformed : AstHOL.everyExp (oneConCheck sourceEnv.c) expr = true)
    (sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] = (sourceMiddle, .err error))
    (expressionSim : ExprSim genv compMap ((AstHOL.patBindings pattern).reverse ++ trace)
      sourceEnv ⟨[]⟩ source flat expr) :
    ∃ flatMiddle flatError,
      EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] = (sourceMiddle, .err error) ∧
      FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location pattern expr]).2.2.2.2 =
        (flatMiddle, some flatError) ∧
      EvalResultRel genv (.err error) (.err flatError) ∧ StateRel genv sourceMiddle flatMiddle := by
  unfold ExprSim at expressionSim
  rw [sourceRun] at expressionSim
  cases flatRun : FlatSem.evaluate ⟨[]⟩ flat
      [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] with
  | mk flatMiddle flatResult =>
    rw [flatRun] at expressionSim
    obtain ⟨resultRel, states⟩ := expressionSim
    cases resultRel with
    | raise valueRel =>
      refine ⟨flatMiddle, .raise _, ?_, ?_, .raise valueRel, states⟩
      · simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun]
      · exact evaluateDlet_pattern_flat_error flat flatMiddle trace n next compMap gen location pattern expr _
          notAlias flatRun
    | abort kind =>
      refine ⟨flatMiddle, .abort kind, ?_, ?_, .abort kind, states⟩
      · simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun]
      · exact evaluateDlet_pattern_flat_error flat flatMiddle trace n next compMap gen location pattern expr _
          notAlias flatRun

/-- Successful evaluation and matching of a non-alias declaration pattern
produce related source and flat declarations and the resulting global
environment invariant. The expression runs and post-expression relations are
the expression induction hypothesis. -/
theorem evaluateDlet_pattern_success {C F : Type} (genv : GlobalEnv)
    (source sourceMiddle : SemanticPrimitivesHOL.State F) (flat flatMiddle : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (next : NextIndices)
    (compMap compMap2 : Environment) (gen : EnvironmentGenerationStore)
    (location : Flapjack.Misc.Location.Locs) (pattern : Pat) (expr : AstHOL.Exp)
    (value : Value) (flatValue : FlatSem.Value) (bindings : List (VarN × Value))
    (notAlias : simpleDlet pattern expr = none) (distinct : (AstHOL.patBindings pattern).Nodup)
    (wellformed : AstHOL.everyExp (oneConCheck sourceEnv.c) expr = true)
    (sourceRun : EvaluateHOL.evaluate source sourceEnv [expr] = (sourceMiddle, .val [value]))
    (flatRun : FlatSem.evaluate ⟨[]⟩ flat
      [compileExp ((AstHOL.patBindings pattern).reverse ++ trace) compMap expr] = (flatMiddle, .val [flatValue]))
    (matched : pmatch sourceEnv.c sourceMiddle.refs pattern value [] = .match bindings)
    (shadowers : VarN → Prop) (envInv : GlobalEnvInv genv compMap2 shadowers sourceEnv)
    (mapsEq : compMap2.c = compMap.c) (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (states : StateRel genv sourceMiddle flatMiddle) (globals : flatMiddle.globals = genv.v)
    (valueRel : ValueRel genv value flatValue) (pre post : List (Option FlatSem.Value))
    (slots : flatMiddle.globals = pre ++ (List.replicate (AstHOL.patBindings pattern).length none ++ post))
    (prefixLength : pre.length = next.vidx) :
    ∃ flatBindings : List (VarN × FlatSem.Value),
      let finalSlots := pre ++ (flatBindings.reverse.map (fun p => some p.2) ++ post)
      let finalGenv := { genv with v := finalSlots }
      let finalFlat := { flatMiddle with globals := finalSlots }
      flatBindings.map Prod.fst = AstHOL.patBindings pattern ∧
      EvaluateHOL.evaluateDecs source sourceEnv [.dlet location pattern expr] =
        (sourceMiddle, .val ⟨alistToNs bindings, nsEmpty⟩) ∧
      FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location pattern expr]).2.2.2.2 =
        (finalFlat, none) ∧
      GlobalGrowth genv finalGenv ∧ StateRel finalGenv sourceMiddle finalFlat ∧
      GlobalEnvInv finalGenv
        { emptyEnv with v := alistToNs (allocDefs (n + 4) next.vidx (AstHOL.patBindings pattern).reverse) }
        (fun _ => False) ⟨alistToNs bindings, nsEmpty⟩ := by
  obtain ⟨flatBindings, flatMatch, _, names, initRun, growth, finalStates, finalEnv⟩ :=
    evaluateDlet_pattern_initializer genv compMap compMap2 sourceEnv sourceMiddle flatMiddle shadowers envInv mapsEq
      ok typesOk states globals pattern value flatValue valueRel bindings matched distinct pre post slots n
  refine ⟨flatBindings, names, ?_, ?_, growth, finalStates, ?_⟩
  · simp [EvaluateHOL.evaluateDecs, distinct, wellformed, sourceRun, matched,
      EvaluateHOL.headValue, Flapjack.holHd]
  · apply evaluateDlet_pattern_flat_success flat flatMiddle _ trace n next compMap gen location pattern expr
      flatValue flatBindings notAlias distinct flatRun flatMatch
    simpa [prefixLength] using initRun
  · simpa [prefixLength] using finalEnv

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
    ∃ (flatBindings : List (VarN × FlatSem.Value)) (pre post : List (Option FlatSem.Value)),
      let finalSlots := pre ++ (flatBindings.reverse.map (fun p => some p.2) ++ post)
      let finalGenv := { genv with v := finalSlots }
      let finalFlat := { flatMiddle with globals := finalSlots }
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
      GlobalEnvInv finalGenv
        { emptyEnv with v := alistToNs (allocDefs (n + 4) start.vidx (AstHOL.patBindings pattern).reverse) }
        (fun _ => False) ⟨alistToNs bindings, nsEmpty⟩ ∧
      factoredInvariant interp transform gen finalGenv (finalNext, finish, other) sourceMiddle finalFlat := by
  have invariantCopy := invariant
  obtain ⟨ok, typesOk, states, range, _, _, globals, _, _, fin⟩ := invariantCopy
  obtain ⟨pre, post, genSlots, prefixLength⟩ := idxRangeRel_blank interp genv sourceMiddle.nextTypeStamp
    sourceMiddle.nextExnStamp sourceMiddle.evalState start finish other (AstHOL.patBindings pattern).length
      ⟨range, by simpa [globals] using fin, by omega⟩
  have slots : flatMiddle.globals = pre ++ (List.replicate (AstHOL.patBindings pattern).length none ++ post) :=
    globals.symm.trans genSlots
  obtain ⟨flatBindings, names, sourceResult, flatResult, growth, finalStates, finalEnv⟩ :=
    evaluateDlet_pattern_success genv source sourceMiddle flat flatMiddle sourceEnv trace n start compMap compMap2
      gen location pattern expr value flatValue bindings notAlias distinct wellformed sourceRun flatRun matched
      shadowers envInv mapsEq ok typesOk states globals.symm valueRel pre post slots prefixLength
  have flatCount : flatBindings.length = (AstHOL.patBindings pattern).length := by
    simpa using congrArg List.length names
  have finalInvariant := factoredInvariant_fillBlock interp transform gen genv start finish other sourceMiddle
    flatMiddle (flatBindings.reverse.map Prod.snd) pre post invariant (by simpa [flatCount] using slots)
    prefixLength (by simpa [flatCount] using fits)
  refine ⟨flatBindings, pre, post, sourceResult, ?_, flatResult, growth, finalStates, finalEnv, ?_⟩
  · simp [compileDecs, notAlias, emptyEnv]
  · simpa [flatCount, List.map_map, Function.comp_def] using finalInvariant

/-- A literal declaration initializes its reserved flat global slot. -/
theorem evaluateDlet_literal_flat {C F : Type} (flat : FlatSem.State C F)
    (trace : List VarN) (n : Nat) (next : NextIndices) (compMap : Environment)
    (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs)
    (name : VarN) (lit : Lit) (empty : flat.globals[next.vidx]? = some none) :
    FlatSem.evaluateDecs flat (compileDecs trace n next compMap gen [.dlet location (.pvar name) (.lit lit)]).2.2.2.2 =
      ({ flat with globals := flat.globals.set next.vidx (some (.litv lit)) }, none) := by
  exact evaluateDlet_var_flat flat flat trace n next compMap gen location name (.lit lit) (.litv lit)
    (by rfl) (by simp [compileExp, FlatSem.evaluate]) empty

/-- A literal `val` declaration initializes its assigned global and advances
the factored invariant by one slot. Its returned source and compiler
environments are related at the grown global environment. -/
theorem evaluateDlet_literal_factored {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : SemanticPrimitivesHOL.State F) (flat : FlatSem.State C F)
    (sourceEnv : SemEnv Value) (trace : List VarN) (n : Nat) (compMap : Environment)
    (gen : EnvironmentGenerationStore) (location : Flapjack.Misc.Location.Locs) (name : VarN) (lit : Lit)
    (invariant : OracleInvariant.factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (fits : start.vidx + 1 ≤ finish.vidx) :
    let newGenv := { genv with v := genv.v.set start.vidx (some (.litv lit)) }
    let newFlat := { flat with globals := flat.globals.set start.vidx (some (.litv lit)) }
    let newNext := { start with vidx := start.vidx + 1 }
    EvaluateHOL.evaluateDecs source sourceEnv [.dlet location (.pvar name) (.lit lit)] =
      (source, .val { v := nsSing name (.litv lit), c := nsEmpty }) ∧
    compileDecs trace n start compMap gen [.dlet location (.pvar name) (.lit lit)] =
      (n + 4 + 1, newNext, { v := nsSing name (.glob omTra start.vidx), c := nsEmpty }, gen,
        [.mat .none (.lit .none lit)
          [(.pvar name, .app .none (.globalVarInit start.vidx) [.varLocal .none name])]]) ∧
    FlatSem.evaluateDecs flat (compileDecs trace n start compMap gen
      [.dlet location (.pvar name) (.lit lit)]).2.2.2.2 = (newFlat, none) ∧
    GlobalEnvInv newGenv { v := nsSing name (.glob omTra start.vidx), c := nsEmpty }
      (fun _ => False) { v := nsSing name (.litv lit), c := nsEmpty } ∧
    OracleInvariant.factoredInvariant interp transform gen newGenv (newNext, finish, other) source newFlat ∧
    GlobalGrowth genv newGenv := by
  have empty := factoredInvariant_nextSlot_blank interp transform gen genv start finish other source flat invariant fits
  have bound : start.vidx < flat.globals.length := (List.getElem?_eq_some_iff.mp empty).1
  have globals : genv.v = flat.globals := invariant.2.2.2.2.2.2.1
  have genBound : start.vidx < genv.v.length := by simpa [globals] using bound
  have growth := GlobalGrowth.fillSlot genv start.vidx (.litv lit) (by simpa [globals] using empty)
  have slot : (genv.v.set start.vidx (some (.litv lit)))[start.vidx]?.getD none = some (.litv lit) := by
    simp [genBound]
  refine ⟨?_, ?_, evaluateDlet_literal_flat flat trace n start compMap gen location name lit empty,
    globalEnvInv_alias _ name start.vidx omTra (.litv lit) (.litv lit) (by simpa using genBound)
      slot (.literal _ lit), ?_, growth⟩
  · simp [EvaluateHOL.evaluateDecs, EvaluateHOL.evaluate, AstHOL.patBindings, AstHOL.everyExp,
      oneConCheck, pmatch, EvaluateHOL.headValue, Flapjack.holHd, nsSing, alistToNs]
  · simp [compileDecs, simpleDlet, AstHOL.patBindings, allocDefs, compileExp, compilePat,
      makeVarls, nsSing, alistToNs]
  · exact factoredInvariant_fillSlot interp transform gen genv start finish other source flat (.litv lit) invariant fits

end Flapjack.Compiler.Backend.SourceToFlat
