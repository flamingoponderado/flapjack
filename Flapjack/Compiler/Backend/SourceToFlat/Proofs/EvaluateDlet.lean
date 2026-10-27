import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDenv
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl

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
