import Flapjack.Compiler.Backend.SourceToFlat.Proofs.PatternSimulation

/-! Pattern-row prerequisites over the preliminary source-to-flat relations.
Full correspondence of these relations with HOL remains open. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- Compiling a pattern preserves the order of its bound variable names. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "pat_bindings_compile_pat"]
theorem compilePat_bindings (compMap : Environment) (pattern : Pat) :
    FlatLang.patBindings (compilePat compMap pattern) = AstHOL.patBindings pattern := by
  apply Pat.rec
    (motive_1 := fun p => FlatLang.patBindings (compilePat compMap p) = AstHOL.patBindings p)
    (motive_2 := fun ps => FlatLang.patsBindings (ps.map (compilePat compMap)) = AstHOL.patsBindings ps)
  case pany => simp [compilePat, FlatLang.patBindings, AstHOL.patBindings]
  case pvar => intro; simp [compilePat, FlatLang.patBindings, AstHOL.patBindings]
  case plit => intro; simp [compilePat, FlatLang.patBindings, AstHOL.patBindings]
  case pcon => intro name patterns ih; simpa [compilePat, FlatLang.patBindings, AstHOL.patBindings] using ih
  case pref => intro pattern ih; simpa [compilePat, FlatLang.patBindings, AstHOL.patBindings] using ih
  case pas => intro pattern name ih; simp [compilePat, FlatLang.patBindings, AstHOL.patBindings, ih]
  case ptannot => intro pattern typ ih; simpa [compilePat, AstHOL.patBindings] using ih
  case nil => rfl
  case cons =>
    intro pattern patterns head tail
    simp [FlatLang.patsBindings, AstHOL.patsBindings, head, tail]

/-- If every source pattern is type-compatible, matching the compiled rows
cannot fail with a flat pattern type error. This is Flapjack infrastructure
over the factored relations, not yet a reviewed port of the HOL theorem. -/
theorem canPmatchAll_rows_noTypeError {C F : Type} (genv : GlobalEnv)
    (compMap compMap2 : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (shadowers : VarN → Prop)
    (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv) (mapsEq : compMap2.c = compMap.c)
    (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (stateRel : StateRel genv sourceState flatState)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value) (valueRel : ValueRel genv source flat)
    (rows : List (Pat × AstHOL.Exp))
    (can : canPmatchAll sourceEnv.c sourceState.refs (rows.map Prod.fst) source = true) :
    FlatSem.pmatchRows (compilePes trace compMap rows) flatState flat ≠ .typeError := by
  induction rows with
  | nil => simp [compilePes, FlatSem.pmatchRows]
  | cons row rows ih =>
    obtain ⟨pattern, body⟩ := row
    have checks := can
    simp only [canPmatchAll, List.map_cons, List.all_cons, Bool.and_eq_true] at checks
    have related := patternSimulation genv compMap compMap2 sourceEnv sourceState flatState [] shadowers
      inv mapsEq ok typesOk stateRel pattern source flat [] [] (by simpa [alistToNs, nsEmpty] using EnvRel.empty genv) valueRel
    simp only [List.nil_append] at related
    have flatSafe : FlatSem.pmatch flatState (compilePat compMap pattern) flat [] ≠ .typeError := by
      cases sourceMatch : pmatch sourceEnv.c sourceState.refs pattern source [] <;>
        cases flatMatch : FlatSem.pmatch flatState (compilePat compMap pattern) flat [] <;>
        simp_all [MatchResultRel]
    have restSafe := ih checks.2
    simp only [compilePes, FlatSem.pmatchRows]
    cases flatMatch : FlatSem.pmatch flatState (compilePat compMap pattern) flat [] with
    | typeError => exact (flatSafe flatMatch).elim
    | noMatch => exact restSafe
    | «match» bindings =>
      cases restMatch : FlatSem.pmatchRows (compilePes trace compMap rows) flatState flat with
      | typeError => exact (restSafe restMatch).elim
      | noMatch => simp
      | «match» result => simp

/-- Select the first source pattern that matches. This comparison helper does
not perform the separate all-row type check or the duplicate-binding check. -/
def sourcePmatchRows {F : Type} (env : SemEnv SemanticPrimitivesHOL.Value)
    (state : SemanticPrimitivesHOL.State F) (value : SemanticPrimitivesHOL.Value) :
    List (Pat × AstHOL.Exp) → MatchResult (List (VarN × SemanticPrimitivesHOL.Value) × Pat × AstHOL.Exp)
  | [] => .noMatch
  | (pattern, body) :: rows =>
    match pmatch env.c state.refs pattern value [] with
    | .typeError => .typeError
    | .noMatch => sourcePmatchRows env state value rows
    | .match bindings => .match (bindings, pattern, body)

/-- Relate the selected source row to its compiled flat row and bindings. -/
def MatchRowsRel (genv : GlobalEnv) (compMap : Environment) (trace : List VarN) :
    MatchResult (List (VarN × SemanticPrimitivesHOL.Value) × Pat × AstHOL.Exp) →
    MatchResult (List (VarN × FlatSem.Value) × FlatLang.Pat × FlatLang.Exp) → Prop
  | .typeError, _ => True
  | .noMatch, .noMatch => True
  | .match (bindings, pattern, body), .match (flatBindings, flatPattern, flatBody) =>
    EnvRel genv (alistToNs bindings) flatBindings ∧
      flatPattern = compilePat compMap pattern ∧
      flatBody = compileExp trace { compMap with v := nsBindList (patTups .none (patBindings pattern)) compMap.v } body
  | _, _ => False

/-- All-row compatibility and pattern preservation identify the same first
matching row on both sides, with related pattern bindings. -/
theorem pmatchRows_related {C F : Type} (genv : GlobalEnv)
    (compMap compMap2 : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (sourceState : SemanticPrimitivesHOL.State F)
    (flatState : FlatSem.State C F) (shadowers : VarN → Prop)
    (inv : GlobalEnvInv genv compMap2 shadowers sourceEnv) (mapsEq : compMap2.c = compMap.c)
    (ok : genvCOk genv.c) (typesOk : genvCTysOk genv.c genv.tys)
    (stateRel : StateRel genv sourceState flatState)
    (source : SemanticPrimitivesHOL.Value) (flat : FlatSem.Value) (valueRel : ValueRel genv source flat)
    (rows : List (Pat × AstHOL.Exp))
    (can : canPmatchAll sourceEnv.c sourceState.refs (rows.map Prod.fst) source = true) :
    MatchRowsRel genv compMap trace (sourcePmatchRows sourceEnv sourceState source rows)
      (FlatSem.pmatchRows (compilePes trace compMap rows) flatState flat) := by
  induction rows with
  | nil => simp [sourcePmatchRows, compilePes, FlatSem.pmatchRows, MatchRowsRel]
  | cons row rows ih =>
    obtain ⟨pattern, body⟩ := row
    have checks := can
    simp only [canPmatchAll, List.map_cons, List.all_cons, Bool.and_eq_true] at checks
    have related := patternSimulation genv compMap compMap2 sourceEnv sourceState flatState [] shadowers
      inv mapsEq ok typesOk stateRel pattern source flat [] [] (by simpa [alistToNs, nsEmpty] using EnvRel.empty genv) valueRel
    simp only [List.nil_append] at related
    have restSafe := canPmatchAll_rows_noTypeError genv compMap compMap2 trace sourceEnv sourceState flatState
      shadowers inv mapsEq ok typesOk stateRel source flat valueRel rows checks.2
    have restRelated := ih checks.2
    cases sourceMatch : pmatch sourceEnv.c sourceState.refs pattern source [] <;>
      cases flatMatch : FlatSem.pmatch flatState (compilePat compMap pattern) flat [] <;>
      simp_all [sourcePmatchRows, compilePes, FlatSem.pmatchRows, MatchResultRel, MatchRowsRel]

end Flapjack.Compiler.Backend.SourceToFlat
