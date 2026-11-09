module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateOracle
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateOracleDisjoint
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownSubspt
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
public import Flapjack.SemanticPrimitivesProps.ResultRelation

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Source-shaped induction predicates for the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The expression conjunct of the source simulation, specialized at an
input program, environment and initial source state. This predicate is
Flapjack induction infrastructure and adds no simulation assumptions. -/
def KnownSimulationAt {C F : Type} (xs : List ClosLang.Exp) (env1full : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) : Prop :=
  ∀ (res1 : Result (List ClosSem.Value) ClosSem.Value) (s : State (Spt ValApprox × C) F)
    (env1 xenv1 env2 xenv2 : List ClosSem.Value) (t0 : State C F) (c : Config)
    (g0 g : Spt ValApprox) (aenv : List ValApprox) (eas : List (ClosLang.Exp × ValApprox)),
    evaluate xs env1full s0 = (res1, s) ∧
    knownListTotal c xs aenv g0 = (eas, g) ∧
    StateRel c (nextG s0) s0 t0 ∧ everyFnVarsNone xs ∧
    coEveryFnVarsNone s0.compileOracle ∧ mglobalsDisjoint s0.globals xs ∧
    oracleGapproxDisjoint (nextG s0) s0.compileOracle ∧ stateOracleMglobalsDisjoint s0 ∧
    (∀ e ∈ xs, esgcFree e) ∧ ssgcFree s0 ∧ (∀ v ∈ env1full, vsgcFree v) ∧
    List.Forall₂ ValApproxVal aenv env1 ∧ oracleStateSgcFree s0.compileOracle ∧
    globalsApproxSgcFree g0 ∧ (∀ a ∈ aenv, valApproxSgcFree a) ∧
    stateGlobalsApprox s0 (nextG s0) ∧ sptSubspt g0 g ∧ sptSubspt g (nextG s0) ∧
    oracleGapproxSubspt s0.compileOracle ∧ fvMax env1.length xs ∧
    List.Forall₂ (ValueRel c (nextG s0)) env1 env2 ∧ uniqueSetGlobals xs s0.compileOracle ∧
    isStateOracle (compileInc c) s0.compileOracle ∧ env1full = env1 ++ xenv1 ∧
    res1 ≠ .err (.abort .typeError) →
    ∃ (res2 : Result (List ClosSem.Value) ClosSem.Value) (t : State C F),
      evaluate (eas.map Prod.fst) (env2 ++ xenv2) t0 = (res2, t) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG s))) (ValueRel c (nextG s)) res1 res2 ∧
      StateRel c (nextG s) s t ∧ stateGlobalsApprox s (nextG s) ∧
      isStateOracle (compileInc c) s.compileOracle ∧ oracleGapproxDisjoint (nextG s) s.compileOracle

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Empty-program case of the original optimizer simulation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Nil {C F : Type} (env1full : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F)
    (res1 : Result (List ClosSem.Value) ClosSem.Value) (s : State (Spt ValApprox × C) F)
    (env1 xenv1 env2 xenv2 : List ClosSem.Value) (t0 : State C F) (c : Config)
    (g0 g : Spt ValApprox) (aenv : List ValApprox) (eas : List (ClosLang.Exp × ValApprox))
    (h : evaluate [] env1full s0 = (res1, s) ∧
      knownListTotal c [] aenv g0 = (eas, g) ∧
      StateRel c (nextG s0) s0 t0 ∧ everyFnVarsNone [] ∧
      coEveryFnVarsNone s0.compileOracle ∧ mglobalsDisjoint s0.globals [] ∧
      oracleGapproxDisjoint (nextG s0) s0.compileOracle ∧ stateOracleMglobalsDisjoint s0 ∧
      (∀ e ∈ ([] : List ClosLang.Exp), esgcFree e) ∧ ssgcFree s0 ∧ (∀ v ∈ env1full, vsgcFree v) ∧
      List.Forall₂ ValApproxVal aenv env1 ∧ oracleStateSgcFree s0.compileOracle ∧
      globalsApproxSgcFree g0 ∧ (∀ a ∈ aenv, valApproxSgcFree a) ∧
      stateGlobalsApprox s0 (nextG s0) ∧ sptSubspt g0 g ∧ sptSubspt g (nextG s0) ∧
      oracleGapproxSubspt s0.compileOracle ∧ fvMax env1.length [] ∧
      List.Forall₂ (ValueRel c (nextG s0)) env1 env2 ∧ uniqueSetGlobals [] s0.compileOracle ∧
      isStateOracle (compileInc c) s0.compileOracle ∧ env1full = env1 ++ xenv1 ∧
      res1 ≠ .err (.abort .typeError)) :
    ∃ (res2 : Result (List ClosSem.Value) ClosSem.Value) (t : State C F),
      evaluate (eas.map Prod.fst) (env2 ++ xenv2) t0 = (res2, t) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG s))) (ValueRel c (nextG s)) res1 res2 ∧
      StateRel c (nextG s) s t ∧ stateGlobalsApprox s (nextG s) ∧
      isStateOracle (compileInc c) s.compileOracle ∧ oracleGapproxDisjoint (nextG s) s.compileOracle := by
  obtain ⟨run, known, related, _, _, _, oracle, _, _, _, _, _, _, _, _, globals, _, _, _, _, _, _, stateOracle, _, _⟩ := h
  simp [evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  simp [knownListTotal] at known
  rcases known with ⟨rfl, rfl⟩
  exact ⟨.val [], t0, by simp [evaluate], by simp [resultRel], related, globals, stateOracle, oracle⟩

/-- Variable case of the original optimizer simulation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Var {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F) :
    KnownSimulationAt [.var trace index] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, _, _, _, oracle, _, _, _, _, _, _, _, _, globals,
    _, _, _, free, envRelated, _, stateOracle, envEq, _⟩ := h
  have bound : index < env1.length := (fvMaxVar env1.length index trace).1 free
  have lengths : env1.length = env2.length := envRelated.length_eq
  have targetBound : index < env2.length := by omega
  have valueRelated : ValueRel c (nextG s0) env1[index] env2[index] :=
    (List.forall₂_iff_get.mp envRelated).2 index bound targetBound
  have sourceLookup : env1full[index]? = some env1[index] := by
    rw [envEq, List.getElem?_append_left bound, List.getElem?_eq_getElem bound]
  have targetLookup : (env2 ++ xenv2)[index]? = some env2[index] := by
    rw [List.getElem?_append_left targetBound, List.getElem?_eq_getElem targetBound]
  simp [evaluate, sourceLookup] at run
  rcases run with ⟨rfl, rfl⟩
  simp [knownListTotal_var] at known
  rcases known with ⟨rfl, rfl⟩
  refine ⟨.val [env2[index]], t0, ?_, ?_, state, globals, stateOracle, oracle⟩
  · simp [evaluate, targetLookup]
  · exact .cons valueRelated .nil

/-- The application conjunct of the source simulation at fixed application
inputs. This is Flapjack induction infrastructure. -/
def KnownAppSimulationAt {C F : Type} (lopt1 : Option Nat) (f1 : ClosSem.Value)
    (args1 : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F) : Prop :=
  ∀ (res1 : Result (List ClosSem.Value) ClosSem.Value) (s : State (Spt ValApprox × C) F)
    (lopt2 : Option Nat) (f2 : ClosSem.Value) (args2 : List ClosSem.Value)
    (t0 : State C F) (c : Config) (argsopt : Option (List ClosSem.Value)),
    evaluateApp lopt1 f1 args1 s0 = (res1, s) ∧
    valueRelApp c (nextG s0) f1 f2 argsopt ∧
    oracleGapproxDisjoint (nextG s0) s0.compileOracle ∧ stateOracleMglobalsDisjoint s0 ∧
    ssgcFree s0 ∧ vsgcFree f1 ∧ (∀ v ∈ args1, vsgcFree v) ∧
    oracleStateSgcFree s0.compileOracle ∧ coEveryFnVarsNone s0.compileOracle ∧
    uniqueSetGlobals [] s0.compileOracle ∧ isStateOracle (compileInc c) s0.compileOracle ∧
    List.Forall₂ (ValueRel c (nextG s0)) args1 args2 ∧ StateRel c (nextG s0) s0 t0 ∧
    stateGlobalsApprox s0 (nextG s0) ∧ oracleGapproxSubspt s0.compileOracle ∧
    loptRel f2 args1.length lopt1 lopt2 ∧
    (argsopt.isSome → argsopt = some args1 ∧ args1 ≠ [] ∧ ∃ exp env,
      destClosure s0.maxApp lopt1 f1 args1 = some (.fullApp exp env [])) ∧
    res1 ≠ .err (.abort .typeError) →
    ∃ (res2 : Result (List ClosSem.Value) ClosSem.Value) (t : State C F),
      evaluateApp lopt2 f2 args2 t0 = (res2, t) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG s))) (ValueRel c (nextG s)) res1 res2 ∧
      StateRel c (nextG s) s t ∧ stateGlobalsApprox s (nextG s) ∧
      isStateOracle (compileInc c) s.compileOracle ∧ oracleGapproxDisjoint (nextG s) s.compileOracle

/-- Empty-argument application case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0AppNil {C F : Type} (lopt1 : Option Nat) (f1 : ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) : KnownAppSimulationAt lopt1 f1 [] s0 := by
  intro res1 s lopt2 f2 args2 t0 c argsopt h
  obtain ⟨run, relation, oracle, _, _, _, _, _, _, _, stateOracle, argsRel, state, globals,
    _, _, argsoptCondition, _⟩ := h
  simp [evaluateApp] at run
  rcases run with ⟨rfl, rfl⟩
  have argsEq : args2 = [] := by cases argsRel; rfl
  subst args2
  have noApprox : argsopt = none := by
    cases argsopt with
    | none => rfl
    | some values =>
      have impossible := argsoptCondition (by simp)
      simp at impossible
  subst argsopt
  have valueRel : ValueRel c (nextG s0) f1 f2 := by
    rw [valueRelAppNone] at relation
    exact relation
  exact ⟨.val [f2], t0, by simp [evaluateApp], .cons valueRel .nil,
    state, globals, stateOracle, oracle⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation
