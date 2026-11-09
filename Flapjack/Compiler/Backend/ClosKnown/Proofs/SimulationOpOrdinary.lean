module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationOpForce
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationGlobal
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyCode

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Ordinary operation cases of known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Ordinary
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps

/-- Ordinary operations with no global writes preserve the current global
approximation and compiler oracle. This is Flapjack proof infrastructure. -/
theorem ordinaryOpStateInvariants {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (xs : List ClosLang.Exp) (env : List Value) (s0 middle final : State (Spt ValApprox × C) F)
    (argResult result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (noWrites : ∀ k, opGlobalBag op k = 0)
    (argsRun : evaluate xs env s0 = (argResult, middle))
    (run : evaluate [.op trace op xs] env s0 = (result, final))
    (globals : stateGlobalsApprox middle (nextG middle))
    (oracle : isStateOracle (compileInc c) middle.compileOracle)
    (oracleDisjoint : oracleGapproxDisjoint (nextG middle) middle.compileOracle) :
    nextG final = nextG middle ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  rw [evaluate_ordinaryOp_eq trace op xs env s0 notInstall notForce, argsRun] at run
  cases argResult with
  | err error =>
    simp at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, globals, oracle, oracleDisjoint⟩
  | val values =>
    cases app : doApp op values.reverse middle with
    | err error =>
      simp [app] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨rfl, globals, oracle, oracleDisjoint⟩
    | val pair =>
      rcases pair with ⟨value, next⟩
      simp [app] at run
      rcases run with ⟨rfl, rfl⟩
      have oracleEq := (doApp_codeOracle op values.reverse middle next value app).2
      have frame := doAppMglobals op values.reverse middle next value app
      have globalNext : stateGlobalsApprox next (nextG middle) := by
        intro k value approx h
        apply globals k value approx
        exact ⟨frame.2 k value ⟨h.1, by simp [noWrites]⟩, h.2⟩
      have nextEq : nextG next = nextG middle := by simp [nextG, oracleEq]
      exact ⟨nextEq, by simpa [nextEq] using globalNext, by simpa [oracleEq] using oracle,
        by simpa [nextEq, oracleEq] using oracleDisjoint⟩

/-- Optimizer output selection for a primitive operation. -/
def selectedOutput (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (a : ValApprox) (args : List ClosLang.Exp) : ClosLang.Exp :=
  match op, a with
  | .globOp (.global _), .int i => .op trace (.intOp (.const i)) args
  | .globOp (.global _), .tuple tag [] => .op trace (.blockOp (.cons tag)) args
  | _, _ => ClosOp.smartOp trace op args

/-- Non-global-read operations use the normal smart-operation output. This
is Flapjack proof infrastructure. -/
theorem ordinaryKnownOutput (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (a : ValApprox) (args : List ClosLang.Exp)
    (notGlobalRead : ∀ index, op ≠ .globOp (.global index)) :
    selectedOutput trace op a args = ClosOp.smartOp trace op args := by
  cases op <;> try rfl
  case globOp operation =>
    cases operation <;> try rfl
    case global index => exact (notGlobalRead index rfl).elim

/-- A primitive with no global writes and no global-read replacement has the
original operation simulation, using the argument induction hypothesis. This
is Flapjack proof infrastructure for the operation cases. -/
theorem knownCorrect0OpNoWrites {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (xs : List ClosLang.Exp) (env1full : List Value) (s0 : State (Spt ValApprox × C) F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (notGlobalRead : ∀ index, op ≠ .globOp (.global index))
    (noWrites : ∀ k, opGlobalBag op k = 0)
    (argsIH : KnownSimulationAt xs env1full s0) : KnownSimulationAt [.op trace op xs] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have argsUnique : uniqueSetGlobals xs s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals_append, elistGlobals, setGlobals, noWrites,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  have argsDisjoint : mglobalsDisjoint s0.globals xs := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals, noWrites,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using disjoint
  have argsSafe : ∀ e ∈ xs, esgcFree e := by
    have safeOp := exprSafe (.op trace op xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using safeOp
  have argsSyntax : everyFnVarsNone xs := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  have argsFree : fvMax env1.length xs := by
    simpa [fvMax, freeVars, freeVarExp] using free
  cases hk : knownListTotal c xs aenv g0 with
  | mk argEas g1 =>
    cases ho : knownOpHOL op (argEas.map Prod.snd).reverse g1 with
    | mk a g2 =>
      rw [knownListTotal_op, hk] at known
      dsimp only at known
      rw [ho] at known
      dsimp only at known
      change ([(selectedOutput trace op a (argEas.map Prod.fst), a)], g2) = (eas, g) at known
      rw [ordinaryKnownOutput trace op a (argEas.map Prod.fst) notGlobalRead] at known
      simp only [Prod.mk.injEq] at known
      rcases known with ⟨rfl, rfl⟩
      have ⟨subArgs, subOp⟩ := subsptKnownOpElistGlobals c xs aenv g0 argEas g1
        op (argEas.map Prod.snd).reverse g2 a ⟨hk, ho, sub0, by simp [noWrites]⟩
      have subArgsNext : sptSubspt g1 (nextG s0) := by
        intro key member
        obtain ⟨mid, eq1⟩ := subOp key member
        obtain ⟨last, eq2⟩ := sub1 key mid
        exact ⟨last, eq2.trans eq1⟩
      cases hr : evaluate xs env1full s0 with
      | mk argResult middle =>
        have argsNoType : argResult ≠ .err (.abort .typeError) := by
          intro eq
          subst argResult
          rw [evaluate_ordinaryOp_eq trace op xs env1full s0 notInstall notForce, hr] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact noType rfl
        obtain ⟨targetArgResult, targetMiddle, targetArgs, argsRelated, midState, midGlobals,
            midOracleState, midOracle⟩ := argsIH argResult middle env1 xenv1 env2 xenv2 t0 c g0 g1
          aenv argEas ⟨hr, hk, state, argsSyntax, coSyntax, argsDisjoint, oracle, stateOracleDisjoint,
            argsSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
            subArgs, subArgsNext, mono, argsFree, envRel, argsUnique, stateOracle, envEq, argsNoType⟩
        obtain ⟨targetResult, targetFinal, targetRun, resultRelated, finalState⟩ :=
          Relations.StateRelation.ordinarySmartOpSimulation c (nextG middle) trace op xs
            (argEas.map Prod.fst) env1full (env2 ++ xenv2) s0 middle t0 targetMiddle
            argResult targetArgResult notInstall notForce hr targetArgs argsRelated midState res1 s run noType
        have ⟨nextEq, finalGlobals, finalOracle, finalDisjoint⟩ :=
          ordinaryOpStateInvariants trace op xs env1full s0 middle s argResult res1
            notInstall notForce noWrites hr run midGlobals midOracleState midOracle
        exact ⟨targetResult, targetFinal, by simpa using targetRun,
          by simpa [nextEq] using resultRelated, by simpa [nextEq] using finalState,
          finalGlobals, finalOracle, finalDisjoint⟩

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Label operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpLabel {C F : Type} (trace : BackendCommon.Tra) (label : Nat)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.label label) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.label label) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- Ffi operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpFfi {C F : Type} (trace : BackendCommon.Tra) (name : Flapjack.Basis.Pure.MlString.MlString)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.ffi name) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.ffi name) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- Int operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpInt {C F : Type} (trace : BackendCommon.Tra) (operation : ClosLang.IntOp)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.intOp operation) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.intOp operation) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- Word operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpWord {C F : Type} (trace : BackendCommon.Tra) (operation : ClosLang.WordOp)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.wordOp operation) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.wordOp operation) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- Block operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpBlock {C F : Type} (trace : BackendCommon.Tra) (operation : ClosLang.BlockOp)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.blockOp operation) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.blockOp operation) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- Memory operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpMemory {C F : Type} (trace : BackendCommon.Tra) (operation : ClosLang.MemOp)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.memOp operation) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.memOp operation) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- AllocThunk operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpAllocThunk {C F : Type} (trace : BackendCommon.Tra) (mode : AstHOL.ThunkMode)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.thunkOp (.allocThunk mode)) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.thunkOp (.allocThunk mode)) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- UpdateThunk operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpUpdateThunk {C F : Type} (trace : BackendCommon.Tra) (mode : AstHOL.ThunkMode)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.thunkOp (.updateThunk mode)) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.thunkOp (.updateThunk mode)) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- AllocGlobal operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpAllocGlobal {C F : Type} (trace : BackendCommon.Tra)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.globOp .allocGlobal) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.globOp .allocGlobal) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- GlobalsPtr operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpGlobalsPtr {C F : Type} (trace : BackendCommon.Tra)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.globOp .globalsPtr) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.globOp .globalsPtr) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

/-- SetGlobalsPtr operation case of the original optimizer simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0OpSetGlobalsPtr {C F : Type} (trace : BackendCommon.Tra)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (ih : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace (.globOp .setGlobalsPtr) xs] env s0 := by
  apply knownCorrect0OpNoWrites trace (.globOp .setGlobalsPtr) xs env s0
  · simp
  · simp
  · intro index; simp
  · intro k; simp [opGlobalBag, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  · exact ih

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Ordinary
