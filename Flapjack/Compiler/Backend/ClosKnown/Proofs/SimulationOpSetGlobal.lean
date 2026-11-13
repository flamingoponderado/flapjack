module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationOpOrdinary

@[expose] public section


/-! Global-write case of known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.SetGlobal
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps

/-- A successful global write preserves agreement with a larger approximation
tree containing the optimizer's result. This is Flapjack induction
infrastructure for the global-write case. -/
theorem setGlobalApproxAfter {C F : Type} (index : Nat)
    (approxs : List ValApprox) (g0 g : Spt ValApprox) (a : ValApprox)
    (values : List Value) (middle next : State C F) (v : Value) (tree : Spt ValApprox)
    (known : knownOpHOL (.globOp (.setGlobal index)) approxs g0 = (a, g))
    (run : doApp (.globOp (.setGlobal index)) values middle = .val (v, next))
    (rel : List.Forall₂ ValApproxVal approxs values)
    (globals : stateGlobalsApprox middle tree) (g0sub : sptSubspt g0 g) (sub : sptSubspt g tree) :
    stateGlobalsApprox next tree := by
  have smaller : stateGlobalsApprox middle g0 := by
    have composed : sptSubspt g0 tree := by
      intro k member
      obtain ⟨mid, eq1⟩ := g0sub k member
      obtain ⟨last, eq2⟩ := sub k mid
      exact ⟨last, eq2.trans eq1⟩
    exact stateGlobalsApproxSubspt g0 tree middle ⟨composed, globals⟩
  have writtenApprox := (KnownOpCorrect.knownOpCorrectApproxSetGlobal index approxs g0 a g
    values middle v next known run rel smaller).1
  have indexMem : sptMem index g := by
    cases approxs with
    | nil =>
      cases rel
      simp [doApp, applyGlobal] at run
    | cons first rest =>
      simp only [knownOpHOL, Prod.mk.injEq] at known
      obtain ⟨_, rfl⟩ := known
      simp [sptMem_sptInsert]
  have eqLookup := (sub index indexMem).2
  have frame := doAppMglobals (.globOp (.setGlobal index)) values middle next v run
  intro k value approx ⟨found, lookup⟩
  by_cases same : k = index
  · subst k
    apply writtenApprox index value approx
    exact ⟨found, eqLookup.symm.trans lookup⟩
  · apply globals k value approx
    exact ⟨frame.2 k value ⟨found, by simp [opGlobalBag, same]⟩, lookup⟩

/-- Evaluating a global-write operation preserves the final-state simulation
invariants, using the optimizer's argument approximations. This is Flapjack
induction infrastructure. -/
theorem setGlobalStateInvariants {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (xs : List ClosLang.Exp) (env : List Value) (s0 middle final : State (Spt ValApprox × C) F)
    (argResult result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (argEas : List (ClosLang.Exp × ValApprox)) (g1 g2 : Spt ValApprox) (a : ValApprox)
    (known : knownOpHOL (.globOp (.setGlobal index)) (argEas.map Prod.snd).reverse g1 = (a, g2))
    (subOp : sptSubspt g1 g2) (subNext : sptSubspt g2 (nextG middle))
    (argsRun : evaluate xs env s0 = (argResult, middle))
    (argsApprox : ∀ values, argResult = .val values →
      List.Forall₂ ValApproxVal (argEas.map Prod.snd) values)
    (run : evaluate [.op trace (.globOp (.setGlobal index)) xs] env s0 = (result, final))
    (globals : stateGlobalsApprox middle (nextG middle))
    (oracle : isStateOracle (compileInc c) middle.compileOracle)
    (oracleDisjoint : oracleGapproxDisjoint (nextG middle) middle.compileOracle) :
    nextG final = nextG middle ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      oracleGapproxDisjoint (nextG final) final.compileOracle := by
  rw [evaluate_ordinaryOp_eq trace (.globOp (.setGlobal index)) xs env s0 (by simp) (by simp), argsRun] at run
  cases argResult with
  | err error =>
    simp at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, globals, oracle, oracleDisjoint⟩
  | val values =>
    cases app : doApp (.globOp (.setGlobal index)) values.reverse middle with
    | err error =>
      simp [app] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨rfl, globals, oracle, oracleDisjoint⟩
    | val pair =>
      rcases pair with ⟨value, next⟩
      simp [app] at run
      rcases run with ⟨rfl, rfl⟩
      have oracleEq := (doApp_codeOracle _ _ _ _ _ app).2
      have valueRel := List.rel_reverse (argsApprox values rfl)
      have globalNext := setGlobalApproxAfter index (argEas.map Prod.snd).reverse g1 g2 a
        values.reverse middle next value (nextG middle) known app valueRel globals subOp subNext
      have nextEq : nextG next = nextG middle := by simp [nextG, oracleEq]
      exact ⟨nextEq, by simpa [nextEq] using globalNext, by simpa [oracleEq] using oracle,
        by simpa [nextEq, oracleEq] using oracleDisjoint⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation.SetGlobal
