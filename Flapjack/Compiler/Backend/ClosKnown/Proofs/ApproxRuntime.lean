import Flapjack.Compiler.Backend.ClosKnown.Proofs.OracleGlobals

/-! Global approximation across runtime closure execution. -/
namespace Flapjack.Compiler.Backend.ClosKnown.ApproxRuntime
open ClosSem ClosProps ClosProps.StateGlobalSafety OracleGlobals
open Flapjack.SemanticPrimitivesHOL


/-- A safe evaluation preserves an approximation when both its own writes
and its future oracle writes are disjoint from the approximation domain.
This is Flapjack infrastructure for dynamic installation. -/
theorem stateGlobalsApproxEvaluateDisjoint {C F : Type} (xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s0 : State C F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State C F) (g : Spt ValApprox)
    (run : evaluate xs env s0 = (res, s)) (safe : ssgcFree s0)
    (envSafe : ∀ v ∈ env, vsgcFree v) (exprSafe : ∀ e ∈ xs, esgcFree e)
    (programDisjoint : gapproxDisjoint g xs)
    (oracle : oracleGapproxDisjoint g s0.compileOracle) (approx : stateGlobalsApprox s0 g) :
    stateGlobalsApprox s g := by
  obtain ⟨_, _, n, _, frame⟩ :=
    EvaluateGlobalsPort.Total.evaluateChangedGlobals xs env s0 res s ⟨run, safe, exprSafe, envSafe⟩
  intro i value a ⟨found, lookup⟩
  have domain : sptMem i g := (sptMem_iff_lookup i g).2 ⟨a, lookup⟩
  have prefixDisjoint := (oracleGapproxDisjointFirstN g s0.compileOracle).mp oracle n
  have outside : i ∉ ({k | elistGlobals xs k ≠ 0} ∪
      {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) := by
    intro member
    rcases member with written | written
    · exact (Set.disjoint_left.mp programDisjoint) domain written
    · exact (Set.disjoint_left.mp prefixDisjoint) domain written
  exact approx i value a ⟨frame.2 i value ⟨found, outside⟩, lookup⟩

/-- If a safe expression writes no globals, and its oracle is disjoint from
the approximation tree, evaluation preserves that approximation. This is
Flapjack infrastructure for the source call and application cases. -/
theorem stateGlobalsApproxEvaluateEmpty {C F : Type} (xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s0 : State C F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State C F) (g : Spt ValApprox)
    (run : evaluate xs env s0 = (res, s)) (safe : ssgcFree s0)
    (envSafe : ∀ v ∈ env, vsgcFree v) (exprSafe : ∀ e ∈ xs, esgcFree e)
    (empty : elistGlobals xs = FlatProps.emptyGlobalBag)
    (oracle : oracleGapproxDisjoint g s0.compileOracle) (approx : stateGlobalsApprox s0 g) :
    stateGlobalsApprox s g := by
  obtain ⟨_, _, n, _, frame⟩ :=
    EvaluateGlobalsPort.Total.evaluateChangedGlobals xs env s0 res s ⟨run, safe, exprSafe, envSafe⟩
  intro i value a ⟨found, lookup⟩
  have domain : sptMem i g := (sptMem_iff_lookup i g).2 ⟨a, lookup⟩
  have prefixDisjoint := (oracleGapproxDisjointFirstN g s0.compileOracle).mp oracle n
  have outside : i ∉ ({k | elistGlobals xs k ≠ 0} ∪
      {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) := by
    intro member
    rcases member with written | written
    · change elistGlobals xs i ≠ 0 at written
      apply written
      simpa [FlatProps.emptyGlobalBag] using congrFun empty i
    · exact (Set.disjoint_left.mp prefixDisjoint) domain written
  exact approx i value a ⟨frame.2 i value ⟨found, outside⟩, lookup⟩

/-- Applying a safe closure preserves an approximation tree disjoint from
future oracle writes. This is Flapjack infrastructure for source applications. -/
theorem stateGlobalsApproxEvaluateApp {C F : Type} (loc : Option Nat) (f : ClosSem.Value)
    (args : List ClosSem.Value) (s0 : State C F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State C F) (g : Spt ValApprox)
    (run : evaluateApp loc f args s0 = (res, s)) (safe : ssgcFree s0)
    (fnSafe : vsgcFree f) (argsSafe : ∀ v ∈ args, vsgcFree v)
    (oracle : oracleGapproxDisjoint g s0.compileOracle) (approx : stateGlobalsApprox s0 g) :
    stateGlobalsApprox s g := by
  obtain ⟨_, _, n, _, frame⟩ :=
    EvaluateGlobalsPort.Total.evaluateAppChangedGlobals loc f args s0 res s ⟨run, safe, fnSafe, argsSafe⟩
  intro i value a ⟨found, lookup⟩
  have domain : sptMem i g := (sptMem_iff_lookup i g).2 ⟨a, lookup⟩
  have prefixDisjoint := (oracleGapproxDisjointFirstN g s0.compileOracle).mp oracle n
  have outside : i ∉ {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0} :=
    (Set.disjoint_left.mp prefixDisjoint) domain
  exact approx i value a ⟨frame.2 i value ⟨found, outside⟩, lookup⟩

end Flapjack.Compiler.Backend.ClosKnown.ApproxRuntime
