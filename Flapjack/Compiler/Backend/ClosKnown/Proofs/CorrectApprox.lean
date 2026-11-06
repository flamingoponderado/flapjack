import Flapjack.Compiler.Backend.ClosKnown.Proofs.OracleGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.SourceEquations

/-! Base cases of the known-function approximation theorem. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- A related environment prefix provides sound indexed approximations;
indices beyond that prefix use `Other`. This is Flapjack infrastructure. -/
private theorem relatedEnvLookup (as : List ValApprox) (vs extra : List ClosSem.Value)
    (related : List.Forall₂ ValApproxVal as vs) : ∀ (i : Nat) (v : ClosSem.Value),
    (vs ++ extra)[i]? = some v → ValApproxVal (as[i]?.getD .other) v := by
  induction related with
  | nil =>
    intro i v found
    simpa using ValApproxVal.other v
  | cons relation related ih =>
    intro i v found
    cases i with
    | zero =>
      simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at found
      subst v
      simpa using relation
    | succ i =>
      simp only [List.cons_append, List.getElem?_cons_succ] at found ⊢
      exact ih i v found


/-- The quantified induction predicate obtained from the source theorem after
fixing the optimizer inputs. This is Flapjack proof infrastructure. -/
def KnownApproxInvariant (C F : Type) (c : Config) (xs : List ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox) : Prop :=
  ∀ (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (env extra : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : State (Spt ValApprox × C) F),
    knownListTotal c xs aenv g0 = (eas, g) ∧ evaluate xs (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals xs s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals xs ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ xs, esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0 →
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs

/-- Empty-list case of the original known-function approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxNil {C F : Type} (c : Config) (aenv : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (env extra : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [] aenv g0 = (eas, g) ∧ evaluate [] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ ([] : List ClosLang.Exp), esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, _, _, approx, _⟩
  simp [knownListTotal] at known
  rcases known with ⟨rfl, rfl⟩
  simp [evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨approx, by intro vs h; cases h; exact .nil⟩

/-- Variable case of the original known-function approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxVar {C F : Type} (c : Config) (trace : BackendCommon.Tra) (index : Nat)
    (aenv : List ValApprox) (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox))
    (g : Spt ValApprox) (env extra : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.var trace index] aenv g0 = (eas, g) ∧
      evaluate [.var trace index] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.var trace index] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.var trace index] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.var trace index], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, _, related, approx, _⟩
  simp only [knownListTotal_var, Prod.mk.injEq] at known
  rcases known with ⟨rfl, rfl⟩
  cases found : (env ++ extra)[index]? with
  | none =>
    simp [evaluate, found] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨approx, by intro vs h; cases h⟩
  | some v =>
    simp [evaluate, found] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨approx, ?_⟩
    intro vs h
    cases h
    exact .cons (relatedEnvLookup aenv env extra related index v found) .nil

/-- Raise case of the original known-function approximation theorem; its
single induction hypothesis is the source theorem for the raised expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxRaise {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (bodyIH : KnownApproxInvariant C F c [body] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.raise trace body] aenv g0 = (eas, g) ∧
      evaluate [.raise trace body] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.raise trace body] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.raise trace body] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.raise trace body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have uniqueBody : uniqueSetGlobals [body] s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals, setGlobals] using unique
  have disjointBody : mglobalsDisjoint s0.globals [body] := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals] using disjoint
  have bodySafe : ∀ e ∈ [body], esgcFree e := by
    have raised := exprSafe (.raise trace body) (by simp)
    simpa [esgcFree] using raised
  cases hk : knownListTotal c [body] aenv g0 with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEasEq⟩ := knownListTotal_single_result c body aenv g0 bodyG bodyEas hk
    subst bodyEas
    rw [knownListTotal_raise, hk] at known
    simp [knownSourceHead] at known
    rcases known with ⟨rfl, rfl⟩
    rw [evaluate] at run
    cases hr : evaluate [body] (env ++ extra) s0 with
    | mk bodyResult next =>
      have result := bodyIH [(bodyExpr, bodyApprox)] bodyG env extra s0 bodyResult next
        ⟨hk, hr, uniqueBody, related, approx, disjointBody, oracle, safe, envSafe, bodySafe, approxSafe, globalsSafe⟩
      rw [hr] at run
      cases bodyResult <;> simp only at run <;> cases run <;>
        exact ⟨result.1, by intro vs impossible; cases impossible⟩

/-- Tick case of the original approximation theorem, including timeout. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxTick {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (bodyIH : KnownApproxInvariant C F c [body] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.tick trace body] aenv g0 = (eas, g) ∧
      evaluate [.tick trace body] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.tick trace body] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.tick trace body] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.tick trace body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have uniqueBody : uniqueSetGlobals [body] s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals, setGlobals] using unique
  have disjointBody : mglobalsDisjoint s0.globals [body] := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals] using disjoint
  have bodySafe : ∀ e ∈ [body], esgcFree e := by
    have ticked := exprSafe (.tick trace body) (by simp)
    simpa [esgcFree] using ticked
  cases hk : knownListTotal c [body] aenv g0 with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEasEq⟩ := knownListTotal_single_result c body aenv g0 bodyG bodyEas hk
    subst bodyEas
    rw [knownListTotal_tickSource, hk] at known
    simp [knownSourceHead] at known
    rcases known with ⟨rfl, rfl⟩
    by_cases zero : s0.clock = 0
    · simp [evaluate, zero] at run
      rcases run with ⟨rfl, rfl⟩
      have preserved := ApproxEvaluate.stateGlobalsApproxKnownDisjoint c [body] aenv g0
        [(bodyExpr, bodyApprox)] bodyG s0 ⟨hk, disjointBody, approx⟩
      exact ⟨preserved, by intro vs impossible; cases impossible⟩
    · have bodyRun : evaluate [body] (env ++ extra) (decClock 1 s0) = (res, s) := by
        simpa [evaluate, zero] using run
      have bodyIHResult := bodyIH [(bodyExpr, bodyApprox)] bodyG env extra (decClock 1 s0) res s
        ⟨hk, bodyRun, by simpa [decClock] using uniqueBody, related,
          by simpa [decClock, stateGlobalsApprox] using approx,
          by simpa [decClock] using disjointBody,
          by simpa [decClock] using oracle,
          by simpa [ssgcFreeDecClock] using safe, envSafe, bodySafe, approxSafe, globalsSafe⟩
      simpa using bodyIHResult

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox
