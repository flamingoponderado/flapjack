module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationFn
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxLetrec

@[expose] public section


/-! Infrastructure for the recursive-closure case of optimizer simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Letrec
open ClosSem ClosProps ClosProps.StateGlobalSafety Relations KnownUnchanged BackendProps
open OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint
open Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Optimizing a list of function bodies that cannot write globals gives
related functions in any approximation tree extending the initial tree.
This is Flapjack proof infrastructure for the recursive-closure case. -/
theorem optimizedFunctionsRelated (c : Config) (fns : List (Nat × ClosLang.Exp))
    (clos aenv : List ValApprox) (g0 g : Spt ValApprox)
    (empty : funGlobals fns = FlatProps.emptyGlobalBag)
    (safeClos : ∀ a ∈ clos, valApproxSgcFree a)
    (safeEnv : ∀ a ∈ aenv, valApproxSgcFree a)
    (safeGlobals : globalsApproxSgcFree g0) (sub : sptSubspt g0 g) :
    List.Forall₂ (fRel c (clos ++ aenv) g) fns
      (fns.map (fun (n, e) =>
        (n, (knownSourceHead (knownListTotal c [e]
          (List.replicate n .other ++ clos ++ aenv) g0).1).1))) := by
  have bodiesEmpty : ∀ f ∈ fns, setGlobals f.2 = FlatProps.emptyGlobalBag := by
    have h := (elistGlobalsEmpty (fns.map Prod.snd)).1 (by simpa [funGlobals_eq_elist] using empty)
    intro f member
    exact h f.2 (List.mem_map.mpr ⟨f, member, rfl⟩)
  have each : ∀ f ∈ fns, fRel c (clos ++ aenv) g f
      (match f with | (n, e) => (n, (knownSourceHead (knownListTotal c [e]
        (List.replicate n .other ++ clos ++ aenv) g0).1).1)) := by
   intro f member
   rcases f with ⟨arity, body⟩
   have safe : ∀ a ∈ List.replicate arity ValApprox.other ++ clos ++ aenv, valApproxSgcFree a := by
    intro a mem
    simp only [List.mem_append] at mem
    rcases mem with (mem | mem) | mem
    · have eq := (List.mem_replicate.mp mem).2
      subst a
      simp [valApproxSgcFree]
    · exact safeClos a mem
    · exact safeEnv a mem
   cases hk : knownListTotal c [body] (List.replicate arity .other ++ clos ++ aenv) g0 with
   | mk eas after =>
    obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body
      (List.replicate arity .other ++ clos ++ aenv) g0 after eas hk
    subst eas
    have noWrites : elistGlobals [body] = FlatProps.emptyGlobalBag := by
      apply (elistGlobalsEmpty [body]).2
      intro e he
      simp only [List.mem_singleton] at he
      subst e
      exact bodiesEmpty (arity, body) member
    have unchanged := knownUnchangedGlobals c [body]
      (List.replicate arity .other ++ clos ++ aenv) g0 [(be, ba)] after ⟨hk, noWrites⟩
    subst after
    simp only [hk, knownSourceHead]
    refine ⟨rfl, g0, g0, ba, c.inlineFactor, sub, ?_, safeGlobals, ?_⟩
    · simpa [List.append_assoc] using safe
    · simpa [List.append_assoc] using hk
  clear empty bodiesEmpty
  induction fns with
  | nil => exact .nil
  | cons f fs ih =>
    apply List.Forall₂.cons (each f (by simp))
    apply ih
    intro f member; exact each f (by simp [member])

/-- Building closures at the same indices preserves the value relation when
their captured environments and function bodies are related. This is Flapjack
proof infrastructure for the recursive-closure case. -/
theorem recursiveClosuresRelated (c : Config) (g : Spt ValApprox) (loc : Option Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (env1 extra1 env2 extra2 : List ClosSem.Value)
    (aenv : List ValApprox)
    (fnSyntax : ∀ f ∈ fns1, everyFnVarsNone [f.2])
    (free : ∀ f ∈ fns1, fvMax (f.1 + fns1.length + env1.length) [f.2])
    (envRel : List.Forall₂ (ValueRel c g) env1 env2)
    (approx : List.Forall₂ ValApproxVal aenv env1)
    (functions : List.Forall₂ (fRel c ((match loc with
      | none => List.replicate fns1.length .other
      | some n => closGenNoInline n 0 fns1) ++ aenv) g) fns1 fns2)
    (indices : List Nat) :
    List.Forall₂ (ValueRel c g)
      (indices.map (fun i => .recclosure loc [] (env1 ++ extra1) fns1 i))
      (indices.map (fun i => .recclosure loc [] (env2 ++ extra2) fns2 i)) := by
  induction indices with
  | nil => exact .nil
  | cons i rest ih =>
    exact .cons (.recclosure loc [] [] env1 extra1 env2 extra2 fns1 fns2 i aenv
      fnSyntax free .nil envRel approx functions) ih

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Recursive-closure case of the optimizer simulation, with the original
evaluator's induction hypothesis for the body. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Letrec {C F : Type} (names : List Basis.Pure.MlString.MlString)
    (loc : Option Nat) (selected : Option (List Nat)) (fns : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env1full : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (bodyIH : ∀ (buildRc : List ClosSem.Value → List ClosSem.Value)
      (envdelta : Option (List ClosSem.Value)) (ed : List ClosSem.Value),
      (∀ f ∈ fns, f.1 ≤ s0.maxApp ∧ f.1 ≠ 0) ∧
      buildRc = (fun captures => (List.range fns.length).map
        (fun i => ClosSem.Value.recclosure loc [] captures fns i)) ∧
      envdelta = (match selected with | none => some (buildRc env1full) | some indices => (lookupVars indices env1full).map buildRc) ∧
      envdelta = some ed → KnownSimulationAt [body] (ed ++ env1full) s0) :
    KnownSimulationAt [.letrec names loc selected fns body] env1full s0 := by
  intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
  obtain ⟨run, known, state, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
    exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
    sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
  have syntaxParts : selected = none ∧ fnVarsNoneFuns fns ∧ everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
  obtain ⟨selectedEq, fnsSyntax, bodySyntax⟩ := syntaxParts
  have fnSyntaxAux : ∀ fs : List (Nat × ClosLang.Exp), fnVarsNoneFuns fs →
      ∀ f ∈ fs, everyFnVarsNone [f.2] := by
    intro fs hs
    induction fs with
    | nil => simp
    | cons f fs ih =>
      obtain ⟨n, e⟩ := f
      simp only [fnVarsNoneFuns] at hs
      intro f member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simpa [everyFnVarsNone] using hs.1
      · exact ih hs.2 f member
  have fnSyntax := fnSyntaxAux fns fnsSyntax
  subst selected
  have safeParts : funGlobals fns = FlatProps.emptyGlobalBag ∧ esgcFree body := by
    simpa [esgcFree] using exprSafe (.letrec names loc none fns body) (by simp)
  let clos := match loc with | none => List.replicate fns.length ValApprox.other | some n => closGenNoInline n 0 fns
  let newFns := fns.map (fun (n, e) =>
    (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ aenv) g0).1).1))
  have closSafe : ∀ a ∈ clos, valApproxSgcFree a := by
    cases loc with
    | none => simp [clos, valApproxSgcFree]
    | some n => exact closGenNoInlineSafe n 0 fns
  have subStart : sptSubspt g0 (nextG s0) := by
    intro k member
    obtain ⟨mid, e1⟩ := sub0 k member
    obtain ⟨last, e2⟩ := sub1 k mid
    exact ⟨last, e2.trans e1⟩
  have fnRel : List.Forall₂ (fRel c (clos ++ aenv) (nextG s0)) fns newFns :=
    optimizedFunctionsRelated c fns clos aenv g0 (nextG s0) safeParts.1 closSafe approxSafe globalSafe subStart
  have freeParts := (fvMaxLetrec env1.length names loc none fns body).1 free
  have fnFree : ∀ f ∈ fns, fvMax (f.1 + fns.length + env1.length) [f.2] := by
    intro f member
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using freeParts.1 f member
  let recs1 := (List.range fns.length).map (fun i => ClosSem.Value.recclosure loc [] env1full fns i)
  let recs2 := (List.range fns.length).map (fun i => ClosSem.Value.recclosure loc [] (env2 ++ xenv2) newFns i)
  have recRel : List.Forall₂ (ValueRel c (nextG s0)) recs1 recs2 := by
    simpa [recs1, recs2, envEq, clos] using recursiveClosuresRelated c (nextG s0) loc fns newFns
      env1 xenv1 env2 xenv2 aenv fnSyntax fnFree envRel approxRel (by simpa [clos] using fnRel)
      (List.range fns.length)
  have recApprox : List.Forall₂ ValApproxVal clos recs1 := by
    exact CorrectApprox.Letrec.recClosuresApprox loc env1full fns
  have recSafe : ∀ v ∈ recs1, vsgcFree v := by
    intro v member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    simpa [recs1, vsgcFree, ← funGlobals_eq_elist] using And.intro safeParts.1 envSafe
  have bodyUnique : uniqueSetGlobals [body] s0.compileOracle := by
    simpa [uniqueSetGlobals, elistGlobals, setGlobals, safeParts.1,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
  have bodyDisjoint : mglobalsDisjoint s0.globals [body] := by
    simpa [mglobalsDisjoint, elistGlobals, setGlobals, safeParts.1,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using disjoint
  have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using safeParts.2
  have extendedSafe : ∀ v ∈ (recs1 ++ env1) ++ xenv1, vsgcFree v := by
    simpa [List.mem_append, or_imp, forall_and, ← envEq] using And.intro recSafe envSafe
  have extendedApproxSafe : ∀ a ∈ clos ++ aenv, valApproxSgcFree a := by
    simpa [List.mem_append, or_imp, forall_and] using And.intro closSafe approxSafe
  cases hk : knownListTotal c [body] (clos ++ aenv) g0 with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ :=
      knownListTotal_single_result c body (clos ++ aenv) g0 bodyG bodyEas hk
    subst bodyEas
    rw [knownListTotal_letrec] at known
    change (let clos' := clos; let fs := newFns; let (ea, gg) := knownListTotal c [body] (clos' ++ aenv) g0
      ([(.letrec names loc none fs (knownSourceHead ea).1, (knownSourceHead ea).2)], gg)) = (eas, g) at known
    dsimp only at known
    rw [hk] at known
    simp [knownSourceHead] at known
    rcases known with ⟨rfl, rfl⟩
    by_cases valid : (fns.all (fun (arity, _) => arity ≤ s0.maxApp && arity != 0)) = true
    · have validAll : ∀ f ∈ fns, f.1 ≤ s0.maxApp ∧ f.1 ≠ 0 := by
        simpa [List.all_eq_true] using valid
      have ih := bodyIH (fun captures => (List.range fns.length).map
        (fun i => ClosSem.Value.recclosure loc [] captures fns i)) (some recs1) recs1
        ⟨validAll, rfl, rfl, rfl⟩
      have bodyRun : evaluate [body] (recs1 ++ env1full) s0 = (res1, s) := by
        simpa [evaluate, valid, recs1] using run
      have bodyEnvSafe : ∀ v ∈ recs1 ++ env1full, vsgcFree v := by
        simpa [envEq, List.append_assoc] using extendedSafe
      have bodyFree : fvMax (recs1 ++ env1).length [body] := by
        simpa [recs1, Nat.add_comm] using freeParts.2
      have result := ih res1 s (recs1 ++ env1) xenv1 (recs2 ++ env2) xenv2 t0 c g0 bodyG
        (clos ++ aenv) [(bodyExpr, bodyApprox)]
        ⟨bodyRun, hk, state, bodySyntax, coSyntax, bodyDisjoint, oracle, stateOracleDisjoint,
          bodySafe, safe, bodyEnvSafe, List.rel_append recApprox approxRel, oracleSafe, globalSafe,
          extendedApproxSafe, globals, sub0, sub1, mono, bodyFree, List.rel_append recRel envRel,
          bodyUnique, stateOracle, by simp [envEq, List.append_assoc], noType⟩
      obtain ⟨res2, t, targetRun, related, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := result
      refine ⟨res2, t, ?_, related, finalState, finalGlobals, finalOracle, finalDisjoint⟩
      have maxEq : s0.maxApp = t0.maxApp := state.2.2.2.2.2.2.1
      have targetValid : (newFns.all (fun (arity, _) => arity ≤ t0.maxApp && arity != 0)) = true := by
        simpa [newFns, List.all_map, ← maxEq] using valid
      simp only [List.map_cons, List.map_nil, evaluate, targetValid, if_true]
      simpa [recs2, newFns, List.append_assoc] using targetRun
    · simp [evaluate, valid] at run
      rcases run with ⟨rfl, rfl⟩
      exact False.elim (noType rfl)

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Letrec
