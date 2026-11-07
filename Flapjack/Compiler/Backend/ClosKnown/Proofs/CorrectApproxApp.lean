import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxCall
import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownUnchanged

/-! Application case infrastructure for known-function approximation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.App
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The global component of the application case, independent of the
inlining decision. This is Flapjack induction infrastructure. -/
theorem knownAppRuntimeApprox {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (loc : Option Nat) (x : ClosLang.Exp) (xs : List ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (functionIH : ∀ (ea2 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea2, g1) = knownListTotal c xs aenv g0 → KnownApproxInvariant C F c [x] aenv g1)
    (ea2 ea1 : List (ClosLang.Exp × ValApprox)) (g1 g2 : Spt ValApprox)
    (env extra : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c xs aenv g0 = (ea2, g1) ∧
      knownListTotal c [x] aenv g1 = (ea1, g2) ∧
      evaluate [.app trace loc x xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.app trace loc x xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.app trace loc x xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.app trace loc x xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g2 := by
  rcases h with ⟨hk, hf, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have uniqueBoth : uniqueSetGlobals (xs ++ [x]) s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero] at bound ⊢
    omega
  have ⟨argsUnique, fnUnique, swappedUnique⟩ := Cons.uniqueParts xs [x] s0.compileOracle uniqueBoth
  have ⟨fnDisjoint, argsDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals x x x x x xs trace .install [] loc none [] 0 0).2.2.2.2.2.2.2.2.1.mp disjoint
  have safeParts := exprSafe (.app trace loc x xs) (by simp)
  simp only [esgcFree, esgcFreeList_iff] at safeParts
  have argsSafe := safeParts.2
  have fnSafe : ∀ e ∈ [x], esgcFree e := by simpa using safeParts.1
  cases xs with
  | nil =>
    simp [evaluate] at run
    rcases run with ⟨rfl, rfl⟩
    have midApprox := ApproxEvaluate.stateGlobalsApproxKnownDisjoint c [] aenv g0 ea2 g1 s0
      ⟨hk, argsDisjoint, approx⟩
    exact ApproxEvaluate.stateGlobalsApproxKnownDisjoint c [x] aenv g1 ea1 g2 s0
      ⟨hf, fnDisjoint, midApprox⟩
  | cons first rest =>
    cases argsRun : evaluate (first :: rest) (env ++ extra) s0 with
    | mk argsResult middle =>
      have argApprox := argsIH ea2 g1 env extra s0 argsResult middle
        ⟨hk, argsRun, argsUnique, related, approx, argsDisjoint, oracle, safe, envSafe, argsSafe, approxSafe, globalsSafe⟩
      have middleClock : middle.clock ≤ s0.clock := by
        simpa [argsRun] using evaluate_clock_le (first :: rest) (env ++ extra) s0
      cases argsResult with
      | err error =>
        simp [evaluate, argsRun, fixClock, Nat.min_eq_right middleClock] at run
        rcases run with ⟨rfl, rfl⟩
        exact ApproxEvaluate.stateGlobalsApproxKnownListEvaluate (first :: rest) (env ++ extra) s0
          (.err error) middle c [x] aenv g1 ea1 g2
          ⟨argsRun, hf, safe, envSafe, argsSafe, fnDisjoint, uniqueBoth, argApprox.1⟩
      | val values =>
        have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals (first :: rest) (env ++ extra) s0
          (.val values) middle ⟨argsRun, safe, argsSafe, envSafe⟩
        have valuesSafe : ∀ v ∈ values, vsgcFree v := by simpa [rsgcFree] using safety.2.1
        have nextUnique := uniqueSetGlobalsEvaluate (first :: rest) [x] (env ++ extra) s0 middle
          (.val values) ⟨fnUnique, argsRun⟩
        have nextDisjoint := mglobalsDisjointEvaluate s0 [x] (first :: rest) (env ++ extra) (.val values) middle
          ⟨argsRun, safe, envSafe, argsSafe, swappedUnique, fnDisjoint⟩
        have nextOracle := oracleGapproxDisjointLemma (first :: rest) (env ++ extra) s0 (.val values) middle
          c aenv g0 ea2 g1 ⟨argsRun, hk, argsUnique, oracle⟩
        have optimizerSafe := PreserveSafety.knownPreservesEsgcFree c (first :: rest) aenv g0 ea2 g1
          ⟨hk, argsSafe, approxSafe, globalsSafe⟩
        cases fnRun : evaluate [x] (env ++ extra) middle with
        | mk fnResult next =>
          have fnApprox := functionIH ea2 g1 hk.symm ea1 g2 env extra middle fnResult next
            ⟨hf, fnRun, nextUnique, related, argApprox.1, nextDisjoint, nextOracle, safety.1,
              envSafe, fnSafe, approxSafe, optimizerSafe.2.2⟩
          have nextClock : next.clock ≤ middle.clock := by
            simpa [fnRun] using evaluate_clock_le [x] (env ++ extra) middle
          cases fnResult with
          | err error =>
            simp [evaluate, argsRun, fixClock, Nat.min_eq_right middleClock, fnRun,
              Nat.min_eq_right nextClock] at run
            rcases run with ⟨rfl, rfl⟩
            exact fnApprox.1
          | val fnValues =>
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value x (env ++ extra) middle next fnValues fnRun
            have fnSafety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [x] (env ++ extra) middle
              (.val [fnValue]) next ⟨fnRun, safety.1, fnSafe, envSafe⟩
            have fnValueSafe : vsgcFree fnValue := by simpa [rsgcFree] using fnSafety.2.1
            have finalOracle := oracleGapproxDisjointLemma [x] (env ++ extra) middle (.val [fnValue]) next
              c aenv g1 ea1 g2 ⟨fnRun, hf, nextUnique, nextOracle⟩
            cases appRun : evaluateApp loc fnValue values next with
            | mk appResult last =>
              have finalApprox := ApproxRuntime.stateGlobalsApproxEvaluateApp loc fnValue values next appResult last g2
                appRun fnSafety.1 fnValueSafe valuesSafe finalOracle fnApprox.1
              simp [evaluate, argsRun, fixClock, Nat.min_eq_right middleClock, fnRun,
                Nat.min_eq_right nextClock, appRun] at run
              rcases run with ⟨rfl, rfl⟩
              exact finalApprox

/-- A successful exact-arity closure application evaluates its body with
all arguments followed by the captured environment. This has no separate HOL
declaration; it isolates the source evaluator's full-application branch. -/
theorem exactClosureAppValue {C F : Type} (loc : Nat) (captures args : List ClosSem.Value)
    (body : ClosLang.Exp) (s0 : State C F) (vs : List ClosSem.Value) (s : State C F)
    (nonempty : args ≠ [])
    (run : evaluateApp none (.closure (some loc) [] captures args.length body) args s0 = (.val vs, s)) :
    evaluate [body] (args ++ captures) (decClock args.length s0) = (.val vs, s) := by
  by_cases bound : args.length ≤ s0.maxApp
  · have pos : 0 < args.length := List.length_pos_iff.mpr nonempty
    have takeAll : args.reverse.take args.length = args.reverse := by
      simpa only [List.length_reverse] using
        (show args.reverse.take args.reverse.length = args.reverse from List.take_length)
    have dest : destClosure s0.maxApp none (.closure (some loc) [] captures args.length body)
        args = some (.fullApp body (args ++ captures) []) := by
      simp [destClosure, checkLoc, bound, pos, takeAll]
    cases args with
    | nil => contradiction
    | cons a rest =>
      rw [evaluateApp, dest] at run
      simp only [List.length_nil, Nat.sub_zero] at run
      split at run
      · simp at run
      · cases hb : evaluate [body] ((a :: rest) ++ captures) (decClock (a :: rest).length s0) with
        | mk result last =>
          have clockBound : last.clock ≤ (decClock (a :: rest).length s0).clock := by
            have le := evaluate_clock_le [body] ((a :: rest) ++ captures) (decClock (a :: rest).length s0)
            rw [hb] at le
            exact le
          simp only [fixClock, hb, Nat.min_eq_right clockBound] at run
          cases result with
          | err error => cases error <;> simp at run
          | val values =>
            obtain ⟨value, rfl⟩ := evaluate_singleton_value body ((a :: rest) ++ captures)
              (decClock (a :: rest).length s0) last values hb
            simp [evaluateApp] at run
            rcases run with ⟨rfl, rfl⟩
            rfl
  · have dest : destClosure s0.maxApp none (.closure (some loc) [] captures args.length body)
        args = none := by simp [destClosure, checkLoc, bound]
    cases args with
    | nil => contradiction
    | cons a rest => rw [evaluateApp, dest] at run; cases run

/-- The value component of an inlined application. This is Flapjack
induction infrastructure; the induction hypotheses are those of the source
application case. -/
theorem inlineAppValueApprox {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (loc : Option Nat) (x : ClosLang.Exp) (xs : List ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox)
    (inlineIH : ∀ (ea2 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox)
      (ea1 : List (ClosLang.Exp × ValApprox)) (g2 : Spt ValApprox)
      (e1 : ClosLang.Exp) (a1 : ValApprox) (body : ClosLang.Exp),
      (ea2, g1) = knownListTotal c xs aenv g0 ∧
      (ea1, g2) = knownListTotal c [x] aenv g1 ∧
      (e1, a1) = knownSourceHead ea1 ∧ decideInlineHOL c a1 loc xs.length = .letInline body →
      KnownApproxInvariant C F (decInlineFactor c) [body] (ea2.map Prod.snd) g2)
    (functionIH : ∀ (ea2 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea2, g1) = knownListTotal c xs aenv g0 → KnownApproxInvariant C F c [x] aenv g1)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (ea2 : List (ClosLang.Exp × ValApprox)) (g1 g2 gb : Spt ValApprox)
    (e1 : ClosLang.Exp) (a1 : ValApprox) (body be : ClosLang.Exp) (ba : ValApprox)
    (env extra : List ClosSem.Value) (s0 : State (Spt ValApprox × C) F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c xs aenv g0 = (ea2, g1) ∧
      knownListTotal c [x] aenv g1 = ([(e1, a1)], g2) ∧
      decideInlineHOL c a1 loc xs.length = .letInline body ∧
      knownListTotal (decInlineFactor c) [body] (ea2.map Prod.snd) g2 = ([(be, ba)], gb) ∧
      evaluate [.app trace loc x xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.app trace loc x xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.app trace loc x xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.app trace loc x xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    ∀ vs, res = .val vs → List.Forall₂ ValApproxVal [ba] vs := by
  rcases h with ⟨hk, hf, decision, hb, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have locNone : loc = none := by cases loc <;> simp_all [decideInlineHOL]; all_goals cases a1 <;> simp_all
  subst loc
  obtain ⟨target, size, approxEq⟩ := decideInlineLetInlineImpClos c a1 none xs.length body decision
  have uniqueBoth : uniqueSetGlobals (xs ++ [x]) s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero] at bound ⊢
    omega
  have ⟨argsUnique, fnUnique, swappedUnique⟩ := Cons.uniqueParts xs [x] s0.compileOracle uniqueBoth
  have ⟨fnDisjoint, argsDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals x x x x x xs trace .install [] none none [] 0 0).2.2.2.2.2.2.2.2.1.mp disjoint
  have safeParts := exprSafe (.app trace none x xs) (by simp)
  simp only [esgcFree, esgcFreeList_iff] at safeParts
  have argsSafe := safeParts.2
  have fnSafe : ∀ e ∈ [x], esgcFree e := by simpa using safeParts.1
  intro vs valueResult
  have valRun : evaluate [.app trace none x xs] (env ++ extra) s0 = (.val vs, s) := by simpa [valueResult] using run
  cases xs with
  | nil => simp [evaluate] at valRun
  | cons first rest =>
    cases argsRun : evaluate (first :: rest) (env ++ extra) s0 with
    | mk argsResult middle =>
      have argApprox := argsIH ea2 g1 env extra s0 argsResult middle
        ⟨hk, argsRun, argsUnique, related, approx, argsDisjoint, oracle, safe, envSafe, argsSafe, approxSafe, globalsSafe⟩
      have middleClock : middle.clock ≤ s0.clock := by
        simpa [argsRun] using evaluate_clock_le (first :: rest) (env ++ extra) s0
      cases argsResult with
      | err error => simp [evaluate, argsRun, fixClock, Nat.min_eq_right middleClock] at valRun
      | val values =>
        have valuesLength : values.length = (first :: rest).length :=
          evaluate_length.1 (first :: rest) (env ++ extra) s0 middle values argsRun
        have valuesNonempty : values ≠ [] := by intro eq; simp [eq] at valuesLength
        have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals (first :: rest) (env ++ extra) s0
          (.val values) middle ⟨argsRun, safe, argsSafe, envSafe⟩
        have valuesSafe : ∀ v ∈ values, vsgcFree v := by simpa [rsgcFree] using safety.2.1
        have nextUnique := uniqueSetGlobalsEvaluate (first :: rest) [x] (env ++ extra) s0 middle
          (.val values) ⟨fnUnique, argsRun⟩
        have nextDisjoint := mglobalsDisjointEvaluate s0 [x] (first :: rest) (env ++ extra) (.val values) middle
          ⟨argsRun, safe, envSafe, argsSafe, swappedUnique, fnDisjoint⟩
        have nextOracle := oracleGapproxDisjointLemma (first :: rest) (env ++ extra) s0 (.val values) middle
          c aenv g0 ea2 g1 ⟨argsRun, hk, argsUnique, oracle⟩
        have optimizerSafe := PreserveSafety.knownPreservesEsgcFree c (first :: rest) aenv g0 ea2 g1
          ⟨hk, argsSafe, approxSafe, globalsSafe⟩
        cases fnRun : evaluate [x] (env ++ extra) middle with
        | mk fnResult next =>
          have fnApprox := functionIH ea2 g1 hk.symm [(e1, a1)] g2 env extra middle fnResult next
            ⟨hf, fnRun, nextUnique, related, argApprox.1, nextDisjoint, nextOracle, safety.1,
              envSafe, fnSafe, approxSafe, optimizerSafe.2.2⟩
          have nextClock : next.clock ≤ middle.clock := by
            simpa [fnRun] using evaluate_clock_le [x] (env ++ extra) middle
          cases fnResult with
          | err error =>
            simp [evaluate, argsRun, fixClock, Nat.min_eq_right middleClock, fnRun,
              Nat.min_eq_right nextClock] at valRun
          | val fnValues =>
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value x (env ++ extra) middle next fnValues fnRun
            have fnRelation := fnApprox.2 [fnValue] rfl
            have closureRel : ValApproxVal (.clos target (first :: rest).length body size) fnValue := by
              cases fnRelation with
              | cons rel _ => simpa [approxEq] using rel
            cases closureRel with
            | clos _ _ _ _ captures =>
              have fnSafety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [x] (env ++ extra) middle
                (.val [.closure (some target) [] captures (first :: rest).length body]) next
                ⟨fnRun, safety.1, fnSafe, envSafe⟩
              have capturesSafe : ∀ v ∈ captures, vsgcFree v := by
                have closureSafe : setGlobals body = FlatProps.emptyGlobalBag ∧
                    ∀ v ∈ captures, vsgcFree v := by
                  simpa [rsgcFree, vsgcFree] using fnSafety.2.1
                exact closureSafe.2
              have finalOracle := oracleGapproxDisjointLemma [x] (env ++ extra) middle
                (.val [.closure (some target) [] captures (first :: rest).length body]) next
                c aenv g1 [(e1, a1)] g2 ⟨fnRun, hf, nextUnique, nextOracle⟩
              have a1Safe : valApproxSgcFree a1 := by
                have fopt := PreserveSafety.knownPreservesEsgcFree c [x] aenv g1 [(e1, a1)] g2
                  ⟨hf, fnSafe, approxSafe, optimizerSafe.2.2⟩
                simpa using fopt.2.1
              have bodyEmpty : setGlobals body = FlatProps.emptyGlobalBag := by
                simpa [approxEq, valApproxSgcFree] using a1Safe
              have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using setGlobalsEmptyEsgcFree body bodyEmpty
              have bodyUnique0 := uniqueSetGlobalsEvaluate [x] [] (env ++ extra) middle next
                (.val [.closure (some target) [] captures (first :: rest).length body])
                ⟨nilUniqueSetGlobals [x] middle.compileOracle nextUnique, fnRun⟩
              have bodyUnique : uniqueSetGlobals [body] next.compileOracle := by
                simpa [uniqueSetGlobals, elistGlobals, setGlobals, bodyEmpty,
                  FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] using bodyUnique0
              have bodyDisjoint : mglobalsDisjoint next.globals [body] := by
                simp [mglobalsDisjoint, elistGlobals, bodyEmpty, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag]
              have appRun : evaluateApp none (.closure (some target) [] captures values.length body) values next = (.val vs, s) := by
                simpa [evaluate, argsRun, fixClock, Nat.min_eq_right middleClock, fnRun,
                  Nat.min_eq_right nextClock, valuesLength] using valRun
              have bodyRun := exactClosureAppValue target captures values body next vs s valuesNonempty appRun
              have bodyInvariant := inlineIH ea2 g1 [(e1, a1)] g2 e1 a1 body
                ⟨hk.symm, hf.symm, by simp [knownSourceHead], decision⟩
              have unchanged := KnownUnchanged.inlineBodyGlobalsUnchanged c a1 none (first :: rest).length
                body (ea2.map Prod.snd) g2 [(be, ba)] gb a1Safe decision hb
              have allSafe : ∀ v ∈ values ++ captures, vsgcFree v := by
                simpa [List.mem_append, or_imp, forall_and] using And.intro valuesSafe capturesSafe
              have bodyResult := bodyInvariant [(be, ba)] gb values captures
                (decClock values.length next) (.val vs) s
                ⟨hb, bodyRun, by simpa [decClock] using bodyUnique, argApprox.2 values rfl,
                  by simpa [decClock, stateGlobalsApprox] using fnApprox.1,
                  by simpa [decClock] using bodyDisjoint,
                  by simpa [decClock] using finalOracle,
                  (ssgcFreeDecClock values.length next).2 fnSafety.1, allSafe, bodySafe,
                  optimizerSafe.2.1, by simpa [← unchanged] using
                    (PreserveSafety.knownPreservesEsgcFree c [x] aenv g1 [(e1, a1)] g2
                      ⟨hf, fnSafe, approxSafe, optimizerSafe.2.2⟩).2.2⟩
              exact bodyResult.2 vs rfl

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Application case of the original approximation theorem, including both
non-inlining decisions and closure-body inlining. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxApp {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (loc : Option Nat) (x : ClosLang.Exp) (xs : List ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox)
    (inlineIH : ∀ (ea2 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox)
      (ea1 : List (ClosLang.Exp × ValApprox)) (g2 : Spt ValApprox)
      (e1 : ClosLang.Exp) (a1 : ValApprox) (body : ClosLang.Exp),
      (ea2, g1) = knownListTotal c xs aenv g0 ∧
      (ea1, g2) = knownListTotal c [x] aenv g1 ∧
      (e1, a1) = knownSourceHead ea1 ∧ decideInlineHOL c a1 loc xs.length = .letInline body →
      KnownApproxInvariant C F (decInlineFactor c) [body] (ea2.map Prod.snd) g2)
    (functionIH : ∀ (ea2 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea2, g1) = knownListTotal c xs aenv g0 → KnownApproxInvariant C F c [x] aenv g1)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.app trace loc x xs] aenv g0 = (eas, g) ∧
      evaluate [.app trace loc x xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.app trace loc x xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.app trace loc x xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.app trace loc x xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  cases ha : knownListTotal c xs aenv g0 with
  | mk ea2 g1 =>
    cases hf : knownListTotal c [x] aenv g1 with
    | mk ea1 g2 =>
      obtain ⟨e1, a1, eq⟩ := knownListTotal_single_result c x aenv g1 g2 ea1 hf
      subst ea1
      have runtime := knownAppRuntimeApprox c trace loc x xs aenv g0 argsIH functionIH
        ea2 [(e1, a1)] g1 g2 env extra s0 res s
        ⟨ha, hf, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
      have otherResult : ∀ vs, res = .val vs → List.Forall₂ ValApproxVal [.other] vs := by
        intro vs result
        have valueRun : evaluate [.app trace loc x xs] (env ++ extra) s0 = (.val vs, s) := by
          simpa [result] using run
        obtain ⟨v, rfl⟩ := evaluate_singleton_value (.app trace loc x xs) (env ++ extra) s0 s vs valueRun
        exact .cons (.other v) .nil
      rw [knownListTotal_app, ha] at known
      dsimp only at known
      rw [hf] at known
      simp only [knownSourceHead, List.headD_cons] at known
      cases decision : decideInlineHOL c a1 loc xs.length with
      | nothing =>
        simp only [decision, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        simpa using And.intro runtime otherResult
      | annotate target =>
        simp only [decision, Prod.mk.injEq] at known
        rcases known with ⟨rfl, rfl⟩
        simpa using And.intro runtime otherResult
      | letInline body =>
        cases hb : knownListTotal (decInlineFactor c) [body] (ea2.map Prod.snd) g2 with
        | mk eab gb =>
          obtain ⟨be, ba, eq⟩ := knownListTotal_single_result (decInlineFactor c) body
            (ea2.map Prod.snd) g2 gb eab hb
          subst eab
          have value := inlineAppValueApprox c trace loc x xs aenv g0 inlineIH functionIH argsIH
            ea2 g1 g2 gb e1 a1 body be ba env extra s0 res s
            ⟨ha, hf, decision, hb, run, unique, related, approx, disjoint, oracle, safe, envSafe,
              exprSafe, approxSafe, globalsSafe⟩
          simp only [decision] at known
          rw [hb] at known
          simp at known
          rcases known with ⟨rfl, rfl⟩
          simpa using And.intro runtime value

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.App
