module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationAppInline
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationAppNonInline
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApplyFullBody
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SubsptComposition
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxCons
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationBool
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBoolean
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationLetrec
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationOpGlobal
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationInstallDispatch

@[expose] public section


/-! Mutual evaluator induction for the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Total
open ClosSem ClosProps ClosProps.StateGlobalSafety
open BackendProps OracleGlobals OracleMonotonic UniqueGlobalsPort StateOracleDisjoint SubsptComposition
open Relations Relations.StateRelation Relations.StateRelation.Oracle
open Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL

/-- Induction on the evaluator clock and expression weight. This is
Flapjack infrastructure for assembling the original mutual theorem. -/
private theorem simulationAll {C F : Type} : ∀ clock : Nat,
    (∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
      (state : State (Spt ValApprox × C) F), state.clock = clock → KnownAppSimulationAt location f args state) ∧
    (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (state : State (Spt ValApprox × C) F), state.clock = clock → expsWeight expressions = weight →
        KnownSimulationAt expressions env state) := by
  intro clock
  induction clock using Nat.strongRecOn with
  | ind clock clockIH =>
    have appAll : ∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
        (state : State (Spt ValApprox × C) F), state.clock = clock → KnownAppSimulationAt location f args state := by
      intro location f args state stateClock
      cases args with
      | nil => exact knownCorrect0AppNil location f state
      | cons first rest =>
        cases found : destClosure state.maxApp location f (first :: rest) with
        | none =>
          intro res1 s loc2 f2 args2 t0 c argsopt h
          obtain ⟨run, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, noType⟩ := h
          rw [evaluateApp, found] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact (noType rfl).elim
        | some kind =>
          cases kind with
          | partialApp value => exact ApplyPartial.knownAppPartialCase location f first rest state value found
          | fullApp body env remaining =>
            by_cases timeout : state.clock < (first :: rest).length - remaining.length
            · exact ApplyFull.fullApplicationTimeoutCase location f first rest state body env remaining found timeout
            · apply ApplyFull.fullApplicationBodyCase location f first rest state body env remaining found timeout
              · have shorter := destClosure_full_remaining_lt _ _ _ _ _ _ _ found
                have small : (decClock ((first :: rest).length - remaining.length) state).clock < clock := by
                  simp only [decClock]; omega
                exact (clockIH _ small).2 _ [body] env _ rfl rfl
              · intro value middle run
                have shorter := destClosure_full_remaining_lt _ _ _ _ _ _ _ found
                have bound := evaluate_clock_le [body] env (decClock ((first :: rest).length - remaining.length) state)
                rw [run] at bound
                simp only at bound
                have small : middle.clock < clock := by simp only [decClock] at bound; omega
                exact (clockIH _ small).1 location value remaining middle rfl
    constructor
    · exact appAll
    · intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
            (state : State (Spt ValApprox × C) F), state.clock ≤ clock → expsWeight expressions < weight →
              KnownSimulationAt expressions env state := by
          intro expressions env state clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact (clockIH state.clock clockLt).2 _ expressions env state rfl rfl
          · exact weightIH _ weightLt expressions env state clockEq rfl
        have smaller : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
            (state : State (Spt ValApprox × C) F), state.clock < clock → KnownSimulationAt expressions env state := by
          intro expressions env state clockLt
          exact (clockIH state.clock clockLt).2 _ expressions env state rfl rfl
        have appBound : ∀ (location : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
            (state : State (Spt ValApprox × C) F), state.clock ≤ clock → KnownAppSimulationAt location f args state := by
          intro location f args state clockLe
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact (clockIH state.clock clockLt).1 location f args state rfl
          · exact appAll location f args state clockEq
        intro expressions env state stateClock measure
        cases expressions with
        | nil => exact knownCorrect0Nil env state
        | cons first rest =>
          cases rest with
          | cons second tail =>
            have headIH : KnownSimulationAt [first] env state := by
              apply exprIH [first] env state (by omega)
              simp only [expsWeight] at measure ⊢; omega
            intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
            obtain ⟨run, known, initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
              exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
              sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
            have ⟨headUnique, tailUnique, swappedUnique⟩ := CorrectApprox.Cons.uniqueParts [first] (second :: tail) state.compileOracle unique
            have ⟨headDisjoint, tailDisjoint⟩ :=
              (mglobalsDisjointRw state.globals first second first first first tail .none .install [] none none [] 0 0).1.mp disjoint
            have syntaxParts : everyFnVarsNone [first] ∧ everyFnVarsNone (second :: tail) := by
              simpa [everyFnVarsNone] using inputSyntax
            have headSyntax := syntaxParts.1
            have tailSyntax := syntaxParts.2
            have headSafe : ∀ e ∈ [first], esgcFree e := by simpa using exprSafe first (by simp)
            have tailSafe : ∀ e ∈ second :: tail, esgcFree e := by
              intro e member
              exact exprSafe e (List.mem_cons_of_mem _ member)
            have ⟨headFree, tailFree⟩ := (fvMaxCons env1.length first (second :: tail)).1 free
            have bagDisjoint : ∀ i, elistGlobals [first] i = 0 ∨ elistGlobals (second :: tail) i = 0 := by
              intro i
              have bound := unique 0 i
              simp only [elistGlobals_append, elistGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag,
                Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
              omega
            cases hk : knownListTotal c [first] aenv g0 with
            | mk headEas g1 =>
              obtain ⟨xe, xa, eq⟩ := knownListTotal_single_result c first aenv g0 g1 headEas hk
              subst headEas
              cases ht : knownListTotal c (second :: tail) aenv g1 with
              | mk tailEas g2 =>
                have tailNonempty : tailEas ≠ [] := by
                  intro empty
                  subst tailEas
                  have len := knownListTotal_length c (second :: tail) aenv g1
                  rw [ht] at len
                  simp at len
                rw [knownListTotal_cons_cons, hk] at known
                dsimp only at known
                rw [ht] at known
                simp only [Prod.mk.injEq] at known
                rcases known with ⟨rfl, rfl⟩
                have ⟨subHead, subTail⟩ := subsptKnownElistGlobals c [first] aenv g0 [(xe, xa)] g1
                  (second :: tail) aenv tailEas g2 ⟨hk, ht, sub0, bagDisjoint⟩
                have subHeadNext : sptSubspt g1 (nextG state) := sptSubsptTrans _ _ _ ⟨subTail, sub1⟩
                cases hr : evaluate [first] env state with
                | mk headResult middle =>
                  have headNoType : headResult ≠ .err (.abort .typeError) := by
                    intro eq
                    subst headResult
                    rw [evaluate, fixClock_evaluate, hr] at run
                    simp at run
                    rcases run with ⟨rfl, rfl⟩
                    exact noType rfl
                  have step := headIH headResult middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv [(xe, xa)]
                    ⟨hr, hk, initialRel, headSyntax, coSyntax, headDisjoint, oracle, stateOracleDisjoint,
                      headSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                      subHead, subHeadNext, mono, headFree, envRel, headUnique, stateOracle, envEq, headNoType⟩
                  obtain ⟨targetHeadResult, targetMiddle, targetHeadRun, headRel, midState, midGlobals, midStateOracle, midOracle⟩ := step
                  have targetHeadRun' : evaluate [xe] (env2 ++ xenv2) t0 = (targetHeadResult, targetMiddle) := by
                    simpa using targetHeadRun
                  rw [evaluate, fixClock_evaluate, hr] at run
                  cases headResult with
                  | err error =>
                    simp at run
                    rcases run with ⟨rfl, rfl⟩
                    cases targetHeadResult with
                    | val values => simp [resultRel] at headRel
                    | err error2 =>
                      refine ⟨.err error2, targetMiddle, ?_, headRel, midState, midGlobals, midStateOracle, midOracle⟩
                      cases tailEas with
                      | nil => contradiction
                      | cons entry rest =>
                        simp only [List.map_cons, List.cons_append, List.nil_append]
                        rw [evaluate, fixClock_evaluate, targetHeadRun']
                  | val headValues =>
                    obtain ⟨head, rfl⟩ := evaluate_singleton_value first env state middle headValues hr
                    cases targetHeadResult with
                    | err error => simp [resultRel] at headRel
                    | val targetValues =>
                      obtain ⟨targetHead, rfl⟩ := evaluate_singleton_value xe (env2 ++ xenv2) t0 targetMiddle targetValues targetHeadRun'
                      have valuesRel : ValueRel c (nextG middle) head targetHead := by
                        cases headRel with | cons rel _ => exact rel
                      have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [first] env state (.val [head]) middle
                        ⟨hr, safe, headSafe, envSafe⟩
                      have nextUnique := uniqueSetGlobalsEvaluate [first] (second :: tail) env state middle (.val [head]) ⟨tailUnique, hr⟩
                      have nextDisjoint := mglobalsDisjointEvaluate state (second :: tail) [first] env (.val [head]) middle
                        ⟨hr, safe, envSafe, headSafe, swappedUnique, tailDisjoint⟩
                      have nextStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate [first] env state (.val [head]) middle
                        ⟨hr, safe, headSafe, envSafe, headUnique, headDisjoint, stateOracleDisjoint⟩
                      obtain ⟨n, shifted⟩ := evaluateImpShiftSeq [first] env state (.val [head]) middle hr
                      have nextCoSyntax : coEveryFnVarsNone middle.compileOracle := by
                        rw [shifted]
                        exact coEveryFnVarsNoneShift state.compileOracle coSyntax n
                      have nextOracleSafe : oracleStateSgcFree middle.compileOracle := by
                        rw [shifted]
                        exact oracleStateSgcFreeShift state.compileOracle oracleSafe n
                      have nextMono : oracleGapproxSubspt middle.compileOracle :=
                        oracleGapproxSubsptEvaluate () [first] env state (.val [head]) middle ⟨mono, hr⟩
                      have nextTree := nextGEvaluateSubspt [first] env state (.val [head]) middle ⟨mono, hr⟩
                      have nextRel := valueRelListSubspt c (nextG state) env1 env2 envRel (nextG middle) nextTree
                      have nextSafe := (PreserveSafety.knownPreservesEsgcFree c [first] aenv g0 [(xe, xa)] g1
                        ⟨hk, headSafe, approxSafe, globalSafe⟩).2.2
                      cases tr : evaluate (second :: tail) env middle with
                      | mk tailResult last =>
                        have tailNoType : tailResult ≠ .err (.abort .typeError) := by
                          intro eq
                          subst tailResult
                          simp [tr] at run
                          rcases run with ⟨rfl, rfl⟩
                          exact noType rfl
                        have tailIH : KnownSimulationAt (second :: tail) env middle := by
                          have bound := evaluate_clock_le [first] env state
                          rw [hr] at bound
                          simp only at bound
                          apply exprIH (second :: tail) env middle (by omega)
                          simp only [expsWeight] at measure ⊢; omega
                        have tailStep := tailIH tailResult last
                          env1 xenv1 env2 xenv2 targetMiddle c g1 g2 aenv tailEas
                          ⟨tr, ht, midState, tailSyntax, nextCoSyntax, nextDisjoint, midOracle, nextStateOracleDisjoint,
                            tailSafe, safety.1, envSafe, approxRel, nextOracleSafe, nextSafe, approxSafe, midGlobals,
                            subTail, sptSubsptTrans _ _ _ ⟨sub1, nextTree⟩, nextMono, tailFree, nextRel, nextUnique,
                            midStateOracle, envEq, tailNoType⟩
                        obtain ⟨targetTailResult, targetLast, targetTailRun, tailRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := tailStep
                        simp only [tr] at run
                        cases tailResult with
                        | err error =>
                          simp at run
                          rcases run with ⟨rfl, rfl⟩
                          cases targetTailResult with
                          | val values => simp [resultRel] at tailRel
                          | err error2 =>
                            refine ⟨.err error2, targetLast, ?_, tailRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                            cases tailEas with
                            | nil => contradiction
                            | cons entry rest =>
                              simp only [List.map_cons, List.cons_append, List.nil_append] at targetTailRun ⊢
                              rw [evaluate, fixClock_evaluate, targetHeadRun', targetTailRun]
                        | val tailValues =>
                          simp at run
                          rcases run with ⟨rfl, rfl⟩
                          cases targetTailResult with
                          | err error => simp [resultRel] at tailRel
                          | val targetTailValues =>
                            have nextTreeFinal := nextGEvaluateSubspt (second :: tail) env middle (.val tailValues) last ⟨nextMono, tr⟩
                            have finalHeadRel := valueRelSubspt c (nextG middle) head targetHead (nextG last) ⟨valuesRel, nextTreeFinal⟩
                            refine ⟨.val (targetHead :: targetTailValues), targetLast, ?_, ?_, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                            · cases tailEas with
                              | nil => contradiction
                              | cons entry rest =>
                                simp only [List.map_cons, List.cons_append, List.nil_append] at targetTailRun ⊢
                                rw [evaluate, fixClock_evaluate, targetHeadRun', targetTailRun]
                                simp
                            · exact .cons finalHeadRel tailRel
          | nil =>
            cases first with
            | var trace index => exact knownCorrect0Var trace index env state
            | fn name location selected arity body => exact Fn.knownCorrect0Fn name location selected arity body env state
            | raise trace body =>
              have bodyIH : KnownSimulationAt [body] env state := by
                apply exprIH [body] env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
              obtain ⟨run, known, initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
                exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
              have bodySyntax : everyFnVarsNone [body] := by simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
              have bodyDisjoint : mglobalsDisjoint state.globals [body] := by
                simpa [mglobalsDisjoint, elistGlobals, setGlobals] using disjoint
              have bodySafe : ∀ e ∈ [body], esgcFree e := by
                have h := exprSafe (.raise trace body) (by simp)
                simpa [esgcFree] using h
              have bodyFree : fvMax env1.length [body] := by
                simpa [fvMax, freeVars, freeVarExp] using free
              have bodyUnique : uniqueSetGlobals [body] state.compileOracle := by
                simpa [uniqueSetGlobals, elistGlobals, setGlobals] using unique
              cases hk : knownListTotal c [body] aenv g0 with
              | mk bodyEas bodyG =>
                obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body aenv g0 bodyG bodyEas hk
                subst bodyEas
                rw [knownListTotal_raise, hk] at known
                simp [knownSourceHead] at known
                rcases known with ⟨rfl, rfl⟩
                cases hr : evaluate [body] env state with
                | mk bodyResult next =>
                  have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
                    intro eq
                    subst bodyResult
                    simp [evaluate, hr] at run
                    rcases run with ⟨rfl, rfl⟩
                    exact noType rfl
                  have step := bodyIH bodyResult next env1 xenv1 env2 xenv2 t0 c g0 bodyG aenv [(be, ba)]
                    ⟨hr, hk, initialRel, bodySyntax, coSyntax, bodyDisjoint, oracle, stateOracleDisjoint,
                      bodySafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                      sub0, sub1, mono, bodyFree, envRel, bodyUnique, stateOracle, envEq, bodyNoType⟩
                  obtain ⟨res2, t, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := step
                  cases bodyResult with
                  | err error =>
                    simp [evaluate, hr] at run
                    rcases run with ⟨rfl, rfl⟩
                    cases res2 with
                    | val vals => simp [resultRel] at result
                    | err error2 =>
                      refine ⟨.err error2, t, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                      have targetRun' : evaluate [be] (env2 ++ xenv2) t0 = (.err error2, t) := by simpa using targetRun
                      simp [evaluate, targetRun']
                  | val vals =>
                    obtain ⟨v, rfl⟩ := evaluate_singleton_value body env state next vals hr
                    simp [evaluate, hr] at run
                    rcases run with ⟨rfl, rfl⟩
                    cases res2 with
                    | err error2 => simp [resultRel] at result
                    | val values2 =>
                      obtain ⟨v2, rfl⟩ := evaluate_singleton_value be (env2 ++ xenv2) t0 t values2 (by simpa using targetRun)
                      have valRel : ValueRel c (nextG next) v v2 := by cases result with | cons rel _ => exact rel
                      refine ⟨.err (.raise v2), t, ?_, ?_, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                      · have targetRun' : evaluate [be] (env2 ++ xenv2) t0 = (.val [v2], t) := by simpa using targetRun
                        simp [evaluate, targetRun']
                      · exact valRel
            | tick trace body =>
              intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
              obtain ⟨run, known, initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
                exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
              have clockEq : state.clock = t0.clock := initialRel.2.2.2.2.1
              have bodySyntax : everyFnVarsNone [body] := by simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
              have bodyDisjoint : mglobalsDisjoint state.globals [body] := by
                simpa [mglobalsDisjoint, elistGlobals, setGlobals] using disjoint
              have bodySafe : ∀ e ∈ [body], esgcFree e := by
                have h := exprSafe (.tick trace body) (by simp)
                simpa [esgcFree] using h
              have bodyFree : fvMax env1.length [body] := by
                simpa [fvMax, freeVars, freeVarExp] using free
              have bodyUnique : uniqueSetGlobals [body] state.compileOracle := by
                simpa [uniqueSetGlobals, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
                  FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
              cases hk : knownListTotal c [body] aenv g0 with
              | mk bodyEas bodyG =>
                obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body aenv g0 bodyG bodyEas hk
                subst bodyEas
                rw [knownListTotal_tickSource, hk] at known
                simp [knownSourceHead] at known
                rcases known with ⟨rfl, rfl⟩
                by_cases zero : state.clock = 0
                · simp [evaluate, zero] at run
                  rcases run with ⟨rfl, rfl⟩
                  refine ⟨.err (.abort .timeoutError), t0, ?_, ?_, initialRel, globals, stateOracle, oracle⟩
                  · simp [evaluate, ← clockEq, zero]
                  · simp [resultRel, excRel]
                · have bodyIH : KnownSimulationAt [body] env (decClock 1 state) := by
                    apply smaller [body] env (decClock 1 state)
                    simp only [decClock]; omega
                  have bodyRun : evaluate [body] env (decClock 1 state) = (res1, s) := by
                    simpa [evaluate, zero] using run
                  have stateDec : StateRel c (nextG (decClock 1 state)) (decClock 1 state) (decClock 1 t0) := by
                    simpa [StateRel, decClock, nextG, clockEq] using initialRel
                  have step := bodyIH res1 s env1 xenv1 env2 xenv2 (decClock 1 t0) c g0 bodyG aenv [(be, ba)]
                    ⟨bodyRun, hk, stateDec, bodySyntax, by simpa [decClock] using coSyntax,
                      by simpa [decClock] using bodyDisjoint, by simpa [decClock, nextG] using oracle,
                      by simpa [decClock, stateOracleMglobalsDisjoint] using stateOracleDisjoint,
                      bodySafe, (ssgcFreeDecClock 1 state).2 safe, envSafe, approxRel,
                      by simpa [decClock] using oracleSafe, globalSafe, approxSafe,
                      by simpa [decClock, nextG, stateGlobalsApprox] using globals,
                      sub0, by simpa [decClock, nextG] using sub1, by simpa [decClock] using mono,
                      bodyFree, by simpa [decClock, nextG] using envRel, by simpa [decClock] using bodyUnique,
                      by simpa [decClock] using stateOracle, envEq, noType⟩
                  obtain ⟨res2, t, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := step
                  refine ⟨res2, t, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                  simpa [evaluate, ← clockEq, zero] using targetRun
            | «let» trace xs body =>
              have bindIH : KnownSimulationAt xs env state := by
                apply exprIH xs env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
              obtain ⟨run, known, initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
                exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
              have uniqueBoth : uniqueSetGlobals (xs ++ [body]) state.compileOracle := by
                intro n i
                have bound := unique n i
                simp only [elistGlobals_append, elistGlobals, setGlobals,
                  FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
                omega
              have ⟨bindUnique, bodyUnique, swappedUnique⟩ := CorrectApprox.Cons.uniqueParts xs [body] state.compileOracle uniqueBoth
              have ⟨bindDisjoint, bodyDisjoint⟩ :=
                (mglobalsDisjointRw state.globals body body body body body xs trace .install [] none none [] 0 0).2.1.mp disjoint
              have syntaxParts : everyFnVarsNone xs ∧ everyFnVarsNone [body] := by
                simpa [everyFnVarsNone, fnVarsNoneExp, and_comm] using inputSyntax
              have safeParts := exprSafe (.let trace xs body) (by simp)
              simp only [esgcFree, esgcFreeList_iff] at safeParts
              have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using safeParts.2
              have ⟨bindFree, bodyFree⟩ := (fvMaxLet env1.length trace xs body).1 free
              have bagDisjoint : ∀ i, elistGlobals xs i = 0 ∨ elistGlobals [body] i = 0 := by
                intro i
                have bound := uniqueBoth 0 i
                simp only [elistGlobals_append] at bound
                omega
              cases hk : knownListTotal c xs aenv g0 with
              | mk bindEas g1 =>
                cases hb : knownListTotal c [body] (bindEas.map Prod.snd ++ aenv) g1 with
                | mk bodyEas g2 =>
                  obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body (bindEas.map Prod.snd ++ aenv) g1 g2 bodyEas hb
                  subst bodyEas
                  rw [knownListTotal_let, hk] at known
                  dsimp only at known
                  rw [hb] at known
                  simp [knownSourceHead] at known
                  rcases known with ⟨rfl, rfl⟩
                  have ⟨subBind, subBody⟩ := subsptKnownElistGlobals c xs aenv g0 bindEas g1
                    [body] (bindEas.map Prod.snd ++ aenv) [(be, ba)] g2 ⟨hk, hb, sub0, bagDisjoint⟩
                  have subBindNext : sptSubspt g1 (nextG state) := sptSubsptTrans _ _ _ ⟨subBody, sub1⟩
                  have startSub : sptSubspt g0 (nextG state) := sptSubsptTrans _ _ _ ⟨sub0, sub1⟩
                  have startApprox := stateGlobalsApproxSubspt g0 (nextG state) state ⟨startSub, globals⟩
                  have startOracle := oracleGapproxDisjointSubspt g0 (nextG state) state.compileOracle ⟨startSub, oracle⟩
                  cases hr : evaluate xs env state with
                  | mk bindResult middle =>
                    rw [evaluate, fixClock_evaluate, hr] at run
                    have bindNoType : bindResult ≠ .err (.abort .typeError) := by
                      intro eq
                      subst bindResult
                      simp at run
                      rcases run with ⟨rfl, rfl⟩
                      exact noType rfl
                    have bindApprox := CorrectApprox.Total.knownCorrectApprox c xs aenv g0 bindEas g1 env1 xenv1 state
                      bindResult middle ⟨hk, by simpa [envEq] using hr, bindUnique, approxRel, startApprox,
                        bindDisjoint, startOracle, safe, by simpa [← envEq] using envSafe, safeParts.1,
                        approxSafe, globalSafe⟩
                    have bindStep := bindIH bindResult middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv bindEas
                      ⟨hr, hk, initialRel, syntaxParts.1, coSyntax, bindDisjoint, oracle, stateOracleDisjoint,
                        safeParts.1, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                        subBind, subBindNext, mono, bindFree, envRel, bindUnique, stateOracle, envEq, bindNoType⟩
                    obtain ⟨targetBindResult, targetMiddle, targetBindRun, bindRel, midState, midGlobals, midStateOracle, midOracle⟩ := bindStep
                    cases bindResult with
                    | err error =>
                      simp at run
                      rcases run with ⟨rfl, rfl⟩
                      cases targetBindResult with
                      | val values => simp [resultRel] at bindRel
                      | err error2 =>
                        refine ⟨.err error2, targetMiddle, ?_, bindRel, midState, midGlobals, midStateOracle, midOracle⟩
                        simp only [List.map_cons, List.map_nil]
                        rw [evaluate, fixClock_evaluate, targetBindRun]
                    | val values =>
                      cases targetBindResult with
                      | err error => simp [resultRel] at bindRel
                      | val targetValues =>
                        have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals xs env state (.val values) middle
                          ⟨hr, safe, safeParts.1, envSafe⟩
                        have valuesSafe : ∀ v ∈ values, vsgcFree v := by simpa [rsgcFree] using safety.2.1
                        have nextUnique := uniqueSetGlobalsEvaluate xs [body] env state middle (.val values) ⟨bodyUnique, hr⟩
                        have nextDisjoint := mglobalsDisjointEvaluate state [body] xs env (.val values) middle
                          ⟨hr, safe, envSafe, safeParts.1, swappedUnique, bodyDisjoint⟩
                        have nextStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate xs env state (.val values) middle
                          ⟨hr, safe, safeParts.1, envSafe, bindUnique, bindDisjoint, stateOracleDisjoint⟩
                        obtain ⟨n, shifted⟩ := evaluateImpShiftSeq xs env state (.val values) middle hr
                        have nextCoSyntax : coEveryFnVarsNone middle.compileOracle := by
                          rw [shifted]
                          exact coEveryFnVarsNoneShift state.compileOracle coSyntax n
                        have nextOracleSafe : oracleStateSgcFree middle.compileOracle := by
                          rw [shifted]
                          exact oracleStateSgcFreeShift state.compileOracle oracleSafe n
                        have nextMono : oracleGapproxSubspt middle.compileOracle :=
                          oracleGapproxSubsptEvaluate () xs env state (.val values) middle ⟨mono, hr⟩
                        have nextTree := nextGEvaluateSubspt xs env state (.val values) middle ⟨mono, hr⟩
                        have nextRel := valueRelListSubspt c (nextG state) env1 env2 envRel (nextG middle) nextTree
                        have optimizerSafe := PreserveSafety.knownPreservesEsgcFree c xs aenv g0 bindEas g1
                          ⟨hk, safeParts.1, approxSafe, globalSafe⟩
                        have extendSafe : ∀ v ∈ values ++ env, vsgcFree v := by
                          simpa [List.mem_append, or_imp, forall_and] using And.intro valuesSafe envSafe
                        have extendApproxSafe : ∀ a ∈ bindEas.map Prod.snd ++ aenv, valApproxSgcFree a := by
                          simpa [List.mem_append, or_imp, forall_and] using And.intro optimizerSafe.2.1 approxSafe
                        have extendApproxRel : List.Forall₂ ValApproxVal (bindEas.map Prod.snd ++ aenv) (values ++ env1) :=
                          List.rel_append (bindApprox.2 values rfl) approxRel
                        have extendEnvRel : List.Forall₂ (ValueRel c (nextG middle)) (values ++ env1) (targetValues ++ env2) :=
                          List.rel_append bindRel nextRel
                        have valueLength := evaluate_length.1 xs env state middle values hr
                        have extendedFree : fvMax (values ++ env1).length [body] := by
                          simpa [List.length_append, valueLength, Nat.add_comm] using bodyFree
                        have bodyIH : KnownSimulationAt [body] (values ++ env) middle := by
                          have bound := evaluate_clock_le xs env state
                          rw [hr] at bound
                          simp only at bound
                          apply exprIH [body] (values ++ env) middle (by omega)
                          simp only [expsWeight, expWeight] at measure ⊢; omega
                        cases bodyRun : evaluate [body] (values ++ env) middle with
                        | mk bodyResult last =>
                          have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
                            intro eq
                            subst bodyResult
                            simp [bodyRun] at run
                            rcases run with ⟨rfl, rfl⟩
                            exact noType rfl
                          have bodyStep := bodyIH bodyResult last
                            (values ++ env1) xenv1 (targetValues ++ env2) xenv2 targetMiddle c g1 g2
                            (bindEas.map Prod.snd ++ aenv) [(be, ba)]
                            ⟨bodyRun, hb, midState, syntaxParts.2, nextCoSyntax, nextDisjoint, midOracle, nextStateOracleDisjoint,
                              bodySafe, safety.1, extendSafe, extendApproxRel, nextOracleSafe, optimizerSafe.2.2, extendApproxSafe,
                              midGlobals, subBody, sptSubsptTrans _ _ _ ⟨sub1, nextTree⟩, nextMono, extendedFree, extendEnvRel,
                              nextUnique, midStateOracle, by simpa [List.append_assoc] using congrArg (values ++ ·) envEq, bodyNoType⟩
                          obtain ⟨targetBodyResult, targetLast, targetBodyRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := bodyStep
                          simp only [bodyRun] at run
                          cases bodyResult <;> cases run <;>
                            refine ⟨targetBodyResult, targetLast, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ <;>
                            simp only [List.map_cons, List.map_nil] <;>
                            rw [evaluate, fixClock_evaluate, targetBindRun] <;>
                            simpa [List.append_assoc] using targetBodyRun
            | handle trace body handler =>
              have bodyIH : KnownSimulationAt [body] env state := by
                apply exprIH [body] env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
              obtain ⟨run, known, initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
                exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
              have uniqueBoth : uniqueSetGlobals ([body] ++ [handler]) state.compileOracle := by
                intro n i
                have bound := unique n i
                simp only [elistGlobals_append, elistGlobals, setGlobals,
                  FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
                omega
              have ⟨bodyUnique, handlerUnique, swappedUnique⟩ := CorrectApprox.Cons.uniqueParts [body] [handler] state.compileOracle uniqueBoth
              have ⟨bodyDisjoint, handlerDisjoint⟩ :=
                (mglobalsDisjointRw state.globals body handler body handler body [] trace .install [] none none [] 0 0).2.2.1.mp disjoint
              have syntaxParts : everyFnVarsNone [body] ∧ everyFnVarsNone [handler] := by
                simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
              have safeParts := exprSafe (.handle trace body handler) (by simp)
              simp only [esgcFree] at safeParts
              have bodySafe : ∀ e ∈ [body], esgcFree e := by simpa using safeParts.1
              have handlerSafe : ∀ e ∈ [handler], esgcFree e := by simpa using safeParts.2
              have ⟨bodyFree, handlerFree⟩ := (fvMaxHandle env1.length trace body handler).1 free
              have bagDisjoint : ∀ i, elistGlobals [body] i = 0 ∨ elistGlobals [handler] i = 0 := by
                intro i
                have bound := uniqueBoth 0 i
                simp only [elistGlobals_append] at bound
                omega
              cases hk : knownListTotal c [body] aenv g0 with
              | mk bodyEas g1 =>
                obtain ⟨be, ba, eq⟩ := knownListTotal_single_result c body aenv g0 g1 bodyEas hk
                subst bodyEas
                cases hh : knownListTotal c [handler] (.other :: aenv) g1 with
                | mk handlerEas g2 =>
                  obtain ⟨he, ha, eq⟩ := knownListTotal_single_result c handler (.other :: aenv) g1 g2 handlerEas hh
                  subst handlerEas
                  rw [knownListTotal_handle, hk] at known
                  dsimp only at known
                  rw [hh] at known
                  simp [knownSourceHead] at known
                  rcases known with ⟨rfl, rfl⟩
                  have ⟨subBody, subHandler⟩ := subsptKnownElistGlobals c [body] aenv g0 [(be, ba)] g1
                    [handler] (.other :: aenv) [(he, ha)] g2 ⟨hk, hh, sub0, bagDisjoint⟩
                  have subBodyNext : sptSubspt g1 (nextG state) := sptSubsptTrans _ _ _ ⟨subHandler, sub1⟩
                  cases hr : evaluate [body] env state with
                  | mk bodyResult middle =>
                    rw [evaluate, fixClock_evaluate, hr] at run
                    have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
                      intro eq
                      subst bodyResult
                      simp at run
                      rcases run with ⟨rfl, rfl⟩
                      exact noType rfl
                    have bodyStep := bodyIH bodyResult middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv [(be, ba)]
                      ⟨hr, hk, initialRel, syntaxParts.1, coSyntax, bodyDisjoint, oracle, stateOracleDisjoint,
                        bodySafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                        subBody, subBodyNext, mono, bodyFree, envRel, bodyUnique, stateOracle, envEq, bodyNoType⟩
                    obtain ⟨targetBodyResult, targetMiddle, targetBodyRun, bodyRel, midState, midGlobals, midStateOracle, midOracle⟩ := bodyStep
                    have targetBodyRun' : evaluate [be] (env2 ++ xenv2) t0 = (targetBodyResult, targetMiddle) := by
                      simpa using targetBodyRun
                    cases bodyResult with
                    | val values =>
                      simp at run
                      rcases run with ⟨rfl, rfl⟩
                      cases targetBodyResult with
                      | err error => simp [resultRel] at bodyRel
                      | val targetValues =>
                        refine ⟨.val targetValues, targetMiddle, ?_, bodyRel, midState, midGlobals, midStateOracle, midOracle⟩
                        simp only [List.map_cons, List.map_nil]
                        rw [evaluate, fixClock_evaluate, targetBodyRun']
                    | err error =>
                      cases error with
                      | abort abort =>
                        simp at run
                        rcases run with ⟨rfl, rfl⟩
                        cases targetBodyResult with
                        | val values => simp [resultRel] at bodyRel
                        | err targetError =>
                          cases targetError with
                          | raise value => simp [resultRel, excRel] at bodyRel
                          | abort targetAbort =>
                            refine ⟨.err (.abort targetAbort), targetMiddle, ?_, bodyRel, midState, midGlobals, midStateOracle, midOracle⟩
                            simp only [List.map_cons, List.map_nil]
                            rw [evaluate, fixClock_evaluate, targetBodyRun']
                      | raise value =>
                        cases targetBodyResult with
                        | val values => simp [resultRel] at bodyRel
                        | err targetError =>
                          cases targetError with
                          | abort targetAbort => simp [resultRel, excRel] at bodyRel
                          | raise targetValue =>
                            have valueRel : ValueRel c (nextG middle) value targetValue := bodyRel
                            have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [body] env state (.err (.raise value)) middle
                              ⟨hr, safe, bodySafe, envSafe⟩
                            have valueSafe : vsgcFree value := by simpa [rsgcFree] using safety.2.1
                            have nextUnique := uniqueSetGlobalsEvaluate [body] [handler] env state middle (.err (.raise value)) ⟨handlerUnique, hr⟩
                            have nextDisjoint := mglobalsDisjointEvaluate state [handler] [body] env (.err (.raise value)) middle
                              ⟨hr, safe, envSafe, bodySafe, swappedUnique, handlerDisjoint⟩
                            have nextStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate [body] env state (.err (.raise value)) middle
                              ⟨hr, safe, bodySafe, envSafe, bodyUnique, bodyDisjoint, stateOracleDisjoint⟩
                            obtain ⟨n, shifted⟩ := evaluateImpShiftSeq [body] env state (.err (.raise value)) middle hr
                            have nextCoSyntax : coEveryFnVarsNone middle.compileOracle := by
                              rw [shifted]
                              exact coEveryFnVarsNoneShift state.compileOracle coSyntax n
                            have nextOracleSafe : oracleStateSgcFree middle.compileOracle := by
                              rw [shifted]
                              exact oracleStateSgcFreeShift state.compileOracle oracleSafe n
                            have nextMono : oracleGapproxSubspt middle.compileOracle :=
                              oracleGapproxSubsptEvaluate () [body] env state (.err (.raise value)) middle ⟨mono, hr⟩
                            have nextTree := nextGEvaluateSubspt [body] env state (.err (.raise value)) middle ⟨mono, hr⟩
                            have nextRel := valueRelListSubspt c (nextG state) env1 env2 envRel (nextG middle) nextTree
                            have nextSafe := (PreserveSafety.knownPreservesEsgcFree c [body] aenv g0 [(be, ba)] g1
                              ⟨hk, bodySafe, approxSafe, globalSafe⟩).2.2
                            have handlerIH : KnownSimulationAt [handler] (value :: env) middle := by
                              have bound := evaluate_clock_le [body] env state
                              rw [hr] at bound
                              simp only at bound
                              apply exprIH [handler] (value :: env) middle (by omega)
                              simp only [expsWeight, expWeight] at measure ⊢; omega
                            cases handlerRun : evaluate [handler] (value :: env) middle with
                            | mk handlerResult last =>
                              have handlerNoType : handlerResult ≠ .err (.abort .typeError) := by
                                intro eq
                                subst handlerResult
                                simp [handlerRun] at run
                                rcases run with ⟨rfl, rfl⟩
                                exact noType rfl
                              have extendedSafe : ∀ v ∈ value :: env, vsgcFree v := by
                                simpa using And.intro valueSafe envSafe
                              have extendedApproxSafe : ∀ a ∈ ValApprox.other :: aenv, valApproxSgcFree a := by
                                simpa [valApproxSgcFree] using approxSafe
                              have handlerStep := handlerIH handlerResult last (value :: env1) xenv1 (targetValue :: env2) xenv2 targetMiddle c g1 g2
                                (.other :: aenv) [(he, ha)]
                                ⟨handlerRun, hh, midState, syntaxParts.2, nextCoSyntax, nextDisjoint, midOracle, nextStateOracleDisjoint,
                                  handlerSafe, safety.1, extendedSafe, .cons (.other value) approxRel, nextOracleSafe, nextSafe,
                                  extendedApproxSafe, midGlobals, subHandler, sptSubsptTrans _ _ _ ⟨sub1, nextTree⟩, nextMono,
                                  by simpa [Nat.add_comm] using handlerFree, .cons valueRel nextRel, nextUnique, midStateOracle,
                                  by simp [envEq], handlerNoType⟩
                              obtain ⟨targetHandlerResult, targetLast, targetHandlerRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := handlerStep
                              simp only [handlerRun] at run
                              cases handlerResult <;> cases run <;>
                                refine ⟨targetHandlerResult, targetLast, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ <;>
                                simp only [List.map_cons, List.map_nil] <;>
                                rw [evaluate, fixClock_evaluate, targetBodyRun'] <;>
                                simpa using targetHandlerRun
            | ifThenElse trace cond yes no =>
              have condIH : KnownSimulationAt [cond] env state := by
                apply exprIH [cond] env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
              obtain ⟨run, known, initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
                exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
              have uniqueAll : uniqueSetGlobals ([cond] ++ ([yes] ++ [no])) state.compileOracle := by
                intro n i
                have bound := unique n i
                simp only [elistGlobals_append, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
                  FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
                omega
              have ⟨condUnique, branchesUnique, swappedUnique⟩ := CorrectApprox.Cons.uniqueParts [cond] ([yes] ++ [no]) state.compileOracle uniqueAll
              have ⟨condDisjoint, yesDisjoint, noDisjoint⟩ :=
                (mglobalsDisjointRw state.globals cond yes cond yes no [] trace .install [] none none [] 0 0).2.2.2.1.mp disjoint
              have branchesDisjoint : mglobalsDisjoint state.globals ([yes] ++ [no]) :=
                (mglobalsDisjointRw state.globals yes no yes yes yes [] trace .install [] none none [] 0 0).1.mpr
                  ⟨yesDisjoint, noDisjoint⟩
              have syntaxParts : everyFnVarsNone [cond] ∧ everyFnVarsNone [yes] ∧ everyFnVarsNone [no] := by
                simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
              have allSafe := exprSafe (.ifThenElse trace cond yes no) (by simp)
              simp only [esgcFree] at allSafe
              have condSafe : ∀ e ∈ [cond], esgcFree e := by simpa using allSafe.1
              have yesSafe : ∀ e ∈ [yes], esgcFree e := by simpa using allSafe.2.1
              have noSafe : ∀ e ∈ [no], esgcFree e := by simpa using allSafe.2.2
              have freeParts : fvMax env1.length [cond] ∧ fvMax env1.length [yes] ∧ fvMax env1.length [no] := by
                simpa [fvMax, freeVars, freeVarExp, or_imp, forall_and] using free
              have condDisjointBags : ∀ i, elistGlobals [cond] i = 0 ∨ elistGlobals ([yes] ++ [no]) i = 0 := by
                intro i
                have bound := uniqueAll 0 i
                simp only [elistGlobals_append] at bound ⊢
                omega
              have yesNoDisjointBags : ∀ i, elistGlobals [yes] i = 0 ∨ elistGlobals [no] i = 0 := by
                intro i
                have bound := branchesUnique 0 i
                simp only [elistGlobals_append] at bound
                omega
              cases hc : knownListTotal c [cond] aenv g0 with
              | mk ea1 g1 =>
                obtain ⟨ec, ac, eq1⟩ := knownListTotal_single_result c cond aenv g0 g1 ea1 hc
                subst ea1
                cases hy : knownListTotal c [yes] aenv g1 with
                | mk ea2 g2 =>
                  obtain ⟨ey, ay, eq2⟩ := knownListTotal_single_result c yes aenv g1 g2 ea2 hy
                  subst ea2
                  cases hn : knownListTotal c [no] aenv g2 with
                  | mk ea3 g3 =>
                    obtain ⟨en, an, eq3⟩ := knownListTotal_single_result c no aenv g2 g3 ea3 hn
                    subst ea3
                    have branchesKnown : knownListTotal c ([yes] ++ [no]) aenv g1 = ([(ey, ay), (en, an)], g3) := by
                      rw [show [yes] ++ [no] = yes :: no :: [] by rfl, knownListTotal_cons_cons, hy]
                      dsimp only
                      rw [hn]
                      rfl
                    rw [knownListTotal_if, hc] at known
                    dsimp only at known
                    rw [hy] at known
                    dsimp only at known
                    rw [hn] at known
                    simp [knownSourceHead] at known
                    rcases known with ⟨rfl, rfl⟩
                    have ⟨subCond, subBranches⟩ := subsptKnownElistGlobals c [cond] aenv g0 [(ec, ac)] g1
                      ([yes] ++ [no]) aenv [(ey, ay), (en, an)] g3 ⟨hc, branchesKnown, sub0, condDisjointBags⟩
                    have ⟨subYes, subNo⟩ := subsptKnownElistGlobals c [yes] aenv g1 [(ey, ay)] g2
                      [no] aenv [(en, an)] g3 ⟨hy, hn, subBranches, yesNoDisjointBags⟩
                    have subCondNext : sptSubspt g1 (nextG state) := sptSubsptTrans _ _ _ ⟨subBranches, sub1⟩
                    cases hr : evaluate [cond] env state with
                    | mk condResult middle =>
                      have middleClock : middle.clock ≤ clock := by
                        have bound := evaluate_clock_le [cond] env state
                        rw [hr] at bound
                        simp only at bound
                        omega
                      have yesIH : KnownSimulationAt [yes] env middle := by
                        apply exprIH [yes] env middle middleClock
                        simp only [expsWeight, expWeight] at measure ⊢; omega
                      have noIH : KnownSimulationAt [no] env middle := by
                        apply exprIH [no] env middle middleClock
                        simp only [expsWeight, expWeight] at measure ⊢; omega
                      rw [evaluate, fixClock_evaluate, hr] at run
                      have condNoType : condResult ≠ .err (.abort .typeError) := by
                        intro eq
                        subst condResult
                        simp at run
                        rcases run with ⟨rfl, rfl⟩
                        exact noType rfl
                      have condStep := condIH condResult middle env1 xenv1 env2 xenv2 t0 c g0 g1 aenv [(ec, ac)]
                        ⟨hr, hc, initialRel, syntaxParts.1, coSyntax, condDisjoint, oracle, stateOracleDisjoint,
                          condSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                          subCond, subCondNext, mono, freeParts.1, envRel, condUnique, stateOracle, envEq, condNoType⟩
                      obtain ⟨targetCondResult, targetMiddle, targetCondRun, condRel, midState, midGlobals, midStateOracle, midOracle⟩ := condStep
                      have targetCondRun' : evaluate [ec] (env2 ++ xenv2) t0 = (targetCondResult, targetMiddle) := by simpa using targetCondRun
                      cases condResult with
                      | err error =>
                        simp at run
                        rcases run with ⟨rfl, rfl⟩
                        cases targetCondResult with
                        | val values => simp [resultRel] at condRel
                        | err error2 =>
                          refine ⟨.err error2, targetMiddle, ?_, condRel, midState, midGlobals, midStateOracle, midOracle⟩
                          simp only [List.map_cons, List.map_nil]
                          rw [evaluate, fixClock_evaluate, targetCondRun']
                      | val values =>
                        obtain ⟨value, rfl⟩ := evaluate_singleton_value cond env state middle values hr
                        cases targetCondResult with
                        | err error => simp [resultRel] at condRel
                        | val targetValues =>
                          obtain ⟨targetValue, rfl⟩ := evaluate_singleton_value ec (env2 ++ xenv2) t0 targetMiddle targetValues targetCondRun'
                          have valRel : ValueRel c (nextG middle) value targetValue := by cases condRel with | cons rel _ => exact rel
                          have safety := EvaluateGlobalsPort.Total.evaluateChangedGlobals [cond] env state (.val [value]) middle
                            ⟨hr, safe, condSafe, envSafe⟩
                          have middleUnique := uniqueSetGlobalsEvaluate [cond] ([yes] ++ [no]) env state middle
                            (.val [value]) ⟨branchesUnique, hr⟩
                          have ⟨yesUnique, noUnique, _⟩ := CorrectApprox.Cons.uniqueParts [yes] [no] middle.compileOracle middleUnique
                          have middleDisjoint := mglobalsDisjointEvaluate state ([yes] ++ [no]) [cond] env
                            (.val [value]) middle ⟨hr, safe, envSafe, condSafe, swappedUnique, branchesDisjoint⟩
                          have ⟨yesDisjoint', noDisjoint'⟩ :=
                            (mglobalsDisjointRw middle.globals yes no yes yes yes [] trace .install [] none none [] 0 0).1.mp middleDisjoint
                          have nextStateOracleDisjoint := stateOracleMglobalsDisjointEvaluate [cond] env state (.val [value]) middle
                            ⟨hr, safe, condSafe, envSafe, condUnique, condDisjoint, stateOracleDisjoint⟩
                          obtain ⟨n, shifted⟩ := evaluateImpShiftSeq [cond] env state (.val [value]) middle hr
                          have nextCoSyntax : coEveryFnVarsNone middle.compileOracle := by
                            rw [shifted]; exact coEveryFnVarsNoneShift state.compileOracle coSyntax n
                          have nextOracleSafe : oracleStateSgcFree middle.compileOracle := by
                            rw [shifted]; exact oracleStateSgcFreeShift state.compileOracle oracleSafe n
                          have nextMono : oracleGapproxSubspt middle.compileOracle :=
                            oracleGapproxSubsptEvaluate () [cond] env state (.val [value]) middle ⟨mono, hr⟩
                          have nextTree := nextGEvaluateSubspt [cond] env state (.val [value]) middle ⟨mono, hr⟩
                          have nextRel := valueRelListSubspt c (nextG state) env1 env2 envRel (nextG middle) nextTree
                          have nextSafe := (PreserveSafety.knownPreservesEsgcFree c [cond] aenv g0 [(ec, ac)] g1
                            ⟨hc, condSafe, approxSafe, globalSafe⟩).2.2
                          change (match asBool value with
                            | none => (.err (.abort .typeError), middle)
                            | some true => evaluate [yes] env middle
                            | some false => evaluate [no] env middle) = (res1, s) at run
                          cases decoded : asBool value with
                          | none =>
                            simp [decoded] at run
                            rcases run with ⟨rfl, rfl⟩
                            exact False.elim (noType rfl)
                          | some flag =>
                            have valueEq := (asBool_eq_some value flag).1 decoded
                            subst value
                            have targetEq : targetValue = ClosSem.boolValue flag := (valueRelBool c (nextG middle) flag targetValue).1.mp valRel
                            subst targetValue
                            cases flag with
                            | true =>
                              simp only [decoded] at run
                              cases yesRun : evaluate [yes] env middle with
                              | mk yesResult last =>
                                have yesNoType : yesResult ≠ .err (.abort .typeError) := by
                                  intro eq; subst yesResult; rw [yesRun] at run; cases run; exact noType rfl
                                have yesStep := yesIH yesResult last env1 xenv1 env2 xenv2 targetMiddle c g1 g2 aenv [(ey, ay)]
                                  ⟨yesRun, hy, midState, syntaxParts.2.1, nextCoSyntax, yesDisjoint', midOracle, nextStateOracleDisjoint,
                                    yesSafe, safety.1, envSafe, approxRel, nextOracleSafe, nextSafe, approxSafe, midGlobals,
                                    subYes, sptSubsptTrans _ _ _ ⟨sptSubsptTrans _ _ _ ⟨subNo, sub1⟩, nextTree⟩, nextMono, freeParts.2.1,
                                    nextRel, yesUnique, midStateOracle, envEq, yesNoType⟩
                                obtain ⟨res2, targetLast, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := yesStep
                                rw [yesRun] at run
                                cases yesResult <;> cases run <;>
                                  refine ⟨res2, targetLast, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ <;>
                                  simp only [List.map_cons, List.map_nil] <;>
                                  rw [evaluate, fixClock_evaluate, targetCondRun'] <;>
                                  simpa [asBool, ClosSem.boolValue, BackendCommon.trueTag] using targetRun
                            | false =>
                              simp only [decoded] at run
                              have g2Safe := (PreserveSafety.knownPreservesEsgcFree c [yes] aenv g1 [(ey, ay)] g2
                                ⟨hy, yesSafe, approxSafe, nextSafe⟩).2.2
                              cases noRun : evaluate [no] env middle with
                              | mk noResult last =>
                                have noNoType : noResult ≠ .err (.abort .typeError) := by
                                  intro eq; subst noResult; rw [noRun] at run; cases run; exact noType rfl
                                have noStep := noIH noResult last env1 xenv1 env2 xenv2 targetMiddle c g2 g3 aenv [(en, an)]
                                  ⟨noRun, hn, midState, syntaxParts.2.2, nextCoSyntax, noDisjoint', midOracle, nextStateOracleDisjoint,
                                    noSafe, safety.1, envSafe, approxRel, nextOracleSafe, g2Safe, approxSafe, midGlobals,
                                    subNo, sptSubsptTrans _ _ _ ⟨sub1, nextTree⟩, nextMono, freeParts.2.2,
                                    nextRel, noUnique, midStateOracle, envEq, noNoType⟩
                                obtain ⟨res2, targetLast, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := noStep
                                rw [noRun] at run
                                cases noResult <;> cases run <;>
                                  refine ⟨res2, targetLast, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ <;>
                                  simp only [List.map_cons, List.map_nil] <;>
                                  rw [evaluate, fixClock_evaluate, targetCondRun'] <;>
                                  simpa [asBool, ClosSem.boolValue, BackendCommon.falseTag] using targetRun
            | letrec names location selected functions body =>
              intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
              obtain ⟨run, known, initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
                exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
              have syntaxParts : selected = none ∧ fnVarsNoneFuns functions ∧ everyFnVarsNone [body] := by
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
              have fnSyntax := fnSyntaxAux functions fnsSyntax
              subst selected
              have safeParts : funGlobals functions = FlatProps.emptyGlobalBag ∧ esgcFree body := by
                simpa [esgcFree] using exprSafe (.letrec names location none functions body) (by simp)
              let clos := match location with | none => List.replicate functions.length ValApprox.other | some n => closGenNoInline n 0 functions
              let newFns := functions.map (fun (n, e) =>
                (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ aenv) g0).1).1))
              have closSafe : ∀ a ∈ clos, valApproxSgcFree a := by
                cases location with
                | none => simp [clos, valApproxSgcFree]
                | some n => exact closGenNoInlineSafe n 0 functions
              have subStart : sptSubspt g0 (nextG state) := sptSubsptTrans _ _ _ ⟨sub0, sub1⟩
              have fnRel : List.Forall₂ (fRel c (clos ++ aenv) (nextG state)) functions newFns :=
                Letrec.optimizedFunctionsRelated c functions clos aenv g0 (nextG state) safeParts.1 closSafe approxSafe globalSafe subStart
              have freeParts := (fvMaxLetrec env1.length names location none functions body).1 free
              have fnFree : ∀ f ∈ functions, fvMax (f.1 + functions.length + env1.length) [f.2] := by
                intro f member
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using freeParts.1 f member
              let recs1 := (List.range functions.length).map (fun i => ClosSem.Value.recclosure location [] env functions i)
              let recs2 := (List.range functions.length).map (fun i => ClosSem.Value.recclosure location [] (env2 ++ xenv2) newFns i)
              have recRel : List.Forall₂ (ValueRel c (nextG state)) recs1 recs2 := by
                simpa [recs1, recs2, envEq, clos] using Letrec.recursiveClosuresRelated c (nextG state) location functions newFns
                  env1 xenv1 env2 xenv2 aenv fnSyntax fnFree envRel approxRel (by cases location <;> simpa [clos] using fnRel)
                  (List.range functions.length)
              have recApprox : List.Forall₂ ValApproxVal clos recs1 := by
                exact CorrectApprox.Letrec.recClosuresApprox location env functions
              have recSafe : ∀ v ∈ recs1, vsgcFree v := by
                intro v member
                obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
                simpa [recs1, vsgcFree, ← funGlobals_eq_elist] using And.intro safeParts.1 envSafe
              have bodyUnique : uniqueSetGlobals [body] state.compileOracle := by
                simpa [uniqueSetGlobals, elistGlobals, setGlobals, safeParts.1,
                  FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
              have bodyDisjoint : mglobalsDisjoint state.globals [body] := by
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
                  ([(.letrec names location none fs (knownSourceHead ea).1, (knownSourceHead ea).2)], gg)) = (eas, g) at known
                dsimp only at known
                rw [hk] at known
                simp [knownSourceHead] at known
                rcases known with ⟨rfl, rfl⟩
                by_cases valid : (functions.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0)) = true
                · have ih : KnownSimulationAt [body] (recs1 ++ env) state := by
                    apply exprIH [body] (recs1 ++ env) state (by omega)
                    simp only [expsWeight, expWeight] at measure ⊢; omega
                  have bodyRun : evaluate [body] (recs1 ++ env) state = (res1, s) := by
                    simpa [evaluate, valid, recs1] using run
                  have bodyEnvSafe : ∀ v ∈ recs1 ++ env, vsgcFree v := by
                    simpa [envEq, List.append_assoc] using extendedSafe
                  have bodyFree : fvMax (recs1 ++ env1).length [body] := by
                    simpa [recs1, Nat.add_comm] using freeParts.2
                  have result := ih res1 s (recs1 ++ env1) xenv1 (recs2 ++ env2) xenv2 t0 c g0 bodyG
                    (clos ++ aenv) [(bodyExpr, bodyApprox)]
                    ⟨bodyRun, hk, initialRel, bodySyntax, coSyntax, bodyDisjoint, oracle, stateOracleDisjoint,
                      bodySafe, safe, bodyEnvSafe, List.rel_append recApprox approxRel, oracleSafe, globalSafe,
                      extendedApproxSafe, globals, sub0, sub1, mono, bodyFree, List.rel_append recRel envRel,
                      bodyUnique, stateOracle, by simp [envEq, List.append_assoc], noType⟩
                  obtain ⟨res2, t, targetRun, related, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := result
                  refine ⟨res2, t, ?_, related, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                  have maxEq : state.maxApp = t0.maxApp := initialRel.2.2.2.2.2.2.1
                  have targetValid : (newFns.all (fun (arity, _) => arity ≤ t0.maxApp && arity != 0)) = true := by
                    simpa [newFns, List.all_map, ← maxEq] using valid
                  simp only [List.map_cons, List.map_nil, evaluate, targetValid, if_true]
                  simpa [recs2, newFns, List.append_assoc] using targetRun
                · simp [evaluate, valid] at run
                  rcases run with ⟨rfl, rfl⟩
                  exact False.elim (noType rfl)
            | call trace ticks location args =>
              have argsIH : KnownSimulationAt args env state := by
                apply exprIH args env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              intro res1 s env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
              obtain ⟨run, known, initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
                exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
              have argsSyntax : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using inputSyntax
              have argsDisjoint : mglobalsDisjoint state.globals args := by
                simpa [mglobalsDisjoint, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
                  FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using disjoint
              have argsSafe : ∀ e ∈ args, esgcFree e := by
                have h := exprSafe (.call trace ticks location args) (by simp)
                simpa [esgcFree, esgcFreeList_iff] using h
              have argsFree : fvMax env1.length args := by
                simpa [fvMax, freeVars, freeVarExp] using free
              have argsUnique : uniqueSetGlobals args state.compileOracle := by
                simpa [uniqueSetGlobals, elistGlobals_append, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
                  FlatProps.emptyGlobalBag, Flapjack.bagUnion, Flapjack.emptyBag] using unique
              cases hk : knownListTotal c args aenv g0 with
              | mk ea g1 =>
                rw [knownListTotal_call, hk] at known
                simp at known
                rcases known with ⟨rfl, rfl⟩
                cases hr : evaluate args env state with
                | mk argResult next =>
                  rw [evaluate, fixClock_evaluate, hr] at run
                  have argsNoType : argResult ≠ .err (.abort .typeError) := by
                    intro eq
                    subst argResult
                    simp at run
                    rcases run with ⟨rfl, rfl⟩
                    exact noType rfl
                  have step := argsIH argResult next env1 xenv1 env2 xenv2 t0 c g0 g1 aenv ea
                    ⟨hr, hk, initialRel, argsSyntax, coSyntax, argsDisjoint, oracle, stateOracleDisjoint,
                      argsSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                      sub0, sub1, mono, argsFree, envRel, argsUnique, stateOracle, envEq, argsNoType⟩
                  obtain ⟨res2, t, targetRun, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := step
                  cases argResult with
                  | err error =>
                    simp at run
                    rcases run with ⟨rfl, rfl⟩
                    cases res2 with
                    | val vals => simp [resultRel] at result
                    | err error2 =>
                      refine ⟨.err error2, t, ?_, result, finalState, finalGlobals, finalOracle, finalDisjoint⟩
                      simp only [List.map_cons, List.map_nil]
                      rw [evaluate, fixClock_evaluate, targetRun]
                  | val values =>
                    have emptyCode : next.code = HolFiniteMapExact.empty := finalState.2.2.1
                    have absent : findCode location values next.code = none := by simp [findCode, emptyCode, HolFiniteMapExact.empty]
                    simp [absent] at run
                    rcases run with ⟨rfl, rfl⟩
                    exact False.elim (noType rfl)
            | app trace location function args =>
              intro result final env1 xenv1 env2 xenv2 t0 c g0 g aenv eas h
              obtain ⟨run, known, initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint,
                exprSafe, safe, envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals,
                sub0, sub1, mono, free, envRel, unique, stateOracle, envEq, noType⟩ := h
              cases args with
              | nil =>
                simp [evaluate] at run
                rcases run with ⟨rfl, rfl⟩
                exact False.elim (noType rfl)
              | cons first rest =>
                have argsInd : KnownSimulationAt (first :: rest) env state := by
                  apply exprIH (first :: rest) env state (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                have fnInd : ∀ middle values, evaluate (first :: rest) env state = (.val values, middle) →
                    KnownSimulationAt [function] env middle := by
                  intro middle values hr
                  have bound := evaluate_clock_le (first :: rest) env state
                  rw [hr] at bound
                  simp only at bound
                  apply exprIH [function] env middle (by omega)
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                have appInd : ∀ middle values next fn, evaluate (first :: rest) env state = (.val values, middle) →
                    evaluate [function] env middle = (.val [fn], next) → KnownAppSimulationAt location fn values next := by
                  intro middle values next fn hr hf
                  have bound1 := evaluate_clock_le (first :: rest) env state
                  rw [hr] at bound1
                  simp only at bound1
                  have bound2 := evaluate_clock_le [function] env middle
                  rw [hf] at bound2
                  simp only at bound2
                  exact appBound location fn values next (by omega)
                cases ha : knownListTotal c (first :: rest) aenv g0 with
                | mk argsEas g1 =>
                  cases hf : knownListTotal c [function] aenv g1 with
                  | mk fnEas g2 =>
                    obtain ⟨fnExp, fnApprox, eq⟩ := knownListTotal_single_result c function aenv g1 g2 fnEas hf
                    subst fnEas
                    rw [knownListTotal_app, ha] at known
                    dsimp only at known
                    rw [hf] at known
                    simp only [knownSourceHead, List.headD_cons] at known
                    cases hd : decideInlineHOL c fnApprox location (first :: rest).length with
                    | nothing =>
                      simp only [List.length_cons] at hd
                      simp [hd] at known
                      rcases known with ⟨rfl, rfl⟩
                      simpa using AppNonInline.nonInlineApplicationSimulation trace location location function first rest
                        env env1 xenv1 env2 xenv2 state final t0 result c aenv g0 g1 g2 argsEas fnExp fnApprox
                        argsInd fnInd appInd ha hf (Or.inl rfl) run noType
                        ⟨initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint, exprSafe, safe,
                          envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals, sub0, sub1, mono,
                          free, envRel, unique, stateOracle, envEq⟩
                    | annotate address =>
                      simp only [List.length_cons] at hd
                      simp [hd] at known
                      rcases known with ⟨rfl, rfl⟩
                      simpa using AppNonInline.nonInlineApplicationSimulation trace location (some address) function first rest
                        env env1 xenv1 env2 xenv2 state final t0 result c aenv g0 g1 g2 argsEas fnExp fnApprox
                        argsInd fnInd appInd ha hf (Or.inr ⟨address, rfl, hd⟩) run noType
                        ⟨initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint, exprSafe, safe,
                          envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals, sub0, sub1, mono,
                          free, envRel, unique, stateOracle, envEq⟩
                    | letInline body =>
                      simp only [List.length_cons] at hd
                      cases hb : knownListTotal (decInlineFactor c) [body] (argsEas.map Prod.snd) g2 with
                      | mk bodyEas after =>
                        obtain ⟨targetBody, bodyApprox, eq⟩ := knownListTotal_single_result (decInlineFactor c) body
                          (argsEas.map Prod.snd) g2 after bodyEas hb
                        subst bodyEas
                        simp [hd, hb] at known
                        rcases known with ⟨rfl, rfl⟩
                        simpa using AppInline.inlineApplicationSimulation trace location function first rest env env1 xenv1 env2 xenv2
                          state final t0 result c aenv g0 g1 g2 argsEas fnExp fnApprox body targetBody bodyApprox after
                          argsInd fnInd appInd ha hf hd hb run noType
                          ⟨initialRel, inputSyntax, coSyntax, disjoint, oracle, stateOracleDisjoint, exprSafe, safe,
                            envSafe, approxRel, oracleSafe, globalSafe, approxSafe, globals, sub0, sub1, mono,
                            free, envRel, unique, stateOracle, envEq⟩
            | op trace op args =>
              have argsIH : KnownSimulationAt args env state := by
                apply exprIH args env state (by omega)
                have opBound := opWeight_gt trace op args
                simp only [expsWeight] at measure
                omega
              cases op with
              | label label => exact Ordinary.knownCorrect0OpLabel trace label args env state argsIH
              | ffi name => exact Ordinary.knownCorrect0OpFfi trace name args env state argsIH
              | intOp operation => exact Ordinary.knownCorrect0OpInt trace operation args env state argsIH
              | wordOp operation => exact Ordinary.knownCorrect0OpWord trace operation args env state argsIH
              | blockOp operation => exact Ordinary.knownCorrect0OpBlock trace operation args env state argsIH
              | memOp operation => exact Ordinary.knownCorrect0OpMemory trace operation args env state argsIH
              | globOp operation =>
                cases operation with
                | global index => exact Global.knownCorrect0OpGlobal trace index args env state argsIH
                | setGlobal index => exact SetGlobal.knownCorrect0OpSetGlobal trace index args env state argsIH
                | allocGlobal => exact Ordinary.knownCorrect0OpAllocGlobal trace args env state argsIH
                | globalsPtr => exact Ordinary.knownCorrect0OpGlobalsPtr trace args env state argsIH
                | setGlobalsPtr => exact Ordinary.knownCorrect0OpSetGlobalsPtr trace args env state argsIH
              | install =>
                apply Install.knownCorrect0OpInstall trace args env state ?_ argsIH
                intro values middle program installed run install
                have bound := evaluate_clock_le args env state
                rw [run] at bound
                simp only at bound
                have installClock := doInstall_success_clock values.reverse middle installed program install
                apply smaller program [] installed
                omega
              | thunkOp operation =>
                cases operation with
                | allocThunk mode => exact Ordinary.knownCorrect0OpAllocThunk trace mode args env state argsIH
                | updateThunk mode => exact Ordinary.knownCorrect0OpUpdateThunk trace mode args env state argsIH
                | forceThunk =>
                  apply Force.knownCorrect0OpForce trace args env state ?_ argsIH
                  intro values middle value run found
                  have bound := evaluate_clock_le args env state
                  rw [run] at bound
                  simp only at bound
                  apply exprIH [appUnit (.var .none 0)] [value] middle (by omega)
                  have hweight := appUnit_var_weight
                  simp only [expsWeight, expWeight] at measure
                  simp only [appUnit, expsWeight, expWeight] at hweight ⊢
                  omega

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The source optimizer's mutual expression and application simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0 {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (state : State (Spt ValApprox × C) F), KnownSimulationAt expressions env state) ∧
    (∀ (location : Option Nat) (fn : ClosSem.Value) (args : List ClosSem.Value)
      (state : State (Spt ValApprox × C) F), KnownAppSimulationAt location fn args state) := by
  constructor
  · intro expressions env state
    exact (simulationAll state.clock).2 _ expressions env state rfl rfl
  · intro location fn args state
    exact (simulationAll state.clock).1 location fn args state rfl

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Total
