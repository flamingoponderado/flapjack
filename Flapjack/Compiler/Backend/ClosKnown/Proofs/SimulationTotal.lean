module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApp
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApplyFullBody
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationCons
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationBool
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBoolean
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationLetrec
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationRaise
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationHandle
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationTick
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationCall
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationOp

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
        apply ApplyFull.knownCorrect0AppCons location f first rest state ?_ ?_
        · intro kind body env remaining bodyResult middle values value tail h
          obtain ⟨found, rfl, enough, run, rfl, rfl, rfl⟩ := h
          have shorter := destClosure_full_remaining_lt _ _ _ _ _ _ _ found
          have bound := evaluate_clock_le [body] env (decClock ((first :: rest).length - remaining.length) state)
          rw [run] at bound
          simp only at bound
          have small : middle.clock < clock := by simp only [decClock] at bound; omega
          exact (clockIH _ small).1 location value remaining middle rfl
        · intro kind body env remaining h
          obtain ⟨found, rfl, enough⟩ := h
          have shorter := destClosure_full_remaining_lt _ _ _ _ _ _ _ found
          have small : (decClock ((first :: rest).length - remaining.length) state).clock < clock := by
            simp only [decClock]; omega
          exact (clockIH _ small).2 _ [body] env _ rfl rfl
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
            apply Cons.knownCorrect0Cons first second tail env state ?_ ?_
            · intro result next values ⟨run, _⟩
              have bound := evaluate_clock_le [first] env state
              rw [run] at bound
              simp only at bound
              apply exprIH (second :: tail) env next (by omega)
              simp only [expsWeight] at measure ⊢; omega
            · apply exprIH [first] env state (by omega)
              simp only [expsWeight] at measure ⊢; omega
          | nil =>
            cases first with
            | var trace index => exact knownCorrect0Var trace index env state
            | fn name location selected arity body => exact Fn.knownCorrect0Fn name location selected arity body env state
            | raise trace body =>
              apply Raise.knownCorrect0Raise trace body env state
              apply exprIH [body] env state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | tick trace body =>
              apply Tick.knownCorrect0Tick trace body env state
              intro nonzero
              apply smaller [body] env (decClock 1 state)
              simp only [decClock]; omega
            | «let» trace bindings body =>
              apply Let.knownCorrect0Let trace bindings body env state ?_ ?_
              · intro result next values ⟨run, _⟩
                have bound := evaluate_clock_le bindings env state
                rw [run] at bound
                simp only at bound
                apply exprIH [body] (values ++ env) next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · apply exprIH bindings env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | handle trace body handler =>
              apply Handle.knownCorrect0Handle trace body handler env state ?_ ?_
              · intro result next error value ⟨run, _, _⟩
                have bound := evaluate_clock_le [body] env state
                rw [run] at bound
                simp only at bound
                apply exprIH [handler] (value :: env) next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · apply exprIH [body] env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
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
              apply Letrec.knownCorrect0Letrec names location selected functions body env state
              intro buildRc envdelta ed _
              apply exprIH [body] (ed ++ env) state (by omega)
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | call trace ticks location args =>
              apply Call.knownCorrect0Call trace ticks location args env state ?_ ?_
              · intro result next values entry callArgs body ⟨run, _, _, _, _⟩
                have bound := evaluate_clock_le args env state
                rw [run] at bound
                simp only at bound
                apply smaller [body] callArgs (decClock (ticks + 1) next)
                simp only [decClock]; omega
              · apply exprIH args env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | app trace location function args =>
              apply App.knownCorrect0App trace location function args env state ?_ ?_ ?_
              · intro argResult next values fnResult last functions ⟨_, argsRun, _, fnRun, _⟩
                have bound1 := evaluate_clock_le args env state
                rw [argsRun] at bound1
                simp only at bound1
                have bound2 := evaluate_clock_le [function] env next
                rw [fnRun] at bound2
                simp only at bound2
                exact appBound location _ values last (by omega)
              · intro result next values ⟨_, run, _⟩
                have bound := evaluate_clock_le args env state
                rw [run] at bound
                simp only at bound
                apply exprIH [function] env next (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro _
                apply exprIH args env state (by omega)
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | op trace op args =>
              apply Op.knownCorrect0Op trace op args env state ?_ ?_ ?_
              · intro result next values installResult installed program ⟨run, _, _, installRun, success⟩
                subst installResult
                have bound := evaluate_clock_le args env state
                rw [run] at bound
                simp only at bound
                have installClock := doInstall_success_clock values.reverse next installed program installRun
                apply smaller program [] installed
                omega
              · intro result next values mode value ⟨run, _, _, opEq, _, _⟩
                have bound := evaluate_clock_le args env state
                rw [run] at bound
                simp only at bound
                apply exprIH [appUnit (.var .none 0)] [value] next (by omega)
                subst op
                have hweight := appUnit_var_weight
                simp only [expsWeight, expWeight] at measure
                simp only [appUnit, expsWeight, expWeight] at hweight ⊢
                omega
              · apply exprIH args env state (by omega)
                have opBound := opWeight_gt trace op args
                simp only [expsWeight] at measure
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
