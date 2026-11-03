import Flapjack.Compiler.Backend.ClosKnown.Proofs.Simulation
import Flapjack.Compiler.Backend.Semantics.ClosProps.ClosureLocation

/-! Partial closure applications in known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyPartial
open ClosSem ClosProps Relations Relations.StateRelation BackendProps OracleGlobals
open Flapjack.SemanticPrimitivesProps

/-- A partial application cannot use the special full-application argument
approximation, and its source call is not directly annotated. This is
Flapjack induction infrastructure. -/
theorem partialApplicationInputs (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (loc : Option Nat) (source target : Value) (args : List Value)
    (argsopt : Option (List Value)) (partialValue : Value)
    (related : valueRelApp c g source target argsopt)
    (constraint : argsopt.isSome → argsopt = some args ∧ args ≠ [] ∧ ∃ body env,
      destClosure maxApp loc source args = some (.fullApp body env []))
    (found : destClosure maxApp loc source args = some (.partialApp partialValue)) :
    argsopt = none ∧ loc = none ∧ ValueRel c g source target := by
  have noneLoc := (destClosureNoneLoc maxApp loc source args partialValue (.var .none 0) [] []).1 found
  have noApprox : argsopt = none := by
    cases argsopt with
    | none => rfl
    | some values =>
      obtain ⟨_, _, body, env, full⟩ := constraint (by simp)
      rw [found] at full
      cases full
  subst argsopt
  exact ⟨rfl, noneLoc, by simpa [valueRelAppNone] using related⟩

/-- A partial application of related ordinary closures produces related
closures. This is Flapjack induction infrastructure. -/
theorem relatedPartialClosure (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (location requested : Option Nat) (supplied captured args targetArgs : List Value)
    (arity : Nat) (body : ClosLang.Exp) (target partialValue : Value)
    (related : ValueRel c g (.closure location supplied captured arity body) target)
    (argsRelated : List.Forall₂ (ValueRel c g) args targetArgs)
    (locRelated : loptRel target args.length none requested)
    (found : destClosure maxApp none (.closure location supplied captured arity body) args =
      some (.partialApp partialValue)) :
    ∃ targetValue, destClosure maxApp requested target targetArgs = some (.partialApp targetValue) ∧
      ValueRel c g partialValue targetValue := by
  cases related with
  | closure location supplied supplied2 env1a env1b env2a env2b arity body body2 aenv
      safe fv suppliedRelated envRelated approx bodyRelated =>
    have lengths := argsRelated.length_eq
    have suppliedLengths := suppliedRelated.length_eq
    simp only [destClosure, checkLoc] at found
    split at found
    · rename_i valid
      split at found
      · rename_i partialCase
        simp only [Option.some.injEq, AppKind.partialApp.injEq] at found
        subst partialValue
        have requestedNone : requested = none := by
          rcases locRelated with equal | ⟨_, extra⟩
          · exact equal
          · cases requested with
            | none => rfl
            | some addr =>
              cases location <;> simp_all
        subst requested
        refine ⟨.closure location (targetArgs ++ supplied2) (env2a ++ env2b) arity body2, ?_, ?_⟩
        · simp only [destClosure, checkLoc]
          simp_all
        · exact ValueRel.closure location (args ++ supplied) (targetArgs ++ supplied2)
            env1a env1b env2a env2b arity body body2 aenv safe fv
            (List.rel_append argsRelated suppliedRelated) envRelated approx bodyRelated
      · simp at found
    · simp at found

/-- The ordinary-closure partial-application branch preserves the simulation
result, clock, state and oracle invariants. This is Flapjack induction
infrastructure for the nonempty application case. -/
theorem partialClosureSimulation {C F : Type} (c : Config)
    (source : State (Spt ValApprox × C) F) (target : State C F)
    (loc1 loc2 closureLoc : Option Nat) (supplied captured : List Value)
    (arity : Nat) (body : ClosLang.Exp) (targetFn : Value)
    (first : Value) (rest targetArgs : List Value) (argsopt : Option (List Value))
    (partialValue : Value)
    (states : StateRel c (nextG source) source target)
    (fnRelated : valueRelApp c (nextG source) (.closure closureLoc supplied captured arity body) targetFn argsopt)
    (argsRelated : List.Forall₂ (ValueRel c (nextG source)) (first :: rest) targetArgs)
    (locRelated : loptRel targetFn (first :: rest).length loc1 loc2)
    (constraint : argsopt.isSome → argsopt = some (first :: rest) ∧ (first :: rest) ≠ [] ∧ ∃ exp env,
      destClosure source.maxApp loc1 (.closure closureLoc supplied captured arity body) (first :: rest) =
        some (.fullApp exp env []))
    (found : destClosure source.maxApp loc1 (.closure closureLoc supplied captured arity body) (first :: rest) =
      some (.partialApp partialValue))
    (globals : stateGlobalsApprox source (nextG source))
    (oracle : isStateOracle (compileInc c) source.compileOracle)
    (oracleDisjoint : oracleGapproxDisjoint (nextG source) source.compileOracle) :
    ∃ sourceResult sourceFinal targetResult targetFinal,
      evaluateApp loc1 (.closure closureLoc supplied captured arity body) (first :: rest) source =
        (sourceResult, sourceFinal) ∧
      evaluateApp loc2 targetFn targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG sourceFinal))) (ValueRel c (nextG sourceFinal))
        sourceResult targetResult ∧ StateRel c (nextG sourceFinal) sourceFinal targetFinal ∧
      stateGlobalsApprox sourceFinal (nextG sourceFinal) ∧
      isStateOracle (compileInc c) sourceFinal.compileOracle ∧
      oracleGapproxDisjoint (nextG sourceFinal) sourceFinal.compileOracle := by
  obtain ⟨_, locEq, fnRel⟩ := partialApplicationInputs c (nextG source) source.maxApp loc1
    (.closure closureLoc supplied captured arity body) targetFn (first :: rest) argsopt partialValue
    fnRelated constraint found
  subst loc1
  have maxEq : source.maxApp = target.maxApp := states.2.2.2.2.2.2.1
  have clockEq : source.clock = target.clock := states.2.2.2.2.1
  obtain ⟨targetValue, targetFound, valueRel⟩ := relatedPartialClosure c (nextG source) source.maxApp
    closureLoc loc2 supplied captured (first :: rest) targetArgs arity body targetFn partialValue
    fnRel argsRelated locRelated found
  have targetNonempty : targetArgs ≠ [] := by
    intro eq
    subst targetArgs
    cases argsRelated
  cases targetArgs with
  | nil => contradiction
  | cons targetFirst targetRest =>
    have len := argsRelated.length_eq
    rw [evaluateApp, found]
    rw [evaluateApp, ← maxEq, targetFound]
    by_cases timeout : source.clock < (first :: rest).length
    · have targetTimeout : target.clock < (targetFirst :: targetRest).length := by omega
      refine ⟨.err (.abort .timeoutError), { source with clock := 0 },
        .err (.abort .timeoutError), { target with clock := 0 }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons] at timeout
        simp [timeout]
      · simp only [List.length_cons] at targetTimeout
        simp [targetTimeout, maxEq]
      · simp [resultRel, excRel]
      · rcases states with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globs, refs, compiler, co⟩
        exact ⟨aux, free, codeS, codeT, rfl, ffi, maxApp, globs, refs, compiler, co⟩
      · simpa [stateGlobalsApprox, nextG] using globals
      · exact oracle
      · simpa [nextG] using oracleDisjoint
    · have targetTimeout : ¬ target.clock < (targetFirst :: targetRest).length := by omega
      refine ⟨.val [partialValue], decClock (first :: rest).length source,
        .val [targetValue], decClock (targetFirst :: targetRest).length target,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons] at timeout
        simp [timeout]
      · simp only [List.length_cons] at targetTimeout
        simp [targetTimeout]
      · simpa [resultRel, nextG, decClock] using valueRel
      · rcases states with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globs, refs, compiler, co⟩
        refine ⟨aux, free, codeS, codeT, ?_, ffi, maxApp, globs, refs, compiler, co⟩
        simp [decClock, clock, len]
      · simpa [stateGlobalsApprox, nextG, decClock] using globals
      · simpa [decClock] using oracle
      · simpa [nextG, decClock] using oracleDisjoint

end Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyPartial
