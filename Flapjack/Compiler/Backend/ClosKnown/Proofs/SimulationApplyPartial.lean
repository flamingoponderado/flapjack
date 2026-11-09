module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Simulation
public import Flapjack.Compiler.Backend.Semantics.ClosProps.ClosureLocation

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


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

/-- Related lists have related elements at the same successful index. This
is Flapjack proof infrastructure for recursive closure selection. -/
theorem relatedLookup {α β : Type} {r : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ r xs ys) : ∀ (index : Nat) (x : α), xs[index]? = some x →
      ∃ y, ys[index]? = some y ∧ r x y := by
  induction related with
  | nil => intro index x found; simp at found
  | @cons x y xs ys head tail ih =>
    intro index value found
    cases index with
    | zero =>
      simp at found
      subst value
      exact ⟨y, rfl, head⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found ⊢
      exact ih index value found

/-- Related recursive closures select related function entries and produce
related partial closures. This is Flapjack induction infrastructure. -/
theorem relatedPartialRecClosure (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (location requested : Option Nat) (supplied captured args targetArgs : List Value)
    (functions : List (Nat × ClosLang.Exp)) (index : Nat) (target partialValue : Value)
    (related : ValueRel c g (.recclosure location supplied captured functions index) target)
    (argsRelated : List.Forall₂ (ValueRel c g) args targetArgs)
    (locRelated : loptRel target args.length none requested)
    (found : destClosure maxApp none (.recclosure location supplied captured functions index) args =
      some (.partialApp partialValue)) :
    ∃ targetValue, destClosure maxApp requested target targetArgs = some (.partialApp targetValue) ∧
      ValueRel c g partialValue targetValue := by
  cases related with
  | recclosure location supplied supplied2 env1a env1b env2a env2b functions functions2 index aenv
      safe fv suppliedRelated envRelated approx functionsRelated =>
    have lengths := argsRelated.length_eq
    have suppliedLengths := suppliedRelated.length_eq
    simp only [destClosure] at found
    cases sourceEntry : functions[index]? with
    | none => simp [sourceEntry] at found
    | some entry =>
      rcases entry with ⟨arity, body⟩
      obtain ⟨targetEntry, targetEntryFound, entryRelated⟩ := relatedLookup functionsRelated index (arity, body) sourceEntry
      rcases targetEntry with ⟨targetArity, targetBody⟩
      have arityEq : arity = targetArity := entryRelated.1
      subst targetArity
      simp only [sourceEntry, checkLoc] at found
      have valid : args.length ≤ maxApp ∧ supplied.length < arity := by
        by_contra notValid
        simp [notValid] at found
      have partialCase : args.length + supplied.length < arity := by
        by_contra notPartial
        simp [valid, notPartial] at found
      simp [valid, partialCase] at found
      subst partialValue
      have targetBound : index < functions2.length :=
        (List.getElem?_eq_some_iff.mp targetEntryFound).choose
      have targetElem : functions2[index]'targetBound = (arity, targetBody) :=
        (List.getElem?_eq_some_iff.mp targetEntryFound).choose_spec
      have requestedNone : requested = none := by
        rcases locRelated with equal | ⟨_, extra⟩
        · exact equal
        · cases requested with
          | none => rfl
          | some addr =>
            cases location with
            | none => simp at extra
            | some loc =>
              let _ : Nonempty (Nat × ClosLang.Exp) := ⟨(0, .var .none 0)⟩
              dsimp only at extra
              rw [Flapjack.holEl_eq_getElem index functions2 targetBound, targetElem] at extra
              omega
      subst requested
      refine ⟨.recclosure location (targetArgs ++ supplied2) (env2a ++ env2b) functions2 index, ?_, ?_⟩
      · simp [destClosure, targetEntryFound, checkLoc, ← lengths, ← suppliedLengths, valid, partialCase]
      · exact ValueRel.recclosure location (args ++ supplied) (targetArgs ++ supplied2)
          env1a env1b env2a env2b functions functions2 index aenv safe fv
          (List.rel_append argsRelated suppliedRelated) envRelated approx functionsRelated

/-- Recursive-closure partial applications preserve the simulation invariants.
This is Flapjack induction infrastructure. -/
theorem partialRecClosureSimulation {C F : Type} (c : Config)
    (source : State (Spt ValApprox × C) F) (target : State C F)
    (loc1 loc2 closureLoc : Option Nat) (supplied captured : List Value)
    (functions : List (Nat × ClosLang.Exp)) (index : Nat) (targetFn : Value)
    (first : Value) (rest targetArgs : List Value) (argsopt : Option (List Value))
    (partialValue : Value)
    (states : StateRel c (nextG source) source target)
    (fnRelated : valueRelApp c (nextG source) (.recclosure closureLoc supplied captured functions index) targetFn argsopt)
    (argsRelated : List.Forall₂ (ValueRel c (nextG source)) (first :: rest) targetArgs)
    (locRelated : loptRel targetFn (first :: rest).length loc1 loc2)
    (constraint : argsopt.isSome → argsopt = some (first :: rest) ∧ (first :: rest) ≠ [] ∧ ∃ exp env,
      destClosure source.maxApp loc1 (.recclosure closureLoc supplied captured functions index) (first :: rest) =
        some (.fullApp exp env []))
    (found : destClosure source.maxApp loc1 (.recclosure closureLoc supplied captured functions index) (first :: rest) =
      some (.partialApp partialValue))
    (globals : stateGlobalsApprox source (nextG source))
    (oracle : isStateOracle (compileInc c) source.compileOracle)
    (oracleDisjoint : oracleGapproxDisjoint (nextG source) source.compileOracle) :
    ∃ sourceResult sourceFinal targetResult targetFinal,
      evaluateApp loc1 (.recclosure closureLoc supplied captured functions index) (first :: rest) source =
        (sourceResult, sourceFinal) ∧
      evaluateApp loc2 targetFn targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG sourceFinal))) (ValueRel c (nextG sourceFinal))
        sourceResult targetResult ∧ StateRel c (nextG sourceFinal) sourceFinal targetFinal ∧
      stateGlobalsApprox sourceFinal (nextG sourceFinal) ∧
      isStateOracle (compileInc c) sourceFinal.compileOracle ∧
      oracleGapproxDisjoint (nextG sourceFinal) sourceFinal.compileOracle := by
  obtain ⟨_, locEq, fnRel⟩ := partialApplicationInputs c (nextG source) source.maxApp loc1
    (.recclosure closureLoc supplied captured functions index) targetFn (first :: rest) argsopt partialValue
    fnRelated constraint found
  subst loc1
  have maxEq : source.maxApp = target.maxApp := states.2.2.2.2.2.2.1
  have clockEq : source.clock = target.clock := states.2.2.2.2.1
  obtain ⟨targetValue, targetFound, valueRel⟩ := relatedPartialRecClosure c (nextG source) source.maxApp
    closureLoc loc2 supplied captured (first :: rest) targetArgs functions index targetFn partialValue
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

/-- Every partial-application outcome is simulated, for ordinary and
recursive closures, with timeout and success retaining the original state
invariants. This is Flapjack induction infrastructure. -/
theorem partialApplicationSimulation {C F : Type} (c : Config)
    (source : State (Spt ValApprox × C) F) (target : State C F)
    (loc1 loc2 : Option Nat) (sourceFn targetFn : Value)
    (first : Value) (rest targetArgs : List Value) (argsopt : Option (List Value))
    (partialValue : Value)
    (states : StateRel c (nextG source) source target)
    (fnRelated : valueRelApp c (nextG source) sourceFn targetFn argsopt)
    (argsRelated : List.Forall₂ (ValueRel c (nextG source)) (first :: rest) targetArgs)
    (locRelated : loptRel targetFn (first :: rest).length loc1 loc2)
    (constraint : argsopt.isSome → argsopt = some (first :: rest) ∧ (first :: rest) ≠ [] ∧ ∃ exp env,
      destClosure source.maxApp loc1 sourceFn (first :: rest) = some (.fullApp exp env []))
    (found : destClosure source.maxApp loc1 sourceFn (first :: rest) = some (.partialApp partialValue))
    (globals : stateGlobalsApprox source (nextG source))
    (oracle : isStateOracle (compileInc c) source.compileOracle)
    (oracleDisjoint : oracleGapproxDisjoint (nextG source) source.compileOracle) :
    ∃ sourceResult sourceFinal targetResult targetFinal,
      evaluateApp loc1 sourceFn (first :: rest) source = (sourceResult, sourceFinal) ∧
      evaluateApp loc2 targetFn targetArgs target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel c (nextG sourceFinal))) (ValueRel c (nextG sourceFinal))
        sourceResult targetResult ∧ StateRel c (nextG sourceFinal) sourceFinal targetFinal ∧
      stateGlobalsApprox sourceFinal (nextG sourceFinal) ∧
      isStateOracle (compileInc c) sourceFinal.compileOracle ∧
      oracleGapproxDisjoint (nextG sourceFinal) sourceFinal.compileOracle := by
  cases sourceFn with
  | closure closureLoc supplied captured arity body =>
    exact partialClosureSimulation c source target loc1 loc2 closureLoc supplied captured arity body
      targetFn first rest targetArgs argsopt partialValue states fnRelated argsRelated locRelated
      constraint found globals oracle oracleDisjoint
  | recclosure closureLoc supplied captured functions index =>
    exact partialRecClosureSimulation c source target loc1 loc2 closureLoc supplied captured functions index
      targetFn first rest targetArgs argsopt partialValue states fnRelated argsRelated locRelated
      constraint found globals oracle oracleDisjoint
  | number _ | word64 _ | byteVector _ | refPtr _ _ | block _ _ => simp [destClosure] at found

/-- A source partial-application outcome satisfies the optimizer's complete
application simulation predicate. This is Flapjack induction infrastructure
for the partial branch of the nonempty application case. -/
theorem knownAppPartialCase {C F : Type} (loc1 : Option Nat) (sourceFn : Value)
    (first : Value) (rest : List Value) (s0 : State (Spt ValApprox × C) F) (partialValue : Value)
    (found : destClosure s0.maxApp loc1 sourceFn (first :: rest) = some (.partialApp partialValue)) :
    KnownAppSimulationAt loc1 sourceFn (first :: rest) s0 := by
  intro res1 s loc2 targetFn targetArgs t0 c argsopt h
  obtain ⟨run, fnRel, oracleDisjoint, _, _, _, _, _, _, _, oracle, argsRel, states, globals,
    _, locRel, constraint, _⟩ := h
  obtain ⟨sourceResult, sourceFinal, targetResult, targetFinal, sourceRun, targetRun,
    resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ :=
    partialApplicationSimulation c s0 t0 loc1 loc2 sourceFn targetFn first rest targetArgs
      argsopt partialValue states fnRel argsRel locRel constraint found globals oracle oracleDisjoint
  rw [run] at sourceRun
  cases sourceRun
  exact ⟨targetResult, targetFinal, targetRun, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩

/-- An annotation selected from a sound function approximation is valid for
the related runtime closure. This is Flapjack infrastructure for the
application case of the optimizer simulation. -/
theorem annotatedApplicationLocation (c : Config) (g : Spt ValApprox)
    (approx : ValApprox) (source target : Value) (loc : Option Nat) (arity address : Nat)
    (decision : decideInlineHOL c approx loc arity = .annotate address)
    (sound : ValApproxVal approx source) (related : ValueRel c g source target) :
    loptRel target arity loc (some address) := by
  cases sound with
  | other v => simp [decideInlineHOL] at decision
  | int i => simp [decideInlineHOL] at decision
  | tuple tag approxs values rel => simp [decideInlineHOL] at decision
  | closNoInline closureLoc n env body =>
    simp only [decideInlineHOL] at decision
    split at decision <;> simp_all
    cases related with
    | closure _ _ supplied2 env1a env1b env2a env2b _ _ body2 aenv
        safe fv suppliedRelated envRelated approx bodyRelated =>
      cases suppliedRelated
      simp_all [loptRel]
  | clos closureLoc n size body env =>
    simp only [decideInlineHOL] at decision
    split at decision <;> simp_all
    split at decision <;> simp_all
    cases related with
    | closure _ _ supplied2 env1a env1b env2a env2b _ _ body2 aenv
        safe fv suppliedRelated envRelated approx bodyRelated =>
      cases suppliedRelated
      simp_all [loptRel]
  | recNoInline closureLoc n base env fns index conditions =>
    simp only [decideInlineHOL] at decision
    split at decision <;> simp_all
    cases related with
    | recclosure _ _ supplied2 env1a env1b env2a env2b _ fns2 _ aenv
        safe fv suppliedRelated envRelated approx functionsRelated =>
      cases suppliedRelated
      obtain ⟨locEq, bound, arityEq⟩ := conditions
      have bound2 : index < fns2.length := by simpa [← functionsRelated.length_eq] using bound
      have entryRel := List.Forall₂.get functionsRelated bound bound2
      let _ : Nonempty (Nat × ClosLang.Exp) := ⟨(0, .var .none 0)⟩
      rw [Flapjack.holEl_eq_getElem index fns bound] at arityEq
      simp only [loptRel]
      right
      refine ⟨trivial, bound2, ?_, ?_, trivial⟩
      · omega
      · rw [Flapjack.holEl_eq_getElem index fns bound,
          Flapjack.holEl_eq_getElem index fns2 bound2]
        exact entryRel.1

end Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyPartial
