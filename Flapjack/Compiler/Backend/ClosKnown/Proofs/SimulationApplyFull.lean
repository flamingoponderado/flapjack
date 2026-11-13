module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApplyPartial
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationLetrec

@[expose] public section


/-! Full closure application in the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyFull
open ClosSem ClosProps Relations Relations.StateRelation BackendProps OracleGlobals
open Flapjack.SemanticPrimitivesProps

/-- A valid closure location check remains valid when the optimizer adds its
permitted direct-call annotation. This is Flapjack proof infrastructure. -/
theorem closureCheckLocRelated (maxApp arity : Nat) (location sourceLoc targetLoc : Option Nat)
    (sourceArgs targetArgs sourceSupplied targetSupplied targetEnv : List Value) (targetBody : ClosLang.Exp)
    (argsLen : sourceArgs.length = targetArgs.length)
    (suppliedLen : sourceSupplied.length = targetSupplied.length)
    (locRel : loptRel (.closure location targetSupplied targetEnv arity targetBody) sourceArgs.length
      sourceLoc targetLoc)
    (valid : checkLoc maxApp sourceLoc location arity sourceArgs.length sourceSupplied.length = true) :
    checkLoc maxApp targetLoc location arity targetArgs.length targetSupplied.length = true := by
  cases sourceLoc <;> cases targetLoc <;> cases location <;> simp_all [loptRel, checkLoc]

/-- Every value is described by an unconstrained approximation. This is
Flapjack proof infrastructure. -/
theorem otherApproximates (values : List Value) :
    List.Forall₂ ValApproxVal (List.replicate values.length .other) values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (.other value) ih

/-- Full application of related ordinary closures selects related bodies,
related captured-prefix environments, and related remaining arguments. This
is Flapjack induction infrastructure for the full-application branch. -/
theorem relatedFullClosure (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (location sourceLoc targetLoc : Option Nat) (supplied captured args targetArgs : List Value)
    (arity : Nat) (body sourceBody : ClosLang.Exp) (sourceEnv sourceRest : List Value) (target : Value)
    (related : ValueRel c g (.closure location supplied captured arity body) target)
    (argsRelated : List.Forall₂ (ValueRel c g) args targetArgs)
    (locRelated : loptRel target args.length sourceLoc targetLoc)
    (found : destClosure maxApp sourceLoc (.closure location supplied captured arity body) args =
      some (.fullApp sourceBody sourceEnv sourceRest)) :
    ∃ targetBody sourcePrefix sourceExtra targetPrefix targetExtra targetRest approxEnv,
      sourceEnv = sourcePrefix ++ sourceExtra ∧
      destClosure maxApp targetLoc target targetArgs =
        some (.fullApp targetBody (targetPrefix ++ targetExtra) targetRest) ∧
      List.Forall₂ (ValueRel c g) sourcePrefix targetPrefix ∧
      List.Forall₂ (ValueRel c g) sourceRest targetRest ∧
      List.Forall₂ ValApproxVal approxEnv sourcePrefix ∧
      expRel c approxEnv g sourceBody targetBody ∧
      fvMax sourcePrefix.length [sourceBody] ∧ everyFnVarsNone [sourceBody] := by
  cases related with
  | closure location supplied supplied2 env1a env1b env2a env2b arity body body2 aenv
      safe fv suppliedRelated envRelated approx bodyRelated =>
    have argsLen := argsRelated.length_eq
    have suppliedLen := suppliedRelated.length_eq
    simp only [destClosure] at found
    by_cases valid : checkLoc maxApp sourceLoc location arity args.length supplied.length = true ∧
        supplied.length < arity
    · by_cases partialCase : args.length + supplied.length < arity
      · simp [valid, partialCase] at found
      · simp [valid, partialCase] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        have targetCheck := closureCheckLocRelated maxApp arity location sourceLoc targetLoc
          args targetArgs supplied supplied2 (env2a ++ env2b) body2 argsLen suppliedLen locRelated valid.1
        let sourceTaken := (args.reverse.take (arity - supplied.length)).reverse ++ supplied
        let targetTaken := (targetArgs.reverse.take (arity - supplied.length)).reverse ++ supplied2
        have takenRel : List.Forall₂ (ValueRel c g) sourceTaken targetTaken := by
          exact List.rel_append
            (List.rel_reverse (List.forall₂_take _ (List.rel_reverse argsRelated))) suppliedRelated
        have takenLength : sourceTaken.length = arity := by
          simp [sourceTaken, List.length_take]
          omega
        refine ⟨body2, sourceTaken ++ env1a, env1b, targetTaken ++ env2a, env2b,
          (targetArgs.reverse.drop (arity - supplied.length)).reverse,
          List.replicate arity .other ++ aenv, ?_, ?_, ?_, ?_, ?_, bodyRelated, ?_, safe⟩
        · simp [sourceTaken, List.append_assoc]
        · have targetCheck' : checkLoc maxApp targetLoc location arity args.length supplied.length = true := by
            simpa [← argsLen, ← suppliedLen] using targetCheck
          simp [destClosure, targetCheck', ← suppliedLen, ← argsLen, valid.2, partialCase,
            targetTaken, List.append_assoc]
        · exact List.rel_append takenRel envRelated
        · exact List.rel_reverse (List.forall₂_drop _ (List.rel_reverse argsRelated))
        · apply List.rel_append ?_ approx
          simpa [takenLength] using otherApproximates sourceTaken
        · simpa [List.length_append, takenLength] using fv
    · simp [valid] at found

/-- Exact full application retains the argument approximations supplied by
the inliner and relates the selected body environments. This is Flapjack
induction infrastructure for the special application relation. -/
theorem relatedFullClosureExact (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (location sourceLoc targetLoc : Option Nat) (supplied captured args targetArgs : List Value)
    (arity : Nat) (body sourceBody : ClosLang.Exp) (sourceEnv : List Value) (target : Value)
    (related : valueRelApp c g (.closure location supplied captured arity body) target (some args))
    (argsRelated : List.Forall₂ (ValueRel c g) args targetArgs)
    (locRelated : loptRel target args.length sourceLoc targetLoc)
    (found : destClosure maxApp sourceLoc (.closure location supplied captured arity body) args =
      some (.fullApp sourceBody sourceEnv [])) :
    ∃ targetBody sourcePrefix sourceExtra targetPrefix targetExtra approxEnv,
      sourceEnv = sourcePrefix ++ sourceExtra ∧
      destClosure maxApp targetLoc target targetArgs =
        some (.fullApp targetBody (targetPrefix ++ targetExtra) []) ∧
      List.Forall₂ (ValueRel c g) sourcePrefix targetPrefix ∧
      List.Forall₂ ValApproxVal approxEnv sourcePrefix ∧
      expRel c approxEnv g sourceBody targetBody ∧
      fvMax sourcePrefix.length [sourceBody] ∧ everyFnVarsNone [sourceBody] := by
  simp only [valueRelApp] at related
  obtain ⟨safe, aenv, env1a, env1b, supplied2, env2a, env2b, body2, aargs,
    capturedEq, fv, suppliedRelated, envRelated, approx, ⟨argsApprox, suppliedEq⟩, bodyRelated, targetEq⟩ := related
  subst captured
  subst supplied
  subst target
  cases suppliedRelated
  have argsLen := argsRelated.length_eq
  simp only [destClosure] at found
  by_cases valid : checkLoc maxApp sourceLoc location arity args.length 0 = true ∧ 0 < arity
  · by_cases partialCase : args.length < arity
    · simp [valid, partialCase] at found
    · simp [valid, partialCase] at found
      obtain ⟨rfl, sourceEnvEq, emptyRest⟩ := found
      have enough : arity ≤ args.length := Nat.le_of_not_gt partialCase
      have atMost : args.length ≤ arity := emptyRest
      have exactLength : args.length = arity := Nat.le_antisymm atMost enough
      have targetCheck := closureCheckLocRelated maxApp arity location sourceLoc targetLoc args targetArgs
        [] [] (env2a ++ env2b) body2 argsLen rfl locRelated valid.1
      have taken : args.reverse.take arity = args.reverse := by simpa [← exactLength] using (List.take_length (l := args.reverse))
      have targetTaken : targetArgs.reverse.take arity = targetArgs.reverse := by
        simpa [← exactLength, argsLen] using (List.take_length (l := targetArgs.reverse))
      have targetDrop : targetArgs.reverse.drop arity = [] := by simp [← exactLength, argsLen]
      refine ⟨body2, args ++ env1a, env1b, targetArgs ++ env2a, env2b, aargs ++ aenv,
        ?_, ?_, List.rel_append argsRelated envRelated, List.rel_append argsApprox approx, bodyRelated, ?_, safe⟩
      · simpa [taken, List.append_assoc] using sourceEnvEq.symm
      · have targetCheck' : checkLoc maxApp targetLoc location arity arity 0 = true := by
          simpa [← argsLen, exactLength] using targetCheck
        simp [destClosure, targetCheck', ← argsLen, exactLength, valid.2, targetTaken, targetDrop, List.append_assoc]
      · simpa [List.length_append, exactLength] using fv
  · simp [valid] at found

/-- Full ordinary closure application handles both the general value relation
and the inliner's exact-argument relation, producing the complete inputs for
the body induction hypothesis. This is Flapjack induction infrastructure. -/
theorem relatedFullClosureWithApproxs (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (location sourceLoc targetLoc : Option Nat) (supplied captured args targetArgs : List Value)
    (arity : Nat) (body sourceBody : ClosLang.Exp) (sourceEnv sourceRest : List Value)
    (target : Value) (argsopt : Option (List Value))
    (related : valueRelApp c g (.closure location supplied captured arity body) target argsopt)
    (argsRelated : List.Forall₂ (ValueRel c g) args targetArgs)
    (locRelated : loptRel target args.length sourceLoc targetLoc)
    (constraint : argsopt.isSome → argsopt = some args ∧ args ≠ [] ∧ ∃ exp env,
      destClosure maxApp sourceLoc (.closure location supplied captured arity body) args =
        some (.fullApp exp env []))
    (found : destClosure maxApp sourceLoc (.closure location supplied captured arity body) args =
      some (.fullApp sourceBody sourceEnv sourceRest)) :
    ∃ targetBody sourcePrefix sourceExtra targetPrefix targetExtra targetRest approxEnv,
      sourceEnv = sourcePrefix ++ sourceExtra ∧
      destClosure maxApp targetLoc target targetArgs =
        some (.fullApp targetBody (targetPrefix ++ targetExtra) targetRest) ∧
      List.Forall₂ (ValueRel c g) sourcePrefix targetPrefix ∧
      List.Forall₂ (ValueRel c g) sourceRest targetRest ∧
      List.Forall₂ ValApproxVal approxEnv sourcePrefix ∧
      expRel c approxEnv g sourceBody targetBody ∧
      fvMax sourcePrefix.length [sourceBody] ∧ everyFnVarsNone [sourceBody] := by
  cases argsopt with
  | none =>
    exact relatedFullClosure c g maxApp location sourceLoc targetLoc supplied captured args targetArgs
      arity body sourceBody sourceEnv sourceRest target (by simpa [valueRelAppNone] using related)
      argsRelated locRelated found
  | some values =>
    obtain ⟨same, _, otherBody, otherEnv, exactRun⟩ := constraint (by simp)
    have sameValues : values = args := Option.some.inj same
    subst values
    rw [found] at exactRun
    simp only [Option.some.injEq, AppKind.fullApp.injEq] at exactRun
    obtain ⟨_, _, restEmpty⟩ := exactRun
    subst sourceRest
    obtain ⟨targetBody, sourcePrefix, sourceExtra, targetPrefix, targetExtra, approxEnv,
      sourceEq, targetRun, prefixes, approximations, bodyRel, fv, safe⟩ :=
      relatedFullClosureExact c g maxApp location sourceLoc targetLoc supplied captured args targetArgs
        arity body sourceBody sourceEnv target related argsRelated locRelated found
    exact ⟨targetBody, sourcePrefix, sourceExtra, targetPrefix, targetExtra, [], approxEnv,
      sourceEq, targetRun, prefixes, .nil, approximations, bodyRel, fv, safe⟩

/-- If a full ordinary closure call gains a direct annotation, it consumes
all arguments; no over-application tail remains. This is Flapjack induction
infrastructure. -/
theorem annotatedFullClosureNoRest (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (location sourceLoc targetLoc : Option Nat) (supplied captured args : List Value)
    (arity : Nat) (body sourceBody : ClosLang.Exp) (sourceEnv sourceRest : List Value) (target : Value)
    (related : ValueRel c g (.closure location supplied captured arity body) target)
    (locRelated : loptRel target args.length sourceLoc targetLoc)
    (found : destClosure maxApp sourceLoc (.closure location supplied captured arity body) args =
      some (.fullApp sourceBody sourceEnv sourceRest))
    (different : sourceLoc ≠ targetLoc) : sourceRest = [] := by
  cases related with
  | closure location supplied supplied2 env1a env1b env2a env2b arity body body2 aenv
      safe fv suppliedRelated envRelated approx bodyRelated =>
    rcases locRelated with same | ⟨sourceNone, direct⟩
    · exact (different same.symm).elim
    · subst sourceLoc
      cases targetLoc with
      | none => exact (different rfl).elim
      | some address =>
        cases location with
        | none => simp at direct
        | some closureAddress =>
          dsimp only at direct
          obtain ⟨_, arityEq, suppliedEmpty⟩ := direct
          have suppliedLength : supplied.length = supplied2.length := suppliedRelated.length_eq
          have suppliedZero : supplied.length = 0 := by simp [suppliedEmpty] at suppliedLength ⊢; omega
          simp only [destClosure, checkLoc] at found
          by_cases bound : args.length ≤ maxApp
          · simp [bound, suppliedZero, arityEq] at found
            have dropEmpty : args.reverse.drop args.length = [] := by simp
            simpa [dropEmpty] using found.2.2.2.symm
          · simp [bound] at found

/-- A valid recursive-closure location check remains valid when the
optimizer adds its permitted direct annotation. This is Flapjack proof
infrastructure. -/
theorem recClosureCheckLocRelated (maxApp arity index : Nat) (location sourceLoc targetLoc : Option Nat)
    (sourceArgs targetArgs sourceSupplied targetSupplied targetEnv : List Value)
    (targetFunctions : List (Nat × ClosLang.Exp)) (targetBody : ClosLang.Exp)
    (argsLen : sourceArgs.length = targetArgs.length)
    (suppliedLen : sourceSupplied.length = targetSupplied.length)
    (entry : targetFunctions[index]? = some (arity, targetBody))
    (locRel : loptRel (.recclosure location targetSupplied targetEnv targetFunctions index) sourceArgs.length
      sourceLoc targetLoc)
    (valid : checkLoc maxApp sourceLoc (location.map (fun loc => 2 * index + loc))
      arity sourceArgs.length sourceSupplied.length = true) :
    checkLoc maxApp targetLoc (location.map (fun loc => 2 * index + loc))
      arity targetArgs.length targetSupplied.length = true := by
  have bound : index < targetFunctions.length := (List.getElem?_eq_some_iff.mp entry).choose
  have elem : targetFunctions[index]'bound = (arity, targetBody) :=
    (List.getElem?_eq_some_iff.mp entry).choose_spec
  let _ : Nonempty (Nat × ClosLang.Exp) := ⟨(0, .var .none 0)⟩
  have element : @Flapjack.holEl (Nat × ClosLang.Exp) ⟨(0, .var .none 0)⟩ index targetFunctions = (arity, targetBody) := by
    rw [Flapjack.holEl_eq_getElem index targetFunctions bound, elem]
  cases sourceLoc <;> cases targetLoc <;> cases location <;>
    simp_all [loptRel, checkLoc, Nat.add_comm]

/-- Full recursive-closure application selects related function bodies,
recursive-closure environments, and over-application tails. This is
Flapjack induction infrastructure. -/
theorem relatedFullRecClosure (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (location sourceLoc targetLoc : Option Nat) (supplied captured args targetArgs : List Value)
    (functions : List (Nat × ClosLang.Exp)) (index : Nat)
    (sourceBody : ClosLang.Exp) (sourceEnv sourceRest : List Value) (target : Value)
    (related : ValueRel c g (.recclosure location supplied captured functions index) target)
    (argsRelated : List.Forall₂ (ValueRel c g) args targetArgs)
    (locRelated : loptRel target args.length sourceLoc targetLoc)
    (found : destClosure maxApp sourceLoc (.recclosure location supplied captured functions index) args =
      some (.fullApp sourceBody sourceEnv sourceRest)) :
    ∃ targetBody sourcePrefix sourceExtra targetPrefix targetExtra targetRest approxEnv,
      sourceEnv = sourcePrefix ++ sourceExtra ∧
      destClosure maxApp targetLoc target targetArgs =
        some (.fullApp targetBody (targetPrefix ++ targetExtra) targetRest) ∧
      List.Forall₂ (ValueRel c g) sourcePrefix targetPrefix ∧
      List.Forall₂ (ValueRel c g) sourceRest targetRest ∧
      List.Forall₂ ValApproxVal approxEnv sourcePrefix ∧
      expRel c approxEnv g sourceBody targetBody ∧
      fvMax sourcePrefix.length [sourceBody] ∧ everyFnVarsNone [sourceBody] := by
  cases related with
  | recclosure location supplied supplied2 env1a env1b env2a env2b functions functions2 index aenv
      safe fv suppliedRelated envRelated approx functionsRelated =>
    have argsLen := argsRelated.length_eq
    have suppliedLen := suppliedRelated.length_eq
    have functionsLen := functionsRelated.length_eq
    simp only [destClosure] at found
    cases sourceEntry : functions[index]? with
    | none => simp [sourceEntry] at found
    | some entry =>
      rcases entry with ⟨arity, body⟩
      obtain ⟨targetEntry, targetEntryFound, entryRelated⟩ :=
        ApplyPartial.relatedLookup functionsRelated index (arity, body) sourceEntry
      rcases targetEntry with ⟨targetArity, body2⟩
      have arityEq : arity = targetArity := entryRelated.1
      subst targetArity
      simp only [sourceEntry] at found
      by_cases valid : checkLoc maxApp sourceLoc (location.map (fun loc => 2 * index + loc))
          arity args.length supplied.length = true ∧ supplied.length < arity
      · by_cases partialCase : args.length + supplied.length < arity
        · simp [valid, partialCase] at found
        · simp [valid, partialCase] at found
          obtain ⟨rfl, rfl, rfl⟩ := found
          have targetCheck := recClosureCheckLocRelated maxApp arity index location sourceLoc targetLoc
            args targetArgs supplied supplied2 (env2a ++ env2b) functions2 body2 argsLen suppliedLen
            targetEntryFound locRelated valid.1
          let sourceTaken := (args.reverse.take (arity - supplied.length)).reverse ++ supplied
          let targetTaken := (targetArgs.reverse.take (arity - supplied.length)).reverse ++ supplied2
          let sourceRec := (List.range functions.length).map
            (fun i => Value.recclosure location [] (env1a ++ env1b) functions i)
          let targetRec := (List.range functions.length).map
            (fun i => Value.recclosure location [] (env2a ++ env2b) functions2 i)
          let clos := match location with
            | none => List.replicate functions.length ValApprox.other
            | some n => closGenNoInline n 0 functions
          have takenRel : List.Forall₂ (ValueRel c g) sourceTaken targetTaken := by
            exact List.rel_append
              (List.rel_reverse (List.forall₂_take _ (List.rel_reverse argsRelated))) suppliedRelated
          have takenLength : sourceTaken.length = arity := by
            simp [sourceTaken, List.length_take]
            omega
          have recRelated : List.Forall₂ (ValueRel c g) sourceRec targetRec := by
            exact Letrec.recursiveClosuresRelated c g location functions functions2 env1a env1b env2a env2b
              aenv safe fv envRelated approx functionsRelated (List.range functions.length)
          have recApprox : List.Forall₂ ValApproxVal clos sourceRec := by
            exact CorrectApprox.Letrec.recClosuresApprox location (env1a ++ env1b) functions
          have member : (arity, body) ∈ functions := List.mem_of_getElem? sourceEntry
          have bodySafe : everyFnVarsNone [body] := safe (arity, body) member
          have bodyFv : fvMax (arity + functions.length + env1a.length) [body] := fv (arity, body) member
          have bodyRel' : expRel c (List.replicate arity .other ++ (clos ++ aenv)) g body body2 := entryRelated.2
          have bodyRel : expRel c (List.replicate arity .other ++ clos ++ aenv) g body body2 := by
            simpa only [List.append_assoc] using bodyRel'
          refine ⟨body2, sourceTaken ++ sourceRec ++ env1a, env1b,
            targetTaken ++ targetRec ++ env2a, env2b,
            (targetArgs.reverse.drop (arity - supplied.length)).reverse,
            List.replicate arity .other ++ clos ++ aenv, ?_, ?_, ?_, ?_, ?_, bodyRel, ?_, bodySafe⟩
          · simp [sourceTaken, sourceRec, List.append_assoc]
          · have targetCheck' : checkLoc maxApp targetLoc (location.map (fun loc => 2 * index + loc))
                arity args.length supplied.length = true := by
              simpa [← argsLen, ← suppliedLen] using targetCheck
            simp [destClosure, targetEntryFound, targetCheck', ← suppliedLen, ← argsLen, valid.2,
              partialCase, targetTaken, targetRec, ← functionsLen, List.append_assoc]
          · exact List.rel_append (List.rel_append takenRel recRelated) envRelated
          · exact List.rel_reverse (List.forall₂_drop _ (List.rel_reverse argsRelated))
          · exact List.rel_append (List.rel_append (by simpa [takenLength] using otherApproximates sourceTaken) recApprox) approx
          · simpa [List.length_append, takenLength, sourceRec, Nat.add_assoc] using bodyFv
      · simp [valid] at found

/-- The application relation for a recursive closure uses the ordinary value
relation regardless of the optional inliner arguments. This is Flapjack
induction infrastructure. -/
theorem relatedFullRecClosureWithApproxs (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (location sourceLoc targetLoc : Option Nat) (supplied captured args targetArgs : List Value)
    (functions : List (Nat × ClosLang.Exp)) (index : Nat)
    (sourceBody : ClosLang.Exp) (sourceEnv sourceRest : List Value) (target : Value)
    (argsopt : Option (List Value))
    (related : valueRelApp c g (.recclosure location supplied captured functions index) target argsopt)
    (argsRelated : List.Forall₂ (ValueRel c g) args targetArgs)
    (locRelated : loptRel target args.length sourceLoc targetLoc)
    (found : destClosure maxApp sourceLoc (.recclosure location supplied captured functions index) args =
      some (.fullApp sourceBody sourceEnv sourceRest)) :
    ∃ targetBody sourcePrefix sourceExtra targetPrefix targetExtra targetRest approxEnv,
      sourceEnv = sourcePrefix ++ sourceExtra ∧
      destClosure maxApp targetLoc target targetArgs =
        some (.fullApp targetBody (targetPrefix ++ targetExtra) targetRest) ∧
      List.Forall₂ (ValueRel c g) sourcePrefix targetPrefix ∧
      List.Forall₂ (ValueRel c g) sourceRest targetRest ∧
      List.Forall₂ ValApproxVal approxEnv sourcePrefix ∧
      expRel c approxEnv g sourceBody targetBody ∧
      fvMax sourcePrefix.length [sourceBody] ∧ everyFnVarsNone [sourceBody] :=
  relatedFullRecClosure c g maxApp location sourceLoc targetLoc supplied captured args targetArgs
    functions index sourceBody sourceEnv sourceRest target related argsRelated locRelated found

/-- Adding a direct annotation to a recursive closure call consumes all
arguments, so a changed annotation cannot affect a later over-application.
This is Flapjack induction infrastructure. -/
theorem annotatedFullRecClosureNoRest (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (location sourceLoc targetLoc : Option Nat) (supplied captured args : List Value)
    (functions : List (Nat × ClosLang.Exp)) (index : Nat)
    (sourceBody : ClosLang.Exp) (sourceEnv sourceRest : List Value) (target : Value)
    (related : ValueRel c g (.recclosure location supplied captured functions index) target)
    (locRelated : loptRel target args.length sourceLoc targetLoc)
    (found : destClosure maxApp sourceLoc (.recclosure location supplied captured functions index) args =
      some (.fullApp sourceBody sourceEnv sourceRest))
    (different : sourceLoc ≠ targetLoc) : sourceRest = [] := by
  cases related with
  | recclosure location supplied supplied2 env1a env1b env2a env2b functions functions2 index aenv
      safe fv suppliedRelated envRelated approx functionsRelated =>
    rcases locRelated with same | ⟨sourceNone, direct⟩
    · exact (different same.symm).elim
    · subst sourceLoc
      cases targetLoc with
      | none => exact (different rfl).elim
      | some address =>
        cases location with
        | none => simp at direct
        | some closureAddress =>
          dsimp only at direct
          obtain ⟨targetBound, _, targetArity, suppliedEmpty⟩ := direct
          let _ : Nonempty (Nat × ClosLang.Exp) := ⟨(0, .var .none 0)⟩
          rw [Flapjack.holEl_eq_getElem index functions2 targetBound] at targetArity
          have suppliedLength : supplied.length = supplied2.length := suppliedRelated.length_eq
          have suppliedZero : supplied.length = 0 := by simp [suppliedEmpty] at suppliedLength ⊢; omega
          simp only [destClosure] at found
          cases sourceEntry : functions[index]? with
          | none => simp [sourceEntry] at found
          | some entry =>
            rcases entry with ⟨arity, body⟩
            obtain ⟨targetEntry, targetEntryFound, entryRelated⟩ :=
              ApplyPartial.relatedLookup functionsRelated index (arity, body) sourceEntry
            have targetElem : functions2[index]? = some (functions2[index]'targetBound) :=
              List.getElem?_eq_getElem targetBound
            rw [targetEntryFound] at targetElem
            have elemEq := Option.some.inj targetElem
            have arityEq : arity = args.length := by
              have h := entryRelated.1
              rw [← elemEq] at targetArity
              exact h.trans targetArity.symm
            simp only [sourceEntry, checkLoc] at found
            by_cases bound : args.length ≤ maxApp
            · simp [bound, suppliedZero, arityEq] at found
              have dropEmpty : args.reverse.drop args.length = [] := by simp
              simpa [dropEmpty] using found.2.2.2.symm
            · simp [bound] at found

/-- A changed direct-call annotation implies that a full application has no
remaining source arguments. This is Flapjack induction infrastructure. -/
theorem annotatedFullApplicationNoRest (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (sourceLoc targetLoc : Option Nat) (source target : Value) (args : List Value)
    (argsopt : Option (List Value)) (body : ClosLang.Exp) (env rest : List Value)
    (related : valueRelApp c g source target argsopt)
    (locRelated : loptRel target args.length sourceLoc targetLoc)
    (constraint : argsopt.isSome → argsopt = some args ∧ args ≠ [] ∧ ∃ exp captures,
      destClosure maxApp sourceLoc source args = some (.fullApp exp captures []))
    (found : destClosure maxApp sourceLoc source args = some (.fullApp body env rest))
    (different : sourceLoc ≠ targetLoc) : rest = [] := by
  cases argsopt with
  | some values =>
    obtain ⟨_, _, otherBody, otherEnv, exactRun⟩ := constraint (by simp)
    rw [found] at exactRun
    simp only [Option.some.injEq, AppKind.fullApp.injEq] at exactRun
    exact exactRun.2.2
  | none =>
    have valRel : ValueRel c g source target := by simpa [valueRelAppNone] using related
    cases source with
    | closure location supplied captured arity sourceBody =>
      exact annotatedFullClosureNoRest c g maxApp location sourceLoc targetLoc supplied captured args
        arity sourceBody body env rest target valRel locRelated found different
    | recclosure location supplied captured functions index =>
      exact annotatedFullRecClosureNoRest c g maxApp location sourceLoc targetLoc supplied captured args
        functions index body env rest target valRel locRelated found different
    | number _ | word64 _ | byteVector _ | refPtr _ _ | block _ _ => simp [destClosure] at found

/-- A full application of either closure constructor selects body and
environment inputs for the original induction hypothesis, with related
remaining arguments and the direct-annotation restriction. This is Flapjack
induction infrastructure. -/
theorem relatedFullApplication (c : Config) (g : Spt ValApprox) (maxApp : Nat)
    (sourceLoc targetLoc : Option Nat) (source target : Value) (args targetArgs : List Value)
    (argsopt : Option (List Value)) (body : ClosLang.Exp) (env rest : List Value)
    (related : valueRelApp c g source target argsopt)
    (argsRelated : List.Forall₂ (ValueRel c g) args targetArgs)
    (locRelated : loptRel target args.length sourceLoc targetLoc)
    (constraint : argsopt.isSome → argsopt = some args ∧ args ≠ [] ∧ ∃ exp captures,
      destClosure maxApp sourceLoc source args = some (.fullApp exp captures []))
    (found : destClosure maxApp sourceLoc source args = some (.fullApp body env rest)) :
    ∃ targetBody sourcePrefix sourceExtra targetPrefix targetExtra targetRest approxEnv,
      env = sourcePrefix ++ sourceExtra ∧
      destClosure maxApp targetLoc target targetArgs =
        some (.fullApp targetBody (targetPrefix ++ targetExtra) targetRest) ∧
      List.Forall₂ (ValueRel c g) sourcePrefix targetPrefix ∧
      List.Forall₂ (ValueRel c g) rest targetRest ∧
      List.Forall₂ ValApproxVal approxEnv sourcePrefix ∧
      expRel c approxEnv g body targetBody ∧
      fvMax sourcePrefix.length [body] ∧ everyFnVarsNone [body] ∧
      (sourceLoc ≠ targetLoc → rest = [] ∧ targetRest = []) := by
  have restIfChanged := annotatedFullApplicationNoRest c g maxApp sourceLoc targetLoc source target args
    argsopt body env rest related locRelated constraint found
  have structural : ∃ targetBody sourcePrefix sourceExtra targetPrefix targetExtra targetRest approxEnv,
      env = sourcePrefix ++ sourceExtra ∧
      destClosure maxApp targetLoc target targetArgs =
        some (.fullApp targetBody (targetPrefix ++ targetExtra) targetRest) ∧
      List.Forall₂ (ValueRel c g) sourcePrefix targetPrefix ∧
      List.Forall₂ (ValueRel c g) rest targetRest ∧
      List.Forall₂ ValApproxVal approxEnv sourcePrefix ∧
      expRel c approxEnv g body targetBody ∧
      fvMax sourcePrefix.length [body] ∧ everyFnVarsNone [body] := by
    cases source with
    | closure location supplied captured arity sourceBody =>
      exact relatedFullClosureWithApproxs c g maxApp location sourceLoc targetLoc supplied captured args targetArgs
        arity sourceBody body env rest target argsopt related argsRelated locRelated constraint found
    | recclosure location supplied captured functions index =>
      exact relatedFullRecClosureWithApproxs c g maxApp location sourceLoc targetLoc supplied captured args targetArgs
        functions index body env rest target argsopt related argsRelated locRelated found
    | number _ | word64 _ | byteVector _ | refPtr _ _ | block _ _ => simp [destClosure] at found
  obtain ⟨targetBody, sourcePrefix, sourceExtra, targetPrefix, targetExtra, targetRest, approxEnv,
    sourceEq, targetRun, prefixes, restRel, approximations, bodyRel, fv, safe⟩ := structural
  refine ⟨targetBody, sourcePrefix, sourceExtra, targetPrefix, targetExtra, targetRest, approxEnv,
    sourceEq, targetRun, prefixes, restRel, approximations, bodyRel, fv, safe, ?_⟩
  intro different
  have empty := restIfChanged different
  subst rest
  cases restRel
  exact ⟨rfl, rfl⟩


end Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyFull
