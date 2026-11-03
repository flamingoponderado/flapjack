import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationApplyPartial

/-! Full closure application in the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyFull
open ClosSem ClosProps Relations Relations.StateRelation

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

end Flapjack.Compiler.Backend.ClosKnown.Simulation.ApplyFull
