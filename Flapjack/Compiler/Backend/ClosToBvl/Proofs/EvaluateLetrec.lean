import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateClosure

/-! Recursive-binding cases of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- An empty recursive group reduces to its body after the source capture
check. This candidate remains untagged pending evaluator and carrier review. -/
theorem expressionSimulation_letrec_nil {C F : Type}
    (names : List Basis.Pure.MlString.MlString) (location : Option Nat) (selected : Option (List Nat))
    (body : ClosLang.Exp) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    expressionSimulation (C := C) (F := F) [.letrec names location selected [] body] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases location with
  | none => simp [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] at locations
  | some label =>
    cases selected with
    | none => simp [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] at varsAnnotated
    | some indices =>
      have bodyLoc : ClosProps.everyFnLocationSome [body] := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp, ClosProps.fnLocationSomeFuns] using locations
      have bodyVars : ClosProps.everyFnVarsSome [body] := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp, ClosProps.fnVarsSomeFuns] using varsAnnotated
      cases capture : ClosSem.lookupVars indices sourceEnv with
      | none =>
        simp [ClosSem.evaluate, capture] at run
        exact False.elim (noTypeError run.1.symm)
      | some values =>
        have bodyRun : ClosSem.evaluate [body] sourceEnv s = (result, sFinal) := by
          simpa [ClosSem.evaluate, capture] using run
        have bodyCompiled : compileExpsHOL s.maxApp [body] aux = (compiled, finalAux) := by
          simpa [compileExps_eq_list, compileExpListHOL, compileExpHOL] using compile
        exact bodyIH s sFinal t sourceEnv targetEnv f aux finalAux compiled result bodyRun noTypeError
          bodyCompiled bodyLoc annotations bodyVars installed envRelated states

/-- A singleton recursive group produces a closure with its own code pointer
in the environment. The function body is installed before the enclosing body
is evaluated. This candidate remains untagged pending carrier review. -/
theorem expressionSimulation_letrec_singleton {C F : Type}
    (names : List Basis.Pure.MlString.MlString) (location : Option Nat) (selected : Option (List Nat))
    (arity : Nat) (functionBody body : ClosLang.Exp)
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    expressionSimulation (C := C) (F := F) [.letrec names location selected [(arity, functionBody)] body] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases location with
  | none => simp [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] at locations
  | some label =>
    cases selected with
    | none => simp [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] at varsAnnotated
    | some indices =>
      have locationParts : ClosProps.fnLocationSomeExp functionBody ∧ ClosProps.fnLocationSomeExp body := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp, ClosProps.fnLocationSomeFuns] using locations
      have variableParts : ClosProps.fnVarsSomeExp functionBody ∧ ClosProps.fnVarsSomeExp body := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp, ClosProps.fnVarsSomeFuns] using varsAnnotated
      have functionLoc : ClosProps.everyFnLocationSome [functionBody] := by simpa [ClosProps.everyFnLocationSome] using locationParts.1
      have bodyLoc : ClosProps.everyFnLocationSome [body] := by simpa [ClosProps.everyFnLocationSome] using locationParts.2
      have functionVars : ClosProps.everyFnVarsSome [functionBody] := by simpa [ClosProps.everyFnVarsSome] using variableParts.1
      have bodyVars : ClosProps.everyFnVarsSome [body] := by simpa [ClosProps.everyFnVarsSome] using variableParts.2
      by_cases valid : arity ≤ s.maxApp ∧ arity ≠ 0
      · cases capture : ClosSem.lookupVars indices sourceEnv with
        | none =>
          simp [ClosSem.evaluate, valid, capture] at run
          exact False.elim (noTypeError run.1.symm)
        | some sourceValues =>
          have bodyRun : ClosSem.evaluate [body]
              (.recclosure (some label) [] sourceValues [(arity, functionBody)] 0 :: sourceEnv) s = (result, sFinal) := by
            simpa [ClosSem.evaluate, valid, capture] using run
          cases functionCompile : compileExpHOL s.maxApp functionBody aux with
          | mk targetFunction auxFunction =>
            let entry := (label + numStubs s.maxApp, arity + 1,
              Bvl.Exp.let ((List.range arity).map Bvl.Exp.var ++ [.var arity] ++
                freeLet (.var arity) indices.length) targetFunction)
            cases bodyCompile : compileExpHOL s.maxApp body (entry :: auxFunction) with
            | mk targetBody auxLast =>
              have functionCompiled : compileExpsHOL s.maxApp [functionBody] aux = ([targetFunction], auxFunction) := by
                rw [compileExps_eq_list]
                simp [compileExpListHOL, functionCompile]
              have bodyCompiled : compileExpsHOL s.maxApp [body] (entry :: auxFunction) = ([targetBody], auxLast) := by
                rw [compileExps_eq_list]
                simp [compileExpListHOL, bodyCompile]
              let closureExp := Bvl.Exp.op (.blockOp (.cons 30))
                ((mkLabel (label + numStubs s.maxApp) :: mkConst (arity - 1) :: indices.map Bvl.Exp.var).reverse)
              have wholeCompiled : compileExpsHOL s.maxApp
                  [.letrec names (some label) (some indices) [(arity, functionBody)] body] aux =
                  ([.let [closureExp] targetBody], auxLast) := by
                rw [compileExps_eq_list]
                have bodyCompile' := bodyCompile
                simp only [entry, List.append_assoc, List.singleton_append] at bodyCompile'
                simp [compileExpListHOL, compileExpHOL, functionCompile, bodyCompile', closureExp]
              have equal := compile.symm.trans wholeCompiled
              cases equal
              have earlierInstalled : codeInstalled (entry :: auxFunction) t.code :=
                compileExps_codeInstalled s.maxApp [body] (entry :: auxFunction) finalAux [targetBody] t.code bodyCompiled installed
              have entryLookup := earlierInstalled entry (by simp)
              have functionInstalled : codeInstalled auxFunction t.code := by
                intro next member
                exact earlierInstalled next (by simp [member])
              obtain ⟨targetValues, targetCapture, valuesRel, lengthEq⟩ :=
                lookupVars_related indices sourceEnv targetEnv sourceValues envRelated capture
              have targetLookup : sptLookup (label + numStubs s.maxApp) t.code =
                  some (arity + 1, .let ((List.range (arity + 1)).map Bvl.Exp.var ++
                    freeLet (.var arity) sourceValues.length) targetFunction) := by
                simpa [entry, lengthEq, List.range_succ, List.map_append, List.append_assoc] using entryLookup
              let sourceClosure := ClosSem.Value.recclosure (some label) [] sourceValues [(arity, functionBody)] 0
              let targetClosure := BvlSem.Value.block 30
                (.codePtr (label + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: targetValues)
              have closureRel : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
                  (sourceValues, targetValues) sourceClosure targetClosure :=
                .singletonRec valid.1 valid.2 functionLoc functionVars functionCompiled functionInstalled targetLookup
              have valueRel : vRel s.maxApp f t.refs t.code sourceClosure targetClosure := .closure valuesRel closureRel
              have extendedEnv : envRel s.maxApp f t.refs t.code (sourceClosure :: sourceEnv) (targetClosure :: targetEnv) :=
                ⟨valueRel, envRelated⟩
              have bodyPost := bodyIH s sFinal t (sourceClosure :: sourceEnv) (targetClosure :: targetEnv) f
                (entry :: auxFunction) finalAux [targetBody] result bodyRun noTypeError bodyCompiled bodyLoc
                annotations bodyVars installed extendedEnv states
              obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, related, state, map, refs, finalAnnotations, clocks⟩ := bodyPost
              have closureRun : BvlSem.evaluate [closureExp] targetEnv { t with clock := s.clock + clock } =
                  (.val [targetClosure], { t with clock := s.clock + clock }) := by
                simpa [closureExp, targetClosure] using evaluate_closure_block indices targetEnv
                  { t with clock := s.clock + clock } targetValues (label + numStubs s.maxApp) (arity - 1)
                  targetCapture ⟨_, targetLookup⟩
              refine ⟨clock, targetResult, tFinal, fFinal, ?_, related, state, map, refs, finalAnnotations, clocks⟩
              rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, closureRun]
              exact targetRun
      · simp [ClosSem.evaluate, valid] at run
        exact False.elim (noTypeError run.1.symm)

end Flapjack.Compiler.Backend.ClosToBvl
