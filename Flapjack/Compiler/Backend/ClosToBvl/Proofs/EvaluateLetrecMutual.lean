import Flapjack.Compiler.Backend.ClosToBvl.Proofs.RecursiveFill
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateLet
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateLetrec

/-! Mutual recursive-binding case of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- A mutually recursive source group is simulated by the generated shared
closure array and the compiled enclosing body. This candidate is untagged
pending review of the evaluator and state carriers. -/
theorem expressionSimulation_letrec_mutual {C F : Type}
    (names : List Basis.Pure.MlString.MlString) (location : Option Nat) (selected : Option (List Nat))
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (multi : 1 < functions.length)
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    expressionSimulation (C := C) (F := F) [.letrec names location selected functions body] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases location with
  | none => simp [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] at locations
  | some label =>
    cases selected with
    | none => simp [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] at varsAnnotated
    | some indices =>
      have locParts : ClosProps.fnLocationSomeFuns functions ∧ ClosProps.fnLocationSomeExp body := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varParts : ClosProps.fnVarsSomeFuns functions ∧ ClosProps.fnVarsSomeExp body := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
      have groupLoc : ClosProps.everyFnLocationSome (functions.map Prod.snd) :=
        (ClosProps.fnLocationSomeFuns_eq_map functions).1 locParts.1
      have groupVars : ClosProps.everyFnVarsSome (functions.map Prod.snd) :=
        (ClosProps.fnVarsSomeFuns_eq_map functions).1 varParts.1
      have bodyLoc : ClosProps.everyFnLocationSome [body] := by simpa [ClosProps.everyFnLocationSome] using locParts.2
      have bodyVars : ClosProps.everyFnVarsSome [body] := by simpa [ClosProps.everyFnVarsSome] using varParts.2
      by_cases valid : functions.all (fun (arity, _) => arity ≤ s.maxApp && arity != 0) = true
      · cases capture : ClosSem.lookupVars indices sourceEnv with
        | none =>
          simp [ClosSem.evaluate, valid, capture] at run
          exact False.elim (noTypeError run.1.symm)
        | some sourceValues =>
          have bodyRun : ClosSem.evaluate [body]
              (((List.range functions.length).map (fun index => ClosSem.Value.recclosure
                (some label) [] sourceValues functions index)) ++ sourceEnv) s = (result, sFinal) := by
            simpa [ClosSem.evaluate, valid, capture] using run
          have aritiesValid : ∀ n functionBody, (n, functionBody) ∈ functions → n ≤ s.maxApp ∧ n ≠ 0 := by
            intro n functionBody member
            have h := (List.all_eq_true.mp valid) (n, functionBody) member
            simpa using h
          obtain ⟨targetValues, targetCapture, valuesRel, captureLength⟩ :=
            lookupVars_related indices sourceEnv targetEnv sourceValues envRelated capture
          cases functionsCompile : compileExpFunsHOL s.maxApp functions aux with
          | mk targetFunctions auxFunctions =>
            let base := label + numStubs s.maxApp
            let entries := targetFunctions.map (fun (n, exp) => codeForReccCase (functions.length + indices.length) n exp)
            let auxRec := (buildAux base entries auxFunctions).2
            cases bodyCompile : compileExpHOL s.maxApp body auxRec with
            | mk targetBody auxLast =>
              have bodyCompiled : compileExpsHOL s.maxApp [body] auxRec = ([targetBody], auxLast) := by
                rw [compileExps_eq_list]
                simp [compileExpListHOL, bodyCompile]
              have wholeCompiled : compileExpsHOL s.maxApp [.letrec names (some label) (some indices) functions body] aux =
                  ([buildReccLetsHOL (functions.map Prod.fst) indices base functions.length targetBody], auxLast) := by
                cases functions with
                | nil => simp at multi
                | cons first rest =>
                  cases rest with
                  | nil => simp at multi
                  | cons second rest =>
                    rw [compileExps_eq_list]
                    have bodyCompile' := bodyCompile
                    simp only [auxRec, entries, base, List.length_cons] at bodyCompile'
                    simp [compileExpListHOL, compileExpHOL, functionsCompile, bodyCompile', base]
              have equal := compile.symm.trans wholeCompiled
              cases equal
              have recInstalled : codeInstalled auxRec t.code :=
                compileExps_codeInstalled s.maxApp [body] auxRec finalAux [targetBody] t.code bodyCompiled installed
              have groupInstalled : codeInstalled (buildAux base
                  (targetFunctions.map (fun (n, exp) => codeForReccCase (sourceValues.length + functions.length) n exp)) auxFunctions).2 t.code := by
                simpa [auxRec, entries, base, captureLength, Nat.add_comm] using recInstalled
              let ptr := BvlSem.leastUnusedRef t.refs
              let blocks := recursiveValues (recursiveEntries functions base) ptr
              let next := { t with refs := t.refs.updateEq (ptr, .valueArray (blocks ++ targetValues)) }
              have allocated := recursiveValues_allocate s t f functions label sourceValues targetValues aux auxFunctions targetFunctions
                states valuesRel multi groupLoc groupVars functionsCompile groupInstalled aritiesValid
              change stateRel f s next ∧ unmappedRefsSubmap t.refs next.refs f f ∧
                (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
                List.Forall₂ (vRel s.maxApp f next.refs next.code)
                  ((List.range functions.length).map (fun index => ClosSem.Value.recclosure
                    (some label) [] sourceValues functions index)) blocks at allocated
              obtain ⟨nextStates, frame, _, closuresRel⟩ := allocated
              have submap : relocationSubmap f f := by intro key value found; exact found
              have nextEnv := envRel_grow_refs envRelated submap frame
              have bodyEnv := envRel_prepend closuresRel nextEnv
              have bodyPost := bodyIH s sFinal next _ _ f auxRec finalAux [targetBody] result bodyRun noTypeError
                bodyCompiled bodyLoc annotations bodyVars installed bodyEnv nextStates
              obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, related, finalStates, map, refs,
                finalAnnotations, clocks⟩ := bodyPost
              have labels : ∀ index, index < functions.length → ∃ entry, sptLookup (base + 2 * index) t.code = some entry := by
                intro index bound
                have sourceFound : functions[index]? = some functions[index] := List.getElem?_eq_getElem bound
                cases sourceEntry : functions[index] with
                | mk arity functionBody =>
                  rw [sourceEntry] at sourceFound
                  obtain ⟨targetFunction, _, _, _, targetLookup, _⟩ :=
                    recursiveFunctions_installed_at s.maxApp functions aux auxFunctions targetFunctions t.code base
                      (sourceValues.length + functions.length) index arity functionBody functionsCompile groupInstalled sourceFound
                  exact ⟨_, targetLookup⟩
              have functionsNonempty : functions ≠ [] := by intro h; simp [h] at multi
              have builder := evaluate_buildReccLets_functions functions indices targetEnv { t with clock := s.clock + clock }
                targetValues base targetBody functionsNonempty targetCapture labels
              refine ⟨clock, targetResult, tFinal, fFinal, ?_, related, finalStates, map, ?_, finalAnnotations, clocks⟩
              · rw [builder]
                exact targetRun
              · exact unmappedRefsSubmap_trans frame refs
      · simp [ClosSem.evaluate, valid] at run
        exact False.elim (noTypeError run.1.symm)

/-- All recursive-binding group shapes satisfy the candidate simulation when
the enclosing body satisfies its induction hypothesis. -/
theorem expressionSimulation_letrec {C F : Type}
    (names : List Basis.Pure.MlString.MlString) (location : Option Nat) (selected : Option (List Nat))
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    expressionSimulation (C := C) (F := F) [.letrec names location selected functions body] := by
  cases functions with
  | nil => exact expressionSimulation_letrec_nil names location selected body bodyIH
  | cons first rest =>
    cases rest with
    | nil =>
      obtain ⟨arity, functionBody⟩ := first
      exact expressionSimulation_letrec_singleton names location selected arity functionBody body bodyIH
    | cons second rest =>
      exact expressionSimulation_letrec_mutual names location selected (first :: second :: rest) body (by simp) bodyIH

end Flapjack.Compiler.Backend.ClosToBvl
