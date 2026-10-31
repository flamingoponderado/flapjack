import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateLet

/-! Direct-call cases of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- A successful source direct-code lookup has a compiled target entry with
matching arguments and installed auxiliary code. The state relation and source
lookup remain candidates pending HOL carrier review. -/
theorem stateRel_findCode {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (location : Nat)
    (args : List ClosSem.Value) (targetArgs : List BvlSem.Value) (body : ClosLang.Exp)
    (states : stateRel f s t)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : ClosSem.findCode location args s.code = some (args, body)) :
    ∃ aux targetBody finalAux,
      compileExpsHOL s.maxApp [body] aux = ([targetBody], finalAux) ∧
      BvlSem.findCode (some (location + numStubs s.maxApp)) targetArgs t.code = some (targetArgs, targetBody) ∧
      codeInstalled finalAux t.code := by
  cases lookup : s.code.lookup location with
  | none => simp [ClosSem.findCode, lookup] at found
  | some entry =>
    obtain ⟨arity, sourceBody⟩ := entry
    simp [ClosSem.findCode, lookup] at found
    obtain ⟨arityEq, rfl⟩ := found
    obtain ⟨aux, targetBody, finalAux, compiled, targetLookup, installed⟩ :=
      states.2.2.2.2.2.2.2.2.2.2.2.2 location arity sourceBody lookup
    refine ⟨aux, targetBody, finalAux, compiled, ?_, installed⟩
    have lengthEq : args.length = targetArgs.length := argsRel.length_eq
    simp [BvlSem.findCode, targetLookup, ← lengthEq, arityEq]

/-- A source argument error propagates through the target direct call. -/
theorem evaluatePost_call_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (ticks location : Nat) (args : List Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.call ticks (some location) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- A resolved direct call with insufficient clock times out on both sides.
The argument simulation supplies the related state and argument values. -/
theorem evaluatePost_call_timeout {C F : Type} (s sMiddle : ClosSem.State C F)
    (t : BvlSem.State C F) (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (ticks location : Nat) (args : List ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (values : List ClosSem.Value) (body : ClosLang.Exp)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sMiddle))
    (found : ClosSem.findCode location values sMiddle.code = some (values, body))
    (timeout : sMiddle.clock < ticks + 1)
    (argsPost : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs) :
    evaluatePost s { sMiddle with clock := 0 } t targetEnv f (.err (.abort .timeoutError))
      [.call ticks (some (location + numStubs s.maxApp)) targetArgs] := by
  have maxApp : sMiddle.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
    rw [argsRun] at h
    exact h
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := argsPost
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code) values targetValues := by
      simpa [maxApp, resultRel] using related
    obtain ⟨_, targetBody, _, _, targetFound, _⟩ :=
      stateRel_findCode sMiddle tMiddle fMiddle location values targetValues body state argsRel found
    have targetFound' : BvlSem.findCode (some (location + numStubs s.maxApp)) targetValues tMiddle.code =
        some (targetValues, targetBody) := by simpa [maxApp] using targetFound
    refine ⟨clock, .err (.abort .timeoutError), { tMiddle with clock := 0 }, fMiddle, ?_, ?_, ?_,
      map, refs, ?_, rfl⟩
    · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
      simp only [targetFound']
      have targetTimeout : tMiddle.clock < ticks + 1 := by omega
      simp [targetTimeout]
    · simp [resultRel, excRel]
    · exact (stateRel_clock fMiddle sMiddle tMiddle 0).2.mpr ((stateRel_clock fMiddle sMiddle tMiddle 0).1.mpr state)
    · exact annotations

/-- Compose argument evaluation with a resolved call body when enough clock is
available. The continuation is the smaller-clock induction hypothesis for the
body selected by source code lookup. -/
theorem evaluatePost_call_body {C F : Type} (s sMiddle sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (ticks location : Nat) (args : List ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (values : List ClosSem.Value) (body : ClosLang.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sMiddle))
    (found : ClosSem.findCode location values sMiddle.code = some (values, body))
    (enough : ticks + 1 ≤ sMiddle.clock)
    (argsPost : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (bodyIH : ∀ (targetValues : List BvlSem.Value) (tMiddle : BvlSem.State C F)
      (fMiddle : HolFiniteMapExact Nat Nat) (targetBody : Bvl.Exp)
      (aux finalAux : List (Nat × Nat × Bvl.Exp)),
      stateRel fMiddle sMiddle tMiddle →
      List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code) values targetValues →
      codeAnnotations sMiddle → compileExpsHOL sMiddle.maxApp [body] aux = ([targetBody], finalAux) →
      codeInstalled finalAux tMiddle.code →
      evaluatePost (ClosSem.decClock (ticks + 1) sMiddle) sFinal
        (BvlSem.decClock (ticks + 1) tMiddle) targetValues fMiddle result [targetBody]) :
    evaluatePost s sFinal t targetEnv f result [.call ticks (some (location + numStubs s.maxApp)) targetArgs] := by
  have maxApp : sMiddle.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
    rw [argsRun] at h
    exact h
  obtain ⟨clock1, targetResult, tMiddle, fMiddle, targetRun1, related1, state1, map1, refs1,
    annotations1, clocks1⟩ := argsPost
  cases targetResult with
  | err error => simp [resultRel] at related1
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code) values targetValues := by
      simpa [maxApp, resultRel] using related1
    obtain ⟨aux, targetBody, finalAux, compiled, targetFound, installed⟩ :=
      stateRel_findCode sMiddle tMiddle fMiddle location values targetValues body state1 argsRel found
    have targetFound' : BvlSem.findCode (some (location + numStubs s.maxApp)) targetValues tMiddle.code =
        some (targetValues, targetBody) := by simpa [maxApp] using targetFound
    obtain ⟨clock2, result2, tFinal, fFinal, targetRun2, related2, state2, map2, refs2,
      annotations2, clocks2⟩ := bodyIH targetValues tMiddle fMiddle targetBody aux finalAux state1 argsRel
        annotations1 compiled installed
    have shifted := BvlProps.evaluate_addClock targetArgs targetEnv
      { t with clock := s.clock + clock1 } tMiddle (.val targetValues) clock2 targetRun1 (by simp)
    have runArgs : BvlSem.evaluate targetArgs targetEnv
        { t with clock := s.clock + (clock1 + clock2) } =
        (.val targetValues, { tMiddle with clock := sMiddle.clock + clock2 }) := by
      simpa [Nat.add_assoc, clocks1] using shifted
    have clockEq : sMiddle.clock + clock2 - (ticks + 1) = sMiddle.clock - (ticks + 1) + clock2 := by omega
    have targetEnough : ¬ sMiddle.clock + clock2 < ticks + 1 := by omega
    refine ⟨clock1 + clock2, result2, tFinal, fFinal, ?_, ?_, state2,
      relocationSubmap_trans map1 map2, unmappedRefsSubmap_trans refs1 refs2, annotations2, clocks2⟩
    · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, runArgs]
      simp only [targetFound', targetEnough, ↓reduceIte]
      simpa [ClosSem.decClock, BvlSem.decClock, clockEq] using targetRun2
    · simpa [ClosSem.decClock, maxApp] using related2

/-- Successful source lookup retains its arguments and identifies the
underlying code entry. -/
theorem findCode_shape {α : Type} (location : Nat) (args returned : List α)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (found : ClosSem.findCode location args code = some (returned, body)) :
    returned = args ∧ ∃ arity, code.lookup location = some (arity, body) := by
  cases lookup : code.lookup location with
  | none => simp [ClosSem.findCode, lookup] at found
  | some entry =>
    obtain ⟨arity, codeBody⟩ := entry
    simp [ClosSem.findCode, lookup] at found
    obtain ⟨_, argsEq, bodyEq⟩ := found
    subst codeBody
    exact ⟨argsEq.symm, arity, rfl⟩

/-- Direct-call evaluator case from the argument simulation and the
smaller-clock induction hypothesis for the looked-up body. Compiler
accumulator bookkeeping for the enclosing expression is kept outside this
helper. -/
theorem evaluate_call_post {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (targetArgs : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.call trace ticks location args] sourceEnv s = (result, sFinal))
    (noTypeError : result ≠ .err (.abort .typeError))
    (argsIH : ∀ (argResult : Result (List ClosSem.Value) ClosSem.Value) (sMiddle : ClosSem.State C F),
      ClosSem.evaluate args sourceEnv s = (argResult, sMiddle) →
      argResult ≠ .err (.abort .typeError) → evaluatePost s sMiddle t targetEnv f argResult targetArgs)
    (bodyIH : ∀ (body : ClosLang.Exp) (start last : ClosSem.State C F) (targetStart : BvlSem.State C F)
      (sourceArgs : List ClosSem.Value) (targetValues : List BvlSem.Value) (fMiddle : HolFiniteMapExact Nat Nat)
      (aux finalAux : List (Nat × Nat × Bvl.Exp)) (targetBody : Bvl.Exp),
      start.clock < s.clock → ClosSem.evaluate [body] sourceArgs start = (result, last) →
      compileExpsHOL start.maxApp [body] aux = ([targetBody], finalAux) →
      ClosProps.everyFnLocationSome [body] → codeAnnotations start → ClosProps.everyFnVarsSome [body] →
      codeInstalled finalAux targetStart.code →
      envRel start.maxApp fMiddle targetStart.refs targetStart.code sourceArgs targetValues →
      stateRel fMiddle start targetStart →
      evaluatePost start last targetStart targetValues fMiddle result [targetBody]) :
    evaluatePost s sFinal t targetEnv f result [.call ticks (some (location + numStubs s.maxApp)) targetArgs] := by
  have argBound := ClosSem.evaluate_clock_le args sourceEnv s
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases argsRun : ClosSem.evaluate args sourceEnv s with
  | mk argResult sMiddle =>
    simp only [argsRun] at run argBound
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact evaluatePost_call_error s sMiddle t targetEnv f ticks (location + numStubs s.maxApp) targetArgs error
        (argsIH (.err error) sMiddle argsRun noTypeError)
    | val values =>
      dsimp only at run
      cases found : ClosSem.findCode location values sMiddle.code with
      | none =>
        simp [found] at run
        exact False.elim (noTypeError run.1.symm)
      | some entry =>
        obtain ⟨returned, body⟩ := entry
        have returnedEq := (findCode_shape location values returned sMiddle.code body found).1
        subst returned
        rw [found] at run
        dsimp only at run
        have argsPost := argsIH (.val values) sMiddle argsRun (by simp)
        by_cases timeout : sMiddle.clock < ticks + 1
        · simp [timeout] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_call_timeout s sMiddle t sourceEnv targetEnv f ticks location args targetArgs values body
            argsRun found timeout argsPost
        · have enough : ticks + 1 ≤ sMiddle.clock := by omega
          have bodyRun : ClosSem.evaluate [body] values (ClosSem.decClock (ticks + 1) sMiddle) = (result, sFinal) := by
            simpa [timeout] using run
          apply evaluatePost_call_body s sMiddle sFinal t sourceEnv targetEnv f ticks location args targetArgs values body
            result argsRun found enough argsPost
          intro targetValues tMiddle fMiddle targetBody aux finalAux middleStates argsRel middleAnnotations compiled installed
          let start := ClosSem.decClock (ticks + 1) sMiddle
          let targetStart := BvlSem.decClock (ticks + 1) tMiddle
          have smaller : start.clock < s.clock := by simp [start, ClosSem.decClock]; omega
          have codeFound := (findCode_shape location values values sMiddle.code body found).2
          obtain ⟨arity, lookup⟩ := codeFound
          have bodyLoc := middleAnnotations.1 location arity body lookup
          have bodyVars := middleAnnotations.2 location arity body lookup
          have startAnnotations : codeAnnotations start := by simpa [start, ClosSem.decClock, codeAnnotations] using middleAnnotations
          have startCompiled : compileExpsHOL start.maxApp [body] aux = ([targetBody], finalAux) := by
            simpa [start, ClosSem.decClock] using compiled
          have startInstalled : codeInstalled finalAux targetStart.code := by simpa [targetStart, BvlSem.decClock] using installed
          have startEnv : envRel start.maxApp fMiddle targetStart.refs targetStart.code values targetValues := by
            have h := envRel_prepend argsRel (envRelated := (show envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code [] [] from trivial))
            simpa [start, targetStart, ClosSem.decClock, BvlSem.decClock] using h
          have startStates : stateRel fMiddle start targetStart := by
            exact (stateRel_clock fMiddle sMiddle tMiddle (sMiddle.clock - (ticks + 1))).2.mpr
              ((stateRel_clock fMiddle sMiddle tMiddle (tMiddle.clock - (ticks + 1))).1.mpr middleStates)
          exact bodyIH body start sFinal targetStart values targetValues fMiddle aux finalAux targetBody smaller
            bodyRun startCompiled bodyLoc startAnnotations bodyVars startInstalled startEnv startStates

/-- Direct-call case with the source compiler's accumulator and installed-code
premises. The body induction hypothesis is available only at a smaller clock,
as in the source evaluator's induction. This candidate remains untagged pending
review of the source and target semantic carriers. -/
theorem expressionSimulation_call_case {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.call trace ticks location args] sourceEnv s = (result, sFinal))
    (noTypeError : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.call trace ticks location args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.call trace ticks location args])
    (annotations : codeAnnotations s) (varsAnnotated : ClosProps.everyFnVarsSome [.call trace ticks location args])
    (installed : codeInstalled finalAux t.code) (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (states : stateRel f s t) (argsIH : expressionSimulation (C := C) (F := F) args)
    (bodyIH : ∀ (body : ClosLang.Exp) (start last : ClosSem.State C F) (targetStart : BvlSem.State C F)
      (sourceArgs : List ClosSem.Value) (targetValues : List BvlSem.Value) (fMiddle : HolFiniteMapExact Nat Nat)
      (aux finalAux : List (Nat × Nat × Bvl.Exp)) (targetBody : Bvl.Exp),
      start.clock < s.clock → ClosSem.evaluate [body] sourceArgs start = (result, last) →
      compileExpsHOL start.maxApp [body] aux = ([targetBody], finalAux) →
      ClosProps.everyFnLocationSome [body] → codeAnnotations start → ClosProps.everyFnVarsSome [body] →
      codeInstalled finalAux targetStart.code →
      envRel start.maxApp fMiddle targetStart.refs targetStart.code sourceArgs targetValues →
      stateRel fMiddle start targetStart →
      evaluatePost start last targetStart targetValues fMiddle result [targetBody]) :
    evaluatePost s sFinal t targetEnv f result compiled := by
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs auxLast =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, auxLast) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.call trace ticks location args] aux =
        ([.call ticks (some (location + numStubs s.maxApp)) targetArgs], auxLast) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLocations : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    apply evaluate_call_post s sFinal t sourceEnv targetEnv f trace ticks location args targetArgs result run noTypeError
    · intro argResult sMiddle argRun argNotType
      exact argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs argResult argRun argNotType
        argsCompiled argsLocations annotations argsVars installed envRelated states
    · exact bodyIH

end Flapjack.Compiler.Backend.ClosToBvl
