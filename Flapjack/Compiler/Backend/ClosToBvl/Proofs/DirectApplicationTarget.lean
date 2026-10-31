import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateApp

/-! Installed-code facts for known-location closure calls. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- The code pointer in a related recursive closure is its source location,
shifted by the stub count and the recursive function index. -/
theorem clRel_recclosure_direct_address {maxApp : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {captured : List ClosSem.Value} {fields : List BvlSem.Value} {ptr index arity : Nat}
    {functions : List (Nat × ClosLang.Exp)} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (found : functions[index]? = some (arity, body)) :
    ∃ payload, target = .block 30
      (.codePtr ((ptr + 2 * index) + numStubs maxApp) :: .number (Int.ofNat (arity - 1)) :: payload) := by
  cases related with
  | singletonRec bound positive loc vars compiled installed lookup =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨fields, by simp⟩
  | @mutualRec exps entries ps rs loc r env ys k expsEq psEq positions values fresh stored many indexBound locations vars installed =>
    have entryBound : index < entries.length := by simpa [expsEq] using indexBound
    have entryEq : (entries[index]'entryBound).1 = (arity, body) := by
      have h : functions[index]? = some (arity, body) := found
      rw [expsEq, List.getElem?_map, List.getElem?_eq_getElem entryBound] at h
      simpa using h
    have entryAddress : (entries[index]'entryBound).2 = ptr + numStubs maxApp + 2 * index := by
      have actual : ps[index]? = some (entries[index]'entryBound).2 := by
        simp [psEq, List.getElem?_map, List.getElem?_eq_getElem entryBound]
      have expected : ps[index]? = some (ptr + numStubs maxApp + 2 * index) := by
        simp [positions, entryBound]
      exact Option.some.inj (actual.symm.trans expected)
    subst rs
    rw [Flapjack.holEl_eq_getElem index _ (by simpa using entryBound)]
    simp only [List.getElem_map]
    cases h : entries[index]'entryBound with
    | mk pair label =>
      have pairEq : pair = (arity, body) := by simpa [h] using entryEq
      have labelEq : label = (ptr + 2 * index) + numStubs maxApp := by
        have := entryAddress
        simp only [h] at this
        omega
      subst pair
      subst label
      exact ⟨_, rfl⟩

/-- A related recursive closure resolves its known-location target call with
one extra argument for the closure block itself. -/
theorem vRel_recclosure_direct_findCode {maxApp ptr index arity : Nat}
    {f : HolFiniteMapExact Nat Nat} {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {captured : List ClosSem.Value}
    {functions : List (Nat × ClosLang.Exp)} {sourceBody : ClosLang.Exp} {target : BvlSem.Value}
    {sourceArgs : List ClosSem.Value} {targetArgs : List BvlSem.Value}
    (related : vRel maxApp f refs code (.recclosure (some ptr) [] captured functions index) target)
    (found : functions[index]? = some (arity, sourceBody))
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) :
    ∃ entry, BvlSem.findCode (some ((ptr + 2 * index) + numStubs maxApp))
      (targetArgs ++ [target]) code = some (targetArgs ++ [target], entry) := by
  obtain ⟨fields, _, closure⟩ := vRel_recclosure_original related
  obtain ⟨expectedPayload, expectedShape⟩ := clRel_recclosure_direct_address closure found
  obtain ⟨address, payload, entry, actualShape, lookup⟩ := clRel_recclosure_target_code closure found
  have addressEq : address = (ptr + 2 * index) + numStubs maxApp := by
    have equal := actualShape.symm.trans expectedShape
    simp only [BvlSem.Value.block.injEq, List.cons.injEq, BvlSem.Value.codePtr.injEq] at equal
    exact equal.2.1
  subst address
  have length : targetArgs.length = arity := argsRel.length_eq.symm.trans arityMatch
  exact ⟨entry, by simp [BvlSem.findCode, lookup, length]⟩

/-- A related ordinary closure resolves its known-location target call with
one extra argument for the closure block itself. -/
theorem vRel_ordinary_direct_findCode {maxApp ptr arity : Nat}
    {f : HolFiniteMapExact Nat Nat} {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {captured : List ClosSem.Value} {sourceBody : ClosLang.Exp}
    {target : BvlSem.Value} {sourceArgs : List ClosSem.Value} {targetArgs : List BvlSem.Value}
    (related : vRel maxApp f refs code (.closure (some ptr) [] captured arity sourceBody) target)
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) :
    ∃ entry, BvlSem.findCode (some (ptr + numStubs maxApp)) (targetArgs ++ [target]) code =
      some (targetArgs ++ [target], entry) := by
  obtain ⟨fields, _, closure⟩ := vRel_ordinary_closure related
  cases closure with
  | closure bound positive locations vars compiled installed lookup =>
    have length : targetArgs.length = arity := argsRel.length_eq.symm.trans arityMatch
    have has : ∃ entry, sptLookup (ptr + numStubs maxApp) code = some (arity + 1, entry) := ⟨_, lookup⟩
    obtain ⟨entry, entryLookup⟩ := has
    exact ⟨entry, by simp [BvlSem.findCode, entryLookup, length]⟩

/-- Whenever a related closure accepts a known-location application, the
compiled direct call resolves to installed code with the right arity. -/
theorem vRel_direct_findCode {maxApp address : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {function : ClosSem.Value} {target : BvlSem.Value} {sourceArgs : List ClosSem.Value}
    {targetArgs : List BvlSem.Value} {application : ClosSem.AppKind}
    (related : vRel maxApp f refs code function target)
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (found : ClosSem.destClosure maxApp (some address) function sourceArgs = some application) :
    ∃ entry, BvlSem.findCode (some (address + numStubs maxApp)) (targetArgs ++ [target]) code =
      some (targetArgs ++ [target], entry) := by
  cases function <;> simp only [ClosSem.destClosure] at found <;> try contradiction
  case closure location supplied captured arity body =>
    have shape := ClosSem.destClosure_direct_closure maxApp address location supplied captured sourceArgs arity body application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨rfl, rfl, arityEq, _, _⟩ := shape
    exact vRel_ordinary_direct_findCode related argsRel arityEq.symm
  case recclosure location supplied captured functions index =>
    have shape := ClosSem.destClosure_direct_recclosure maxApp address location supplied captured sourceArgs functions index application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨arity, body, selected, locationEq, rfl, arityEq, _, _⟩ := shape
    cases location with
    | none => simp at locationEq
    | some ptr =>
      simp only [Option.map, Option.some.injEq] at locationEq
      subst address
      have call := vRel_recclosure_direct_findCode related selected argsRel arityEq.symm
      simpa [Nat.add_comm] using call

/-- A successfully selected known-location closure has the target block
layout expected by an exact generic closure call. -/
theorem vRel_direct_shape {maxApp address : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {function : ClosSem.Value} {target : BvlSem.Value} {sourceArgs : List ClosSem.Value}
    {targetArgs : List BvlSem.Value} {application : ClosSem.AppKind}
    (related : vRel maxApp f refs code function target)
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (found : ClosSem.destClosure maxApp (some address) function sourceArgs = some application) :
    ∃ payload, target = .block 30 (.codePtr (address + numStubs maxApp) ::
      .number (Int.ofNat (targetArgs.length - 1)) :: payload) := by
  have argLength : targetArgs.length = sourceArgs.length := argsRel.length_eq.symm
  cases function <;> simp only [ClosSem.destClosure] at found <;> try contradiction
  case closure location supplied captured arity body =>
    have shape := ClosSem.destClosure_direct_closure maxApp address location supplied captured sourceArgs arity body application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨rfl, rfl, arityEq, _, _⟩ := shape
    obtain ⟨fields, _, closure⟩ := vRel_ordinary_closure related
    cases closure with
    | closure _ _ _ _ _ _ _ => exact ⟨fields, by simp [argLength, arityEq]⟩
  case recclosure location supplied captured functions index =>
    have shape := ClosSem.destClosure_direct_recclosure maxApp address location supplied captured sourceArgs functions index application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨arity, body, selected, locationEq, rfl, arityEq, _, _⟩ := shape
    cases location with
    | none => simp at locationEq
    | some ptr =>
      simp only [Option.map, Option.some.injEq] at locationEq
      subst address
      obtain ⟨fields, _, closure⟩ := vRel_recclosure_original related
      obtain ⟨payload, targetEq⟩ := clRel_recclosure_direct_address closure selected
      exact ⟨payload, by simpa [argLength, arityEq, Nat.add_comm] using targetEq⟩

/-- Generated direct-call argument variables read the same values as the
exact generic closure-call path. -/
theorem evaluate_directCall_env {C F : Type} (s : BvlSem.State C F)
    (values rest : List BvlSem.Value) (closure : BvlSem.Value) (address : Nat) (body : Bvl.Exp)
    (nonempty : values ≠ [])
    (found : BvlSem.findCode (some address) (values ++ [closure]) s.code = some (values ++ [closure], body)) :
    BvlSem.evaluate [.call (values.length - 1) (some address)
      ((List.range values.length).map Bvl.Exp.var ++ [.var values.length])]
      (values ++ [closure] ++ rest) s =
      if s.clock < values.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body] (values ++ [closure]) (BvlSem.decClock values.length s) := by
  let env := values ++ [closure] ++ rest
  have argsRun : BvlSem.evaluate ((List.range values.length).map Bvl.Exp.var) env s = (.val values, s) := by
    have bound : values.length ≤ env.length := by simp [env]
    simpa [env] using evaluate_rangeVars values.length env s bound
  have closureRun : BvlSem.evaluate [.var values.length] env s = (.val [closure], s) := by
    simp [BvlSem.evaluate, env]
  have arguments : BvlSem.evaluate ((List.range values.length).map Bvl.Exp.var ++ [.var values.length]) env s =
      (.val (values ++ [closure]), s) := by
    change BvlSem.evaluateTuple (((List.range values.length).map Bvl.Exp.var ++ [.var values.length]), env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, closureRun]
  have count : values.length - 1 + 1 = values.length := by
    cases values <;> simp_all
  change BvlSem.evaluate [.call (values.length - 1) (some address)
    ((List.range values.length).map Bvl.Exp.var ++ [.var values.length])] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, arguments]
  simp [found, count]

/-- A direct target call and the exact generic closure call execute the same
installed entry at the same clock when the source accepted the location. -/
theorem evaluate_directCall_eq_generic {C F : Type} (s : BvlSem.State C F)
    (maxApp address : Nat) (f : HolFiniteMapExact Nat Nat)
    (function : ClosSem.Value) (target : BvlSem.Value)
    (sourceArgs : List ClosSem.Value) (targetArgs rest : List BvlSem.Value) (application : ClosSem.AppKind)
    (related : vRel maxApp f s.refs s.code function target)
    (argsRel : List.Forall₂ (vRel maxApp f s.refs s.code) sourceArgs targetArgs)
    (found : ClosSem.destClosure maxApp (some address) function sourceArgs = some application)
    (nonempty : targetArgs ≠ []) :
    BvlSem.evaluate [.call (targetArgs.length - 1) (some (address + numStubs maxApp))
      ((List.range targetArgs.length).map Bvl.Exp.var ++ [.var targetArgs.length])]
      (targetArgs ++ [target] ++ rest) s =
    BvlSem.evaluate [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)]
      (targetArgs ++ [target] ++ rest) s := by
  obtain ⟨payload, targetEq⟩ := vRel_direct_shape related argsRel found
  obtain ⟨entry, targetFound⟩ := vRel_direct_findCode related argsRel found
  have lookup : sptLookup (address + numStubs maxApp) s.code = some (targetArgs.length + 1, entry) := by
    cases h : sptLookup (address + numStubs maxApp) s.code with
    | none => simp [BvlSem.findCode, h] at targetFound
    | some pair =>
      obtain ⟨arity, expression⟩ := pair
      simp [BvlSem.findCode, h] at targetFound
      obtain ⟨arityEq, entryEq⟩ := targetFound
      subst arity
      subst expression
      rfl
  have direct := evaluate_directCall_env s targetArgs rest target (address + numStubs maxApp) entry nonempty targetFound
  rw [direct, targetEq]
  exact (evaluate_mkClCall_direct_env s targetArgs rest 30 (address + numStubs maxApp) payload entry nonempty lookup).symm

/-- The arity bound carried by related closures also bounds a successful
known-location application's argument count. -/
theorem vRel_direct_args_bound {maxApp address : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {function : ClosSem.Value} {target : BvlSem.Value} {sourceArgs : List ClosSem.Value}
    {application : ClosSem.AppKind}
    (related : vRel maxApp f refs code function target)
    (found : ClosSem.destClosure maxApp (some address) function sourceArgs = some application) :
    sourceArgs.length ≤ maxApp := by
  cases function <;> simp only [ClosSem.destClosure] at found <;> try contradiction
  case closure location supplied captured arity body =>
    have shape := ClosSem.destClosure_direct_closure maxApp address location supplied captured sourceArgs arity body application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨rfl, rfl, arityEq, _, _⟩ := shape
    obtain ⟨fields, _, closure⟩ := vRel_ordinary_closure related
    cases closure with
    | closure bound _ _ _ _ _ _ => simpa [arityEq] using bound
  case recclosure location supplied captured functions index =>
    have shape := ClosSem.destClosure_direct_recclosure maxApp address location supplied captured sourceArgs functions index application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨arity, body, selected, locationEq, rfl, arityEq, _, _⟩ := shape
    cases location with
    | none => simp at locationEq
    | some ptr =>
      obtain ⟨fields, _, closure⟩ := vRel_recclosure_original related
      have bound := (clRel_recclosure_arity closure selected).1
      simpa [arityEq] using bound

/-- A known-location closure application is simulated by the direct target
call using the bounded induction hypothesis for source closure bodies. -/
theorem evaluateApp_direct_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (address clockBound : Nat) (function : ClosSem.Value) (target : BvlSem.Value)
    (sourceArgs : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (application : ClosSem.AppKind) (result : Result (List ClosSem.Value) ClosSem.Value)
    (clockBounded : s.clock ≤ clockBound)
    (found : ClosSem.destClosure s.maxApp (some address) function sourceArgs = some application)
    (run : ClosSem.evaluateApp (some address) function sourceArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code function target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [.call (targetArgs.length - 1) (some (address + numStubs s.maxApp))
        ((List.range targetArgs.length).map Bvl.Exp.var ++ [.var targetArgs.length])] := by
  have bound := vRel_direct_args_bound functionRel found
  have sourceNonempty : sourceArgs ≠ [] := by
    cases application with
    | partialApp value => exact False.elim (ClosSem.destClosure_direct_not_partial _ _ _ _ _ found)
    | fullApp body env remaining =>
      have h := ClosSem.destClosure_full_remaining_lt s.maxApp (some address) function sourceArgs env remaining body found
      intro empty
      simp [empty] at h
  have targetNonempty : targetArgs ≠ [] := by
    intro empty
    have length := argsRel.length_eq
    simp [empty] at length
    exact sourceNonempty length
  have genericRun : ClosSem.evaluateApp none function sourceArgs s = (result, sFinal) := by
    rw [← ClosSem.evaluateApp_direct_eq_generic address function sourceArgs s application bound found]
    exact run
  have post := applicationSimulationThrough_of_body_simulationBelow clockBound bodyIH sourceArgs sourceNonempty
    s sFinal t f function target targetArgs rest result clockBounded genericRun noType states annotations functionRel argsRel
  obtain ⟨extra, targetResult, tFinal, fFinal, targetRun, resultRelated, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := post
  refine ⟨extra, targetResult, tFinal, fFinal, ?_, resultRelated, finalStates, map, frame, finalAnnotations, finalClock⟩
  have same := evaluate_directCall_eq_generic { t with clock := s.clock + extra } s.maxApp address f function target
    sourceArgs targetArgs rest application (by simpa using functionRel) (by simpa using argsRel) found targetNonempty
  rw [same]
  exact targetRun

end Flapjack.Compiler.Backend.ClosToBvl
