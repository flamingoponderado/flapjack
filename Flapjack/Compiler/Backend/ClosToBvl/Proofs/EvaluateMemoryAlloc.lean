import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshMappedRefs
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IntegerRelation

/-! Mutable reference allocation in the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

private theorem reverse_related {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys) : List.Forall₂ R xs.reverse ys.reverse := by
  have appendRel : ∀ {a c : List α} {b d : List β}, List.Forall₂ R a b →
      List.Forall₂ R c d → List.Forall₂ R (a ++ c) (b ++ d) := by
    intro a c b d first second
    induction first with
    | nil => exact second
    | cons head tail ih => exact .cons head ih
  induction related with
  | nil => exact .nil
  | cons head tail ih => simpa using appendRel ih (.cons head .nil)

/-- Argument errors propagate through reference allocation. -/
theorem evaluatePost_ref_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (args : List Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.memOp .ref) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Allocating related argument lists yields related fresh references. -/
theorem evaluatePost_ref_success {C F : Type} (s sMiddle : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (targetArgs : List Bvl.Exp) (values : List ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (maxApp : sMiddle.maxApp = s.maxApp) :
    let ptr := ClosSem.leastUnusedRef sMiddle.refs
    let next := { sMiddle with refs := sMiddle.refs.updateEq (ptr, .valueArray values.reverse) }
    evaluatePost s next t targetEnv f (.val [.refPtr true ptr]) [.op (.memOp .ref) targetArgs] := by
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        values.reverse targetValues.reverse := by
      simpa [resultRel, maxApp] using reverse_related related
    have allocated := doApp_ref_related sMiddle tMiddle fMiddle values.reverse targetValues.reverse state argsRel
    let sourcePtr := ClosSem.leastUnusedRef sMiddle.refs
    let targetPtr := BvlSem.leastUnusedRef tMiddle.refs
    let newMap := fMiddle.updateEq (sourcePtr, targetPtr)
    let targetNext := { tMiddle with refs := tMiddle.refs.updateEq (targetPtr, .valueArray targetValues.reverse) }
    change _ ∧ BvlSem.doApp (.memOp .ref) targetValues.reverse tMiddle = .val (.refPtr true targetPtr, targetNext) ∧
      stateRel newMap _ targetNext ∧ vRel sMiddle.maxApp newMap targetNext.refs targetNext.code
        (.refPtr true sourcePtr) (.refPtr true targetPtr) ∧ relocationSubmap fMiddle newMap ∧
        unmappedRefsSubmap tMiddle.refs targetNext.refs fMiddle newMap at allocated
    refine ⟨clock, .val [.refPtr true targetPtr], targetNext, newMap, ?_, ?_, allocated.2.2.1,
      relocationSubmap_trans map allocated.2.2.2.2.1,
      unmappedRefsSubmap_trans refs allocated.2.2.2.2.2, annotations, clocks⟩
    · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
      simp [allocated.2.1]
    · exact .cons (by simpa [maxApp] using allocated.2.2.2.1) .nil

/-- The reference-allocation expression case follows from the argument-list
induction hypothesis. This candidate is untagged pending carrier review and
assembly of the pass theorem. -/
theorem expressionSimulation_ref {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.memOp .ref) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.memOp .ref) args] aux =
        ([.op (.memOp .ref) targetArgs], aux1) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile, compileOp]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args sourceEnv s with
    | mk argsResult sMiddle =>
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_ref_error s sMiddle t targetEnv f targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        simp [ClosSem.doApp, ClosSem.applyMemory] at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_ref_success s sMiddle t targetEnv f targetArgs values argsPost maxApp

/-- Argument errors propagate through repeated-array allocation. -/
theorem evaluatePost_refArray_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (args : List Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.memOp .refArray) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- A successful repeated-array allocation preserves the simulation. -/
theorem evaluatePost_refArray_success {C F : Type} (s sMiddle sLast : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (value : ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (run : ClosSem.doApp (.memOp .refArray) values.reverse sMiddle = .val (value, sLast))
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sLast t targetEnv f (.val [value]) [.op (.memOp .refArray) targetArgs] := by
  obtain ⟨count, initial, argsEq, nonnegative, valueEq, stateEq⟩ := refArray_success values.reverse sMiddle sLast value run
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        [.number count, initial] targetValues.reverse := by
      simpa [resultRel, maxApp, argsEq] using reverse_related related
    cases reversed : targetValues.reverse with
    | nil => rw [reversed] at argsRel; cases argsRel
    | cons targetCount tail =>
      cases tail with
      | nil => rw [reversed] at argsRel; cases argsRel with | cons _ tail => cases tail
      | cons targetInitial rest =>
        rw [reversed] at argsRel
        cases argsRel with
        | cons countRel tail =>
          cases tail with
          | cons initialRel tail =>
            cases tail
            have countEq := vRel_number_inv countRel
            subst targetCount
            have allocated := doApp_refArray_related sMiddle tMiddle fMiddle count nonnegative initial targetInitial state initialRel
            subst value
            subst sLast
            let sourcePtr := ClosSem.leastUnusedRef sMiddle.refs
            let targetPtr := BvlSem.leastUnusedRef tMiddle.refs
            let newMap := fMiddle.updateEq (sourcePtr, targetPtr)
            let targetNext := { tMiddle with refs := tMiddle.refs.updateEq (targetPtr, .valueArray (List.replicate count.toNat targetInitial)) }
            change _ ∧ BvlSem.doApp (.memOp .refArray) [.number count, targetInitial] tMiddle =
              .val (.refPtr true targetPtr, targetNext) ∧ stateRel newMap _ targetNext ∧
              vRel sMiddle.maxApp newMap targetNext.refs targetNext.code (.refPtr true sourcePtr) (.refPtr true targetPtr) ∧
              relocationSubmap fMiddle newMap ∧ unmappedRefsSubmap tMiddle.refs targetNext.refs fMiddle newMap at allocated
            refine ⟨clock, .val [.refPtr true targetPtr], targetNext, newMap, ?_, ?_, allocated.2.2.1,
              relocationSubmap_trans map allocated.2.2.2.2.1,
              unmappedRefsSubmap_trans refs allocated.2.2.2.2.2, annotations, clocks⟩
            · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
              simp [reversed, allocated.2.1]
            · exact .cons (by simpa [maxApp] using allocated.2.2.2.1) .nil

/-- The repeated-array allocation expression case follows from the argument-list
induction hypothesis. This candidate remains untagged pending review of the
semantic carriers and the assembled pass theorem. -/
theorem expressionSimulation_refArray {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.memOp .refArray) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.memOp .refArray) args] aux =
        ([.op (.memOp .refArray) targetArgs], aux1) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile, compileOp]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args sourceEnv s with
    | mk argsResult sMiddle =>
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_refArray_error s sMiddle t targetEnv f targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases appRun : ClosSem.doApp (.memOp .refArray) values.reverse sMiddle with
        | err error =>
          have errorEq := refArray_error values.reverse sMiddle error appRun
          simp [appRun] at run
          apply False.elim
          apply noTypeError
          simpa [errorEq] using run.1.symm
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp [appRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_refArray_success s sMiddle last t targetEnv f targetArgs values value argsPost appRun maxApp


/-- Argument errors propagate through mutable-byte allocation. -/
theorem evaluatePost_refByte_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (args : List Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.memOp (.refByte false)) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- A successful mutable-byte allocation preserves the simulation. -/
theorem evaluatePost_refByte_success {C F : Type} (s sMiddle sLast : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value) (value : ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (run : ClosSem.doApp (.memOp (.refByte false)) values.reverse sMiddle = .val (value, sLast))
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sLast t targetEnv f (.val [value]) [.op (.memOp (.refByte false)) targetArgs] := by
  obtain ⟨count, number, byte, argsEq, nonnegative, valid, valueEq, stateEq⟩ := refByte_success values.reverse sMiddle sLast value run
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        [.number count, .number number] targetValues.reverse := by
      simpa [resultRel, maxApp, argsEq] using reverse_related related
    cases reversed : targetValues.reverse with
    | nil => rw [reversed] at argsRel; cases argsRel
    | cons targetCount tail =>
      cases tail with
      | nil => rw [reversed] at argsRel; cases argsRel with | cons _ tail => cases tail
      | cons targetNumber rest =>
        rw [reversed] at argsRel
        cases argsRel with
        | cons countRel tail =>
          cases tail with
          | cons numberRel tail =>
            cases tail
            have numberEq := vRel_number_inv numberRel
            subst targetNumber
            have countEq := vRel_number_inv countRel
            subst targetCount
            have allocated := doApp_refByte_related sMiddle tMiddle fMiddle count number nonnegative byte valid state
            subst value
            subst sLast
            let sourcePtr := ClosSem.leastUnusedRef sMiddle.refs
            let targetPtr := BvlSem.leastUnusedRef tMiddle.refs
            let newMap := fMiddle.updateEq (sourcePtr, targetPtr)
            let targetNext := { tMiddle with refs := tMiddle.refs.updateEq (targetPtr, .byteArray false (List.replicate count.toNat byte)) }
            change _ ∧ BvlSem.doApp (.memOp (.refByte false)) [.number count, .number number] tMiddle =
              .val (.refPtr true targetPtr, targetNext) ∧ stateRel newMap _ targetNext ∧
              vRel sMiddle.maxApp newMap targetNext.refs targetNext.code (.refPtr true sourcePtr) (.refPtr true targetPtr) ∧
              relocationSubmap fMiddle newMap ∧ unmappedRefsSubmap tMiddle.refs targetNext.refs fMiddle newMap at allocated
            refine ⟨clock, .val [.refPtr true targetPtr], targetNext, newMap, ?_, ?_, allocated.2.2.1,
              relocationSubmap_trans map allocated.2.2.2.2.1,
              unmappedRefsSubmap_trans refs allocated.2.2.2.2.2, annotations, clocks⟩
            · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
              simp [reversed, allocated.2.1]
            · exact .cons (by simpa [maxApp] using allocated.2.2.2.1) .nil

/-- The mutable-byte allocation expression case follows from the argument-list
induction hypothesis. This candidate remains untagged pending review of the
semantic carriers and the assembled pass theorem. -/
theorem expressionSimulation_refByte {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.memOp (.refByte false)) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.memOp (.refByte false)) args] aux =
        ([.op (.memOp (.refByte false)) targetArgs], aux1) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile, compileOp]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args sourceEnv s with
    | mk argsResult sMiddle =>
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_refByte_error s sMiddle t targetEnv f targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases appRun : ClosSem.doApp (.memOp (.refByte false)) values.reverse sMiddle with
        | err error =>
          have errorEq := refByte_error values.reverse sMiddle error appRun
          simp [appRun] at run
          apply False.elim
          apply noTypeError
          simpa [errorEq] using run.1.symm
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp [appRun] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_refByte_success s sMiddle last t targetEnv f targetArgs values value argsPost appRun maxApp


/-- Argument errors propagate even for the unsupported allocation flag. -/
theorem evaluatePost_refByteTrue_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (args : List Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.memOp (.refByte true)) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- The unsupported source allocation flag always gives a type error after
successful argument evaluation; argument errors still propagate. -/
theorem expressionSimulation_refByteTrue {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.memOp (.refByte true)) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.memOp (.refByte true)) args] aux =
        ([.op (.memOp (.refByte true)) targetArgs], aux1) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile, compileOp]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args sourceEnv s with
    | mk argsResult sMiddle =>
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_refByteTrue_error s sMiddle t targetEnv f targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        simp [ClosSem.doApp, ClosSem.applyMemory] at run
        exact False.elim (noTypeError run.1.symm)

end Flapjack.Compiler.Backend.ClosToBvl
