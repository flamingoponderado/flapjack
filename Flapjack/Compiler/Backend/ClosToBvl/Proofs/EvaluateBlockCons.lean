import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IntegerRelation

/-! Block construction case of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.BackendCommon

/-- A source block is related only to a target block with the shifted tag and
pointwise related fields. -/
theorem vRel_block_inv {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {tag : Nat} {fields : List ClosSem.Value} {target : BvlSem.Value}
    (related : vRel maxApp f refs code (.block tag fields) target) :
    ∃ targetFields, target = .block (closTagShift tag) targetFields ∧
      List.Forall₂ (vRel maxApp f refs code) fields targetFields := by
  cases related with
  | block fields => exact ⟨_, rfl, fields⟩
  | closure _ closure => cases closure
  | partialClosure _ _ _ _ _ added _ closure => cases closure <;> simp [addArgs] at added

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

/-- An error while evaluating the arguments propagates through the target
block construction. -/
theorem evaluatePost_consBlock_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (tag : Nat) (args : List Bvl.Exp)
    (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (.blockOp (.cons (closTagShift tag))) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- Construction shifts the tag and relates each field. -/
theorem evaluatePost_consBlock_success {C F : Type} (s sMiddle : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (tag : Nat) (targetArgs : List Bvl.Exp)
    (values : List ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sMiddle t targetEnv f (.val [.block tag values.reverse])
      [.op (.blockOp (.cons (closTagShift tag))) targetArgs] := by
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        values.reverse targetValues.reverse := by
      simpa [resultRel, maxApp] using reverse_related related
    refine ⟨clock, .val [.block (closTagShift tag) targetValues.reverse], tMiddle, fMiddle,
      ?_, ?_, state, map, refs, annotations, clocks⟩
    · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
      rfl
    · exact List.Forall₂.cons (by simpa [maxApp] using (vRel.block argsRel)) .nil

/-- The block-construction expression case follows from the argument-list
induction hypothesis. This candidate remains untagged pending review of the
semantic carriers and the assembled pass theorem. -/
theorem expressionSimulation_consBlock {C F : Type} (trace : BackendCommon.Tra)
    (tag : Nat) (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.blockOp (.cons tag)) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.blockOp (.cons tag)) args] aux =
        ([.op (.blockOp (.cons (closTagShift tag))) targetArgs], aux1) := by
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
        exact evaluatePost_consBlock_error s sMiddle t targetEnv f tag targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        simp [ClosSem.doApp, ClosSem.applyBlock] at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_consBlock_success s sMiddle t targetEnv f tag targetArgs values argsPost maxApp

end Flapjack.Compiler.Backend.ClosToBvl
