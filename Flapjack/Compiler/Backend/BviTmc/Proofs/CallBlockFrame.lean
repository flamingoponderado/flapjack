import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockEnvironment
import Flapjack.Compiler.Backend.BviTmc.Proofs.VariableEvaluation
import Flapjack.Compiler.Backend.BviTmc.Proofs.ListSimulation

/-! Ordinary simulation of constructor frames in call blocks. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockFrame
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation ListSimulation CallBlockEnvironment

/-- Flapjack infrastructure: well-formed constructor-frame variables are
read without changing the state, so only the child can fail or change it. -/
theorem evaluate_frame {C F : Type} (loc tag : Nat) (left right : List Nat)
    (child : CallBlock) (env : List Value) (state : BviState C F)
    (leftWf : wfVars env.length left) (rightWf : wfVars env.length right) :
    evaluate [callBlockToBvi loc (.callBlock tag left child right)] env state =
      match evaluate [callBlockToBvi loc child] env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) =>
        (.val [.block tag ((right.map (fun n => holEl n env)).reverse ++
          [holHd values] ++ (left.map (fun n => holEl n env)).reverse)], next) := by
  have leftRun := evaluate_vars_target left env.length env state leftWf (Nat.le_refl _)
  have argsRun : evaluate (left.map Bvi.Exp.var ++ [callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env state =
      match evaluate [callBlockToBvi loc child] env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) =>
        (.val (left.map (fun n => holEl n env) ++ values ++ right.map (fun n => holEl n env)), next) := by
    simp only [List.append_assoc]
    change BviSem.evaluateTuple (_, env, state) = _
    rw [evaluateAppend]
    simp only [BviSem.evaluateTuple, leftRun]
    have rightRun (next : BviState C F) := evaluate_vars_target right env.length env next rightWf (Nat.le_refl _)
    have tailRun : evaluate ([callBlockToBvi loc child] ++ right.map Bvi.Exp.var) env state =
        match evaluate [callBlockToBvi loc child] env state with
        | (.err error, next) => (.err error, next)
        | (.val values, next) => (.val (values ++ right.map (fun n => holEl n env)), next) := by
      change BviSem.evaluateTuple (_, env, state) = _
      rw [evaluateAppend]
      simp only [BviSem.evaluateTuple]
      cases childRun : evaluate [callBlockToBvi loc child] env state with
      | mk childResult next =>
        cases childResult with
        | err error => rfl
        | val values => simp [rightRun]
    rw [tailRun]
    cases childRun : evaluate [callBlockToBvi loc child] env state with
    | mk childResult next => cases childResult <;> simp

  simp only [callBlockToBvi]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  cases childRun : evaluate [callBlockToBvi loc child] env state with
  | mk childResult next =>
    cases childResult with
    | err error => rfl
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton _ env state next values childRun
      simp [BviTailrec.doApp_blockCons, List.reverse_append, holHd]

private theorem append_related (f : HolFiniteMapExact Nat Nat) {xs ys xs' ys' : List Value}
    (first : List.Forall₂ (valueRel f) xs ys) (second : List.Forall₂ (valueRel f) xs' ys') :
    List.Forall₂ (valueRel f) (xs ++ xs') (ys ++ ys') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

private theorem reverse_related (f : HolFiniteMapExact Nat Nat) {xs ys : List Value}
    (related : List.Forall₂ (valueRel f) xs ys) : List.Forall₂ (valueRel f) xs.reverse ys.reverse := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => simpa using append_related f ih (.cons head .nil)

/-- Flapjack infrastructure: a well-formed call-block constructor frame
preserves ordinary simulation of its child. -/
theorem evaluate_frame_core {C F : Type} (loc tag : Nat) (left right : List Nat) (child : CallBlock)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value)
    (run : evaluate [callBlockToBvi loc (.callBlock tag left child right)] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (environments : envRel opt f env1 env2) (leftWf : wfVars env1.length left) (rightWf : wfVars env1.length right)
    (childIH : ∀ r mid, evaluate [callBlockToBvi loc child] env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core [callBlockToBvi loc child] env2 f target r mid) :
    Core [callBlockToBvi loc (.callBlock tag left child right)] env2 f target result final := by
  have targetLength := envRel_length opt f env1 env2 environments
  have targetLeft := wfVars_expand env1.length env2.length left leftWf targetLength
  have targetRight := wfVars_expand env1.length env2.length right rightWf targetLength
  rw [evaluate_frame loc tag left right child env1 source leftWf rightWf] at run
  cases childRun : evaluate [callBlockToBvi loc child] env1 source with
  | mk childResult middle =>
    have childSafe : childResult ≠ .err (.abort .typeError) := by
      intro bad
      subst childResult
      simp [childRun] at run
      exact notTypeError run.1.symm
    obtain ⟨next, g, targetResult, targetRun, related, states, extension, fresh, unchanged, still⟩ :=
      childIH childResult middle childRun childSafe
    cases childResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err error' =>
        simp [childRun] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨next, g, .err error', ?_, related, states, extension, fresh, unchanged, still⟩
        rw [evaluate_frame loc tag left right child env2 target targetLeft targetRight, targetRun]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton _ env1 source middle values childRun
      cases targetResult with
      | err error => simp [resultRel] at related
      | val values' =>
        obtain ⟨value', rfl⟩ := evaluate_singleton _ env2 target next values' targetRun
        have valueRelated : valueRel g value value' := by
          simp only [resultRel] at related
          cases related with | cons h _ => exact h
        have leftRelated := wfVars_list_rel left opt f env1 env2 environments leftWf
        have rightRelated := wfVars_list_rel right opt f env1 env2 environments rightWf
        have leftNext := listRel_submap f g _ _ leftRelated extension
        have rightNext := listRel_submap f g _ _ rightRelated extension
        have fields : List.Forall₂ (valueRel g)
            ((right.map (fun n => holEl n env1)).reverse ++ [value] ++ (left.map (fun n => holEl n env1)).reverse)
            ((right.map (fun n => holEl n env2)).reverse ++ [value'] ++ (left.map (fun n => holEl n env2)).reverse) := by
          simpa [List.append_assoc] using append_related g (reverse_related g rightNext)
            (.cons valueRelated (reverse_related g leftNext))
        simp [childRun, holHd] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨next, g, .val [.block tag ((right.map (fun n => holEl n env2)).reverse ++
          [value'] ++ (left.map (fun n => holEl n env2)).reverse)], ?_, ?_, states, extension, fresh, unchanged, still⟩
        · rw [evaluate_frame loc tag left right child env2 target targetLeft targetRight, targetRun]
          rfl
        · exact .cons (.block _ _ _ (by simpa [List.append_assoc] using fields)) .nil

/-- Flapjack infrastructure: ordinary simulation of any well-formed call
block, assuming simulation of its recursive-call leaf. The optimized worker
and wrapper conclusions are not included. -/
theorem evaluate_cb_core {C F : Type} (loc : Nat) (cb : CallBlock)
    (source : BviState (Nat × C) F) (env1 : List Value) (opt : Bool)
    (f : HolFiniteMapExact Nat Nat) (target : BviState C F) (env2 : List Value)
    (environments : envRel opt f env1 env2)
    (leafIH : ∀ ticks args result final, wfVars env1.length args →
      evaluate [callBlockToBvi loc (.rCall ticks args)] env1 source = (result, final) →
      result ≠ .err (.abort .typeError) →
      Core [callBlockToBvi loc (.rCall ticks args)] env2 f target result final)
    (result : BviResult) (final : BviState (Nat × C) F)
    (wf : wfBlock env1.length cb) (run : evaluate [callBlockToBvi loc cb] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    Core [callBlockToBvi loc cb] env2 f target result final := by
  induction cb generalizing result final with
  | rCall ticks args => exact leafIH ticks args result final wf run notTypeError
  | callBlock tag left child right ih =>
    apply evaluate_frame_core loc tag left right child source env1 result final opt f target env2
      run notTypeError environments wf.1 wf.2.2.1
    intro r mid childRun childSafe
    exact ih r mid wf.2.1 childRun childSafe

end Flapjack.Compiler.Backend.BviTmc.CallBlockFrame
