module

public import Flapjack.Compiler.Backend.BvlHandle.Proofs.VarBound
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.HandleOk
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.SequenceCorrect

@[expose] public section


/-! Handler-shape properties of generated packing expressions. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlProps (bVarBound isVar)

/-- Lists consisting of variables and integer constants satisfy the handler invariant. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "handle_ok_Var_Const_list"]
theorem handleOk_varConstList (xs : List Bvl.Exp)
    (shape : xs.Forall (fun x => ∃ (v : Nat) (i : Int),
      x = .var v ∨ x = .op (.intOp (.const i)) [])) :
    handleOk xs := by
  rw [handleOk_every, List.forall_iff_forall_mem]
  rw [List.forall_iff_forall_mem] at shape
  intro x member
  obtain ⟨v, i, rfl | rfl⟩ := shape x member <;> simp [handleOk]

/-- A smart let is handler-safe precisely when its bindings and body are. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "handle_ok_SmartLet"]
theorem handleOk_smartLet (bindings : List Bvl.Exp) (body : Bvl.Exp) :
    handleOk [smartLet bindings body] ↔ handleOk bindings ∧ handleOk [body] := by
  cases bindings with
  | nil => simp [smartLet, handleOk]
  | cons first rest => cases body <;> simp [smartLet, handleOk]

/-- The packer's outer let has variable-only bindings and a bounded body;
its inner body also satisfies the handler-shape invariant. -/
theorem letLet_shape {α : Type} (n : Nat) (live : Spt α) (body : Bvl.Exp)
    (bound : bVarBound n [body]) (shape : handleOk [body]) :
    letOk (letLet n live body) ∧
      (match letLet n live body with
       | .let _ inner => handleOk [inner]
       | _ => True) := by
  let retained := (List.range n).filter fun i => (sptLookup i live).isSome
  let long := (List.range n).map fun i =>
    match retained.zipIdx.lookup i with
    | some packed => Bvl.Exp.var packed
    | none => zero
  have vars : (retained.map Bvl.Exp.var).all isVar = true := by
    simp [List.all_eq_true, isVar]
  have longBound : bVarBound retained.length long := by
    rw [bVarBound_every]
    intro expression member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    cases found : retained.zipIdx.lookup index with
    | none => simp [zero, bVarBound]
    | some packed =>
      have slot := lookup_zipIdx_getElem retained index packed found
      have packedBound : packed < retained.length := (List.getElem?_eq_some_iff.mp slot).1
      simpa [bVarBound] using packedBound
  have longShape : handleOk long := by
    apply handleOk_varConstList
    rw [List.forall_iff_forall_mem]
    intro expression member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    cases retained.zipIdx.lookup index with
    | none => exact ⟨0, 0, Or.inr (by simp [zero])⟩
    | some slot => exact ⟨slot, 0, Or.inl (by simp)⟩
  have bodyBound : bVarBound (retained.length + long.length) [body] := by
    apply bVarBound_mono [body] n _ ?_ bound
    simp [long]
  have smartBound : bVarBound retained.length [smartLet long body] :=
    (bVarBound_smartLet _ long body).mpr ⟨longBound, bodyBound⟩
  have smartShape : handleOk [smartLet long body] := (handleOk_smartLet long body).mpr ⟨longShape, shape⟩
  have definition : letLet n live body = .let (retained.map Bvl.Exp.var) (smartLet long body) := by
    simp [letLet, retained, long, List.zipIdx_eq_zip_range', ← List.range_eq_range']
    rfl
  rw [definition]
  simp only [letOk, List.length_map]
  exact ⟨⟨vars, smartBound⟩, smartShape⟩

/-- Optional environment packing preserves the source handler invariant. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "handle_ok_OptionalLetLet"]
theorem handleOk_optionalLetLet (body : Bvl.Exp) (n : Nat) (live : DbVars.DbVarSet)
    (size limit : Nat) (noRaise : Bool)
    (premises : handleOk [body] ∧ bVarBound n [body]) :
    handleOk (optionalLetLet body n live size limit noRaise).1 := by
  obtain ⟨shape, bound⟩ := premises
  unfold optionalLetLet
  split
  · exact shape
  · simp only [handleOk_emptyLet]
    have packed := letLet_shape n (DbVars.dbToSet live) body bound shape
    refine ⟨packed.1, ?_⟩
    intro ys inner equal
    simpa only [equal] using packed.2

/-- A nonempty let is handler-safe exactly when its bindings and body are. -/
theorem handleOk_nonemptyLet (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (nonempty : bindings ≠ []) :
    handleOk [.let bindings body] ↔ handleOk bindings ∧ handleOk [body] := by
  cases bindings with
  | nil => contradiction
  | cons first rest => cases body <;> simp [handleOk]

/-- Wrapping a bounded, handler-safe body in the packer produces a legal
handler body for the subsequent BVL-to-BVI lowering. -/
theorem handleOk_handle_letLet {α : Type} (n : Nat) (live : Spt α) (body handler : Bvl.Exp)
    (bound : bVarBound n [body]) (bodyShape : handleOk [body]) (handlerShape : handleOk [handler]) :
    handleOk [.handle (letLet n live body) handler] := by
  have packed := letLet_shape n live body bound bodyShape
  simp only [letLet, letOk] at packed
  simp only [letLet, handleOk]
  exact ⟨packed.1.1, packed.1.2, packed.2, handlerShape⟩

mutual
/-- Every singleton generated by the handler compiler has the shape required
by the following BVL-to-BVI pass. -/
theorem compileSing_handleOk (limit env : Nat) (expression : Bvl.Exp) :
    handleOk [(compileSing limit env expression).1] := by
  cases expression with
  | var index => by_cases inside : index < env <;> simp [compileSing, inside, handleOk]
  | force location index => by_cases inside : index < env <;> simp [compileSing, inside, handleOk]
  | tick body => simpa [compileSing, handleOk] using compileSing_handleOk limit env body
  | raise body =>
    generalize run : compileSing limit env body = data
    obtain ⟨compiled, live, size, flag⟩ := data
    have shape : handleOk [compiled] := by simpa [run] using compileSing_handleOk limit env body
    have bound : bVarBound env [compiled] := by simpa [run] using compileSing_varBound limit env env body (Nat.le_refl _)
    simp only [compileSing, run]
    simpa only [optionalLetLetSing_eq] using
      handleOk_optionalLetLet _ env live (size + 1) limit false
        ⟨by simpa [handleOk] using shape, by simpa [bVarBound] using bound⟩
  | call ticks dest args =>
    generalize run : compileList limit env args = data
    obtain ⟨compiled, live, size, flag⟩ := data
    have shape : handleOk compiled := by simpa [run] using compileList_handleOk limit env args
    have bound : bVarBound env compiled := by simpa [run] using compileList_varBound limit env args env (Nat.le_refl _)
    simp only [compileSing, run]
    simpa only [optionalLetLetSing_eq] using
      handleOk_optionalLetLet _ env live (size + 1) limit false
        ⟨by simpa [handleOk] using shape, by simpa [bVarBound] using bound⟩
  | op op args =>
    generalize run : compileList limit env args = data
    obtain ⟨compiled, live, size, flag⟩ := data
    have shape : handleOk compiled := by simpa [run] using compileList_handleOk limit env args
    have bound : bVarBound env compiled := by simpa [run] using compileList_varBound limit env args env (Nat.le_refl _)
    by_cases force : op = .thunkOp .forceThunk
    · subst op
      simpa [compileSing, run, handleOk] using shape
    · rw [compileSing_op_other limit env op args force, run]
      simpa only [optionalLetLetSing_eq] using
        handleOk_optionalLetLet _ env live (size + 1) limit flag
          ⟨by simpa [handleOk] using shape, by simpa [bVarBound] using bound⟩
  | ifThenElse condition yes no =>
    generalize conditionEq : compileSing limit env condition = conditionData
    obtain ⟨compiledCondition, conditionLive, conditionSize, conditionFlag⟩ := conditionData
    generalize yesEq : compileSing limit env yes = yesData
    obtain ⟨compiledYes, yesLive, yesSize, yesFlag⟩ := yesData
    generalize noEq : compileSing limit env no = noData
    obtain ⟨compiledNo, noLive, noSize, noFlag⟩ := noData
    have conditionShape : handleOk [compiledCondition] := by simpa [conditionEq] using compileSing_handleOk limit env condition
    have yesShape : handleOk [compiledYes] := by simpa [yesEq] using compileSing_handleOk limit env yes
    have noShape : handleOk [compiledNo] := by simpa [noEq] using compileSing_handleOk limit env no
    have conditionBound : bVarBound env [compiledCondition] := by simpa [conditionEq] using compileSing_varBound limit env env condition (Nat.le_refl _)
    have yesBound : bVarBound env [compiledYes] := by simpa [yesEq] using compileSing_varBound limit env env yes (Nat.le_refl _)
    have noBound : bVarBound env [compiledNo] := by simpa [noEq] using compileSing_varBound limit env env no (Nat.le_refl _)
    simp only [compileSing, conditionEq, yesEq, noEq]
    simpa only [optionalLetLetSing_eq] using
      handleOk_optionalLetLet _ env _ _ limit _
        ⟨by simpa [handleOk] using And.intro conditionShape (And.intro yesShape noShape),
         by simpa [bVarBound] using And.intro conditionBound (And.intro yesBound noBound)⟩
  | handle body handler =>
    generalize bodyEq : compileSing limit env body = bodyData
    obtain ⟨compiledBody, bodyLive, bodySize, bodyFlag⟩ := bodyData
    have bodyShape : handleOk [compiledBody] := by simpa [bodyEq] using compileSing_handleOk limit env body
    have bodyBound : bVarBound env [compiledBody] := by simpa [bodyEq] using compileSing_varBound limit env env body (Nat.le_refl _)
    cases bodyFlag with
    | true => simpa [compileSing, bodyEq] using bodyShape
    | false =>
      generalize handlerEq : compileSing limit (env + 1) handler = handlerData
      obtain ⟨compiledHandler, handlerLive, handlerSize, handlerFlag⟩ := handlerData
      have handlerShape : handleOk [compiledHandler] := by simpa [handlerEq] using compileSing_handleOk limit (env + 1) handler
      simp only [compileSing, bodyEq, Bool.false_eq_true, ↓reduceIte, handlerEq]
      exact handleOk_handle_letLet env (DbVars.dbToSet bodyLive) compiledBody compiledHandler bodyBound bodyShape handlerShape
  | «let» bindings body =>
    cases bindings with
    | nil => simpa [compileSing] using compileSing_handleOk limit env body
    | cons first rest =>
      generalize bindingsEq : compileList limit env (first :: rest) = bindingsData
      obtain ⟨compiledBindings, bindingsLive, bindingsSize, bindingsFlag⟩ := bindingsData
      generalize bodyEq : compileSing limit (env + (first :: rest).length) body = bodyData
      obtain ⟨compiledBody, bodyLive, bodySize, bodyFlag⟩ := bodyData
      have bindingsShape : handleOk compiledBindings := by simpa [bindingsEq] using compileList_handleOk limit env (first :: rest)
      have bodyShape : handleOk [compiledBody] := by
        have h := compileSing_handleOk limit (env + (first :: rest).length) body
        rw [bodyEq] at h
        exact h
      have bindingsBound : bVarBound env compiledBindings := by simpa [bindingsEq] using compileList_varBound limit env (first :: rest) env (Nat.le_refl _)
      have length : compiledBindings.length = (first :: rest).length := by simpa [bindingsEq] using compileList_length limit env (first :: rest)
      have nonempty : compiledBindings ≠ [] := by
        intro empty
        simp [empty] at length
      have bodyBound : bVarBound (env + compiledBindings.length) [compiledBody] := by
        have h := compileSing_varBound limit (env + (first :: rest).length) (env + (first :: rest).length) body (Nat.le_refl _)
        rw [bodyEq] at h
        simpa [length] using h
      simp only [compileSing, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, bindingsEq, bodyEq]
      simpa only [optionalLetLetSing_eq] using
        handleOk_optionalLetLet _ env _ _ limit _
          ⟨(handleOk_nonemptyLet compiledBindings compiledBody nonempty).mpr ⟨bindingsShape, bodyShape⟩,
           by simpa only [bVarBound] using And.intro bindingsBound bodyBound⟩
termination_by sizeOf expression

/-- Every generated expression list satisfies the handler-shape invariant. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_handle_ok"]
theorem compileList_handleOk (limit env : Nat) (expressions : List Bvl.Exp) :
    handleOk (compile limit env expressions).1 := by
  cases expressions with
  | nil => simp [compileList, handleOk]
  | cons head tail =>
    generalize headEq : compileSing limit env head = headData
    obtain ⟨compiledHead, headLive, headSize, headFlag⟩ := headData
    generalize tailEq : compileList limit env tail = tailData
    obtain ⟨compiledTail, tailLive, tailSize, tailFlag⟩ := tailData
    have headShape : handleOk [compiledHead] := by simpa [headEq] using compileSing_handleOk limit env head
    have tailShape : handleOk compiledTail := by simpa [tailEq] using compileList_handleOk limit env tail
    simp only [compileList, headEq, tailEq]
    exact (handleOk_cons compiledHead compiledTail).mpr ⟨headShape, tailShape⟩
termination_by sizeOf expressions
end

/-- The constant-and-handler expression pipeline produces a legal handler
shape at every arity. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_exp_handle_ok"]
theorem compileExpression_handleOk (limit arity : Nat) (expression : Bvl.Exp) :
    handleOk [compileExp limit arity expression] :=
  compileSing_handleOk limit arity _

/-- Sequence splitting preserves handler shape when its continuation is
both closed and handler-safe. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_seqs_handle_ok"]
theorem compileSeqsWith_handleOk (limit : Nat) (expression : Bvl.Exp) (acc : Option Bvl.Exp)
    (accSafe : ∀ rest, acc = some rest → handleOk [rest] ∧ bVarBound 0 [rest]) :
    handleOk [compileSeqs limit expression acc] := by
  change handleOk [compileSeqsWith (fun l e => compileExpression l 0 e) limit expression acc]
  by_cases shape : ∃ first second, expression = .let [first, second] (.var 1)
  · obtain ⟨first, second, rfl⟩ := shape
    simp only [compileSeqsWith]
    apply compileSeqsWith_handleOk limit first
    intro rest equal
    cases equal
    constructor
    · exact compileSeqsWith_handleOk limit second acc accSafe
    · exact compileSeqsWith_varBound limit second acc (fun rest equal => (accSafe rest equal).2)
  · have notShape : ∀ first second, expression = .let [first, second] (.var 1) → False := by
      intro first second equal
      exact shape ⟨first, second, equal⟩
    cases acc with
    | none =>
      rw [compileSeqsWith.eq_2 _ limit expression notShape]
      exact compileExpression_handleOk limit 0 expression
    | some rest =>
      rw [compileSeqsWith.eq_3 _ limit expression rest notShape]
      obtain ⟨restShape, restBound⟩ := accSafe rest rfl
      have nested : handleOk [.let [] (.let [] rest)] := by
        rw [handleOk_emptyLet]
        simp [letOk, restBound, restShape]
      apply (handleOk_nonemptyLet [_] _ (by simp)).mpr
      exact ⟨by simpa using compileExpression_handleOk limit 0 expression, nested⟩
termination_by sizeOf expression

/-- The actual handler entry point emits a handler-safe expression in both
sequence-splitting modes. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_any_handle_ok"]
theorem compileAny_handleOk (splitSeq : Bool) (limit arity : Nat)
    (expression : Bvl.Exp) :
    handleOk [compileAny splitSeq limit arity expression] := by
  unfold compileAny
  split
  · exact compileSeqsWith_handleOk limit expression none (by simp)
  · exact compileExpression_handleOk limit arity expression

end Flapjack.Compiler.Backend.BvlHandle.Proofs
