module

public import Flapjack.Compiler.Backend.BvlHandle.Proofs.CompileCases
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.ConstantComposition
public import Flapjack.Compiler.Backend.BvlHandle.SourceCompile
public import Flapjack.Compiler.Backend.Semantics.BvlProps.VarBound

@[expose] public section

/-! Variable bounds for the handler compiler's generated expressions. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem (expsWeight expWeight)
open Flapjack.Compiler.Backend.BvlProps (bVarBound)

/-- Variable bounds are monotone in the available environment size. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "bVarBound_LESS_EQ"]
theorem bVarBound_mono (expressions : List Bvl.Exp) (n m : Nat)
    (le : n ≤ m) (bound : bVarBound n expressions) : bVarBound m expressions := by
  cases expressions with
  | nil => simp [bVarBound]
  | cons first rest =>
    cases rest with
    | cons second tail =>
      simp only [bVarBound] at bound ⊢
      exact ⟨bVarBound_mono [first] n m le bound.1,
        bVarBound_mono (second :: tail) n m le bound.2⟩
    | nil =>
      cases first with
      | var index => simp only [bVarBound] at bound ⊢; omega
      | force location index => simp only [bVarBound] at bound ⊢; omega
      | tick body => simp only [bVarBound] at bound ⊢; exact bVarBound_mono [body] n m le bound
      | raise body => simp only [bVarBound] at bound ⊢; exact bVarBound_mono [body] n m le bound
      | op operation args =>
        simp only [bVarBound] at bound ⊢
        exact bVarBound_mono args n m le bound
      | call ticks dest args =>
        simp only [bVarBound] at bound ⊢
        exact bVarBound_mono args n m le bound
      | ifThenElse condition yes no =>
        simp only [bVarBound] at bound ⊢
        exact ⟨bVarBound_mono [condition] n m le bound.1,
          bVarBound_mono [yes] n m le bound.2.1,
          bVarBound_mono [no] n m le bound.2.2⟩
      | handle body handler =>
        simp only [bVarBound] at bound ⊢
        exact ⟨bVarBound_mono [body] n m le bound.1,
          bVarBound_mono [handler] (n + 1) (m + 1) (by omega) bound.2⟩
      | «let» bindings body =>
        simp only [bVarBound] at bound ⊢
        exact ⟨bVarBound_mono bindings n m le bound.1,
          bVarBound_mono [body] (n + bindings.length) (m + bindings.length) (by omega)
            bound.2⟩
termination_by expsWeight expressions
decreasing_by
  all_goals simp_all only [expsWeight, expWeight]
  all_goals try (have := BvlSem.expWeight_pos first)
  all_goals omega

/-- A list is bounded exactly when each member is bounded individually. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "bVarBound_MEM"]
theorem bVarBound_every (n : Nat) (expressions : List Bvl.Exp) :
    bVarBound n expressions ↔ ∀ expression ∈ expressions, bVarBound n [expression] := by
  induction expressions with
  | nil => simp [bVarBound]
  | cons head tail ih =>
    cases tail with
    | nil => simp
    | cons second rest =>
      simp only [bVarBound]
      rw [ih]
      simp

/-- A smart let has the same variable-bound obligations as an ordinary let. -/
theorem bVarBound_smartLet (n : Nat) (bindings : List Bvl.Exp) (body : Bvl.Exp) :
    bVarBound n [smartLet bindings body] ↔
      bVarBound n bindings ∧ bVarBound (n + bindings.length) [body] := by
  cases bindings <;> simp [smartLet, bVarBound]

/-- The environment packer stays within any bound at least as large as
its original environment and the body's existing bound. -/
theorem bVarBound_letLet {α : Type} (n m : Nat) (live : Spt α) (body : Bvl.Exp)
    (envBound : n ≤ m) (bodyBound : bVarBound m [body]) :
    bVarBound m [letLet n live body] := by
  let retained := (List.range n).filter fun i => (sptLookup i live).isSome
  let long := (List.range n).map fun i =>
    match retained.zipIdx.lookup i with
    | some packed => Bvl.Exp.var packed
    | none => zero
  have retainedBound : bVarBound m (retained.map Bvl.Exp.var) := by
    rw [bVarBound_every]
    intro expression member
    obtain ⟨index, indexMem, rfl⟩ := List.mem_map.mp member
    have bound : index < n := by
      have rangeMem := (List.mem_filter.mp indexMem).1
      simpa [retained] using rangeMem
    simp only [bVarBound]
    omega
  have longBound : bVarBound (m + retained.length) long := by
    rw [bVarBound_every]
    intro expression member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    cases found : retained.zipIdx.lookup index with
    | none => simp [zero, bVarBound]
    | some packed =>
      have slot := lookup_zipIdx_getElem retained index packed found
      have packedBound : packed < retained.length := (List.getElem?_eq_some_iff.mp slot).1
      simp only [bVarBound]
      omega
  have enlarged : bVarBound (m + retained.length + long.length) [body] :=
    bVarBound_mono [body] m _ (by omega) bodyBound
  have inner : bVarBound (m + retained.length) [smartLet long body] :=
    (bVarBound_smartLet _ long body).mpr ⟨longBound, enlarged⟩
  have definition : letLet n live body = .let (retained.map Bvl.Exp.var) (smartLet long body) := by
    simp [letLet, retained, long, List.zipIdx_eq_zip_range', ← List.range_eq_range']
    rfl
  rw [definition, bVarBound]
  simpa using ⟨retainedBound, inner⟩

/-- The source variable-bound theorem for sparse sets of live variables. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "bVarBound_LetLet"]
theorem bVarBound_letLet_numSet (n m : Nat) (live : NumSet) (body : Bvl.Exp)
    (bodyBound : bVarBound m [body]) (envBound : n ≤ m) :
    bVarBound m [letLet n live body] :=
  bVarBound_letLet n m live body envBound bodyBound

/-- Optional environment packing preserves a bound on the source list result. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "bVarBound_OptionalLetLet"]
theorem bVarBound_optionalLetLet (body : Bvl.Exp) (n m : Nat) (live : DbVars.DbVarSet)
    (size limit : Nat) (noRaise : Bool)
    (premises : bVarBound m [body] ∧ n ≤ m) :
    bVarBound m (optionalLetLet body n live size limit noRaise).1 := by
  obtain ⟨bodyBound, envBound⟩ := premises
  unfold optionalLetLet
  split
  · exact bodyBound
  · simp only [bVarBound, List.length_nil, Nat.add_zero, true_and]
    exact bVarBound_letLet n m (DbVars.dbToSet live) body envBound bodyBound

/-- A source compiler result has the same length as its input list. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_IMP_LENGTH"]
theorem compile_imp_length (limit env : Nat) (expressions output : List Bvl.Exp)
    (live : DbVars.DbVarSet) (remainder : Nat × Bool)
    (compiled : compile limit env expressions = (output, live, remainder)) :
    output.length = expressions.length := by
  have length := compileList_length limit env expressions
  simpa [compiled] using length

mutual
/-- Every singleton emitted by the handler traversal is in scope whenever
the compilation environment fits in the requested bound. -/
theorem compileSing_varBound (limit env m : Nat) (expression : Bvl.Exp) (envBound : env ≤ m) :
    bVarBound m [(compileSing limit env expression).1] := by
  cases expression with
  | var index =>
    by_cases inside : index < env
    · simp [compileSing, inside, bVarBound]; omega
    · simp [compileSing, inside, bVarBound]
  | force location index =>
    by_cases inside : index < env
    · simp [compileSing, inside, bVarBound]; omega
    · simp [compileSing, inside, bVarBound]
  | tick body =>
    simpa [compileSing, bVarBound] using compileSing_varBound limit env m body envBound
  | raise body =>
    generalize run : compileSing limit env body = data
    obtain ⟨compiled, live, size, flag⟩ := data
    have bound : bVarBound m [compiled] := by
      simpa [run] using compileSing_varBound limit env m body envBound
    simp only [compileSing, run]
    simpa only [optionalLetLetSing_eq] using
      bVarBound_optionalLetLet _ env m live (size + 1) limit false
        ⟨by simpa [bVarBound] using bound, envBound⟩
  | call ticks dest args =>
    generalize run : compileList limit env args = data
    obtain ⟨compiled, live, size, flag⟩ := data
    have bound : bVarBound m compiled := by
      simpa [run] using compileList_varBound limit env args m envBound
    simp only [compileSing, run]
    simpa only [optionalLetLetSing_eq] using
      bVarBound_optionalLetLet _ env m live (size + 1) limit false
        ⟨by simpa [bVarBound] using bound, envBound⟩
  | op op args =>
    generalize run : compileList limit env args = data
    obtain ⟨compiled, live, size, flag⟩ := data
    have bound : bVarBound m compiled := by
      simpa [run] using compileList_varBound limit env args m envBound
    by_cases force : op = .thunkOp .forceThunk
    · subst op
      simpa [compileSing, run, bVarBound] using bound
    · rw [compileSing_op_other limit env op args force, run]
      simpa only [optionalLetLetSing_eq] using
        bVarBound_optionalLetLet _ env m live (size + 1) limit flag
          ⟨by simpa [bVarBound] using bound, envBound⟩
  | ifThenElse condition yes no =>
    generalize conditionEq : compileSing limit env condition = conditionData
    obtain ⟨compiledCondition, conditionLive, conditionSize, conditionFlag⟩ := conditionData
    generalize yesEq : compileSing limit env yes = yesData
    obtain ⟨compiledYes, yesLive, yesSize, yesFlag⟩ := yesData
    generalize noEq : compileSing limit env no = noData
    obtain ⟨compiledNo, noLive, noSize, noFlag⟩ := noData
    have conditionBound : bVarBound m [compiledCondition] := by
      simpa [conditionEq] using compileSing_varBound limit env m condition envBound
    have yesBound : bVarBound m [compiledYes] := by
      simpa [yesEq] using compileSing_varBound limit env m yes envBound
    have noBound : bVarBound m [compiledNo] := by
      simpa [noEq] using compileSing_varBound limit env m no envBound
    simp only [compileSing, conditionEq, yesEq, noEq]
    simpa only [optionalLetLetSing_eq] using
      bVarBound_optionalLetLet _ env m _ _ limit _
        ⟨by simpa [bVarBound] using And.intro conditionBound (And.intro yesBound noBound), envBound⟩
  | handle body handler =>
    generalize bodyEq : compileSing limit env body = bodyData
    obtain ⟨compiledBody, bodyLive, bodySize, bodyFlag⟩ := bodyData
    have bodyBound : bVarBound m [compiledBody] := by
      simpa [bodyEq] using compileSing_varBound limit env m body envBound
    cases bodyFlag with
    | true => simpa [compileSing, bodyEq] using bodyBound
    | false =>
      generalize handlerEq : compileSing limit (env + 1) handler = handlerData
      obtain ⟨compiledHandler, handlerLive, handlerSize, handlerFlag⟩ := handlerData
      have handlerBound : bVarBound (m + 1) [compiledHandler] := by
        simpa [handlerEq] using compileSing_varBound limit (env + 1) (m + 1) handler (by omega)
      simp only [compileSing, bodyEq, Bool.false_eq_true, ↓reduceIte, handlerEq, bVarBound]
      exact ⟨bVarBound_letLet env m (DbVars.dbToSet bodyLive) compiledBody envBound bodyBound, handlerBound⟩
  | «let» bindings body =>
    cases bindings with
    | nil => simpa [compileSing] using compileSing_varBound limit env m body envBound
    | cons first rest =>
      generalize bindingsEq : compileList limit env (first :: rest) = bindingsData
      obtain ⟨compiledBindings, bindingsLive, bindingsSize, bindingsFlag⟩ := bindingsData
      generalize bodyEq : compileSing limit (env + (first :: rest).length) body = bodyData
      obtain ⟨compiledBody, bodyLive, bodySize, bodyFlag⟩ := bodyData
      have bindingsBound : bVarBound m compiledBindings := by
        simpa [bindingsEq] using compileList_varBound limit env (first :: rest) m envBound
      have length : compiledBindings.length = (first :: rest).length := by
        simpa [bindingsEq] using compileList_length limit env (first :: rest)
      have bodyBound : bVarBound (m + compiledBindings.length) [compiledBody] := by
        have bound := compileSing_varBound limit (env + (first :: rest).length)
          (m + (first :: rest).length) body (by omega)
        rw [bodyEq] at bound
        simpa [length] using bound
      simp only [compileSing, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, bindingsEq, bodyEq]
      simpa only [optionalLetLetSing_eq] using
        bVarBound_optionalLetLet _ env m _ _ limit _
          ⟨by simpa only [bVarBound] using And.intro bindingsBound bodyBound, envBound⟩
termination_by sizeOf expression

/-- Every list emitted by the handler traversal is in scope. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "bVarBound_compile"]
theorem compileList_varBound (limit env : Nat) (expressions : List Bvl.Exp) (m : Nat) (envBound : env ≤ m) :
    bVarBound m (compile limit env expressions).1 := by
  cases expressions with
  | nil => simp [compileList, bVarBound]
  | cons head tail =>
    generalize headEq : compileSing limit env head = headData
    obtain ⟨compiledHead, headLive, headSize, headFlag⟩ := headData
    generalize tailEq : compileList limit env tail = tailData
    obtain ⟨compiledTail, tailLive, tailSize, tailFlag⟩ := tailData
    have headBound : bVarBound m [compiledHead] := by
      simpa [headEq] using compileSing_varBound limit env m head envBound
    have tailBound : bVarBound m compiledTail := by
      simpa [tailEq] using compileList_varBound limit env tail m envBound
    simp only [compileList, headEq, tailEq]
    rw [bVarBound_every] at tailBound ⊢
    intro expression member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact headBound
    · exact tailBound expression member
termination_by sizeOf expressions
end

/-- A successful source compilation result is bounded by its environment. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_IMP_bVarBound"]
theorem compile_imp_bVarBound (limit env : Nat) (expressions output : List Bvl.Exp)
    (live : DbVars.DbVarSet) (remainder : Nat × Bool)
    (compiled : compile limit env expressions = (output, live, remainder)) :
    bVarBound env output := by
  have bound := compileList_varBound limit env expressions env (Nat.le_refl _)
  simpa [compiled] using bound

/-- The complete expression pipeline emits an expression bounded by its
declared arity. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_exp_bVarBound"]
theorem compileExpression_varBound (limit arity : Nat) (expression : Bvl.Exp) :
    bVarBound arity [compileExp limit arity expression] := by
  exact compileSing_varBound limit arity arity _ (Nat.le_refl _)

/-- Sequence splitting preserves a closed variable bound for any closed
continuation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "compile_seqs_bVarBound"]
theorem compileSeqsWith_varBound (limit : Nat) (expression : Bvl.Exp) (acc : Option Bvl.Exp)
    (accBound : ∀ rest, acc = some rest → bVarBound 0 [rest]) :
    bVarBound 0 [compileSeqs limit expression acc] := by
  change bVarBound 0 [compileSeqsWith (fun l e => compileExpression l 0 e) limit expression acc]
  by_cases shape : ∃ first second, expression = .let [first, second] (.var 1)
  · obtain ⟨first, second, rfl⟩ := shape
    simp only [compileSeqsWith]
    apply compileSeqsWith_varBound limit first
    intro rest equal
    cases equal
    exact compileSeqsWith_varBound limit second acc accBound
  · have notShape : ∀ first second, expression = .let [first, second] (.var 1) → False := by
      intro first second equal
      exact shape ⟨first, second, equal⟩
    cases acc with
    | none =>
      rw [compileSeqsWith.eq_2 _ limit expression notShape]
      exact compileExpression_varBound limit 0 expression
    | some rest =>
      rw [compileSeqsWith.eq_3 _ limit expression rest notShape]
      have continuation : bVarBound 1 [rest] := bVarBound_mono [rest] 0 1 (by omega) (accBound rest rfl)
      simpa [bVarBound] using And.intro (compileExpression_varBound limit 0 expression) continuation
termination_by sizeOf expression

/-- The composed source entry point is bounded in either mode; this combines
the source expression and sequence bound theorems for Flapjack callers. -/
theorem compileAny_varBound (splitSeq : Bool) (limit arity : Nat)
    (expression : Bvl.Exp) :
    bVarBound arity [compileAny splitSeq limit arity expression] := by
  unfold compileAny
  split
  · rename_i condition
    have zero : arity = 0 := by
      simp only [Bool.and_eq_true, beq_iff_eq] at condition
      exact condition.1
    subst arity
    exact compileSeqsWith_varBound limit expression none (by simp)
  · exact compileExpression_varBound limit arity expression

end Flapjack.Compiler.Backend.BvlHandle.Proofs
