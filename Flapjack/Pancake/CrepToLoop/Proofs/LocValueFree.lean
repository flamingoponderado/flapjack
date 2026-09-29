import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.LoopLive.Fixedpoint

/-!
Flapjack-only structural facts for the runtime-only `HolLoopProg.locValue`
constructor.  This module deliberately carries no HOL tags: the predicate is
infrastructure for a future source/runtime correspondence argument, not an
HOL theorem port.
-/

namespace Flapjack

/-- A nested `HolLoopProg` contains no `locValue` constructor, including in
either program stored inside an optional call handler. -/
def holLoopProgLocValueFree {width : Nat} [NeZero width] :
    HolLoopProg width → Prop
  | .locValue _ _ => False
  | .seq first second => holLoopProgLocValueFree first ∧ holLoopProgLocValueFree second
  | .ite _ _ _ thenBranch elseBranch _ =>
      holLoopProgLocValueFree thenBranch ∧ holLoopProgLocValueFree elseBranch
  | .loop _ body _ => holLoopProgLocValueFree body
  | .mark body => holLoopProgLocValueFree body
  | .call _ _ _ none => True
  | .call _ _ _ (some (_, handler, normal, _)) =>
      holLoopProgLocValueFree handler ∧ holLoopProgLocValueFree normal
  | _ => True
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [HolLoopProg.call.sizeOf_spec]; omega)

/-- Every element of a list satisfies the nested LocValue-free predicate. -/
def holLoopProgListLocValueFree {width : Nat} [NeZero width]
    (programs : List (HolLoopProg width)) : Prop :=
  ∀ program, program ∈ programs → holLoopProgLocValueFree program

private theorem holLoopProgListLocValueFree_append {width : Nat} [NeZero width]
    (first second : List (HolLoopProg width))
    (hfirst : holLoopProgListLocValueFree first)
    (hsecond : holLoopProgListLocValueFree second) :
    holLoopProgListLocValueFree (first ++ second) := by
  intro program hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hfirst program hmem
  · exact hsecond program hmem

private theorem holLoopProgListLocValueFree_append3 {width : Nat} [NeZero width]
    (first second : List (HolLoopProg width)) (last : HolLoopProg width)
    (hfirst : holLoopProgListLocValueFree first)
    (hsecond : holLoopProgListLocValueFree second)
    (hlast : holLoopProgListLocValueFree [last]) :
    holLoopProgListLocValueFree (first ++ second ++ [last]) := by
  intro program hmem
  rcases List.mem_append.mp hmem with hprefix | hlastMem
  · rcases List.mem_append.mp hprefix with hfirstMem | hsecondMem
    · exact hfirst program hfirstMem
    · exact hsecond program hsecondMem
  · exact hlast program (by simpa using hlastMem)

private theorem loopNestedSeqHOL_preserves_locValueFree {width : Nat} [NeZero width]
    (programs : List (HolLoopProg width))
    (hfree : holLoopProgListLocValueFree programs) :
    holLoopProgLocValueFree (loopNestedSeqHOL programs) := by
  induction programs with
  | nil => simp [loopNestedSeqHOL, holLoopProgLocValueFree]
  | cons first rest ih =>
      have hfirst := hfree first (by simp)
      have hrest : holLoopProgListLocValueFree rest := by
        intro program hmem
        exact hfree program (by simp [hmem])
      simpa [loopNestedSeqHOL, holLoopProgLocValueFree] using And.intro hfirst (ih hrest)

private theorem holLoopProgListLocValueFree_zipWith {width : Nat} [NeZero width]
    {α β : Type} (f : α → β → HolLoopProg width)
    (hfree : ∀ x y, holLoopProgLocValueFree (f x y)) :
    ∀ (xs : List α) (ys : List β), holLoopProgListLocValueFree (xs.zipWith f ys)
  | [], _ => by simp [holLoopProgListLocValueFree]
  | _ :: _, [] => by simp [holLoopProgListLocValueFree]
  | x :: xs, y :: ys => by
      simp only [List.zipWith_cons_cons, holLoopProgListLocValueFree, List.mem_cons]
      intro program hmem
      rcases hmem with rfl | hmem
      · exact hfree x y
      · exact holLoopProgListLocValueFree_zipWith f hfree xs ys program hmem

private theorem compileCrepopHOLExact_codeLocValueFree {width : Nat} [NeZero width]
    (operator : CrepOp) (target : Compiler.Encoders.Asm.AsmArchitecture)
    (left right tmp : Nat)
    (live : NumSet) :
    holLoopProgListLocValueFree
      (compileCrepopHOLExact (width := width) operator target left right tmp live).1 := by
  cases operator with
  | mul =>
      by_cases htarget : target = .armv7 <;>
        simp [compileCrepopHOLExact, htarget,
          holLoopProgListLocValueFree, holLoopProgLocValueFree]

mutual
private theorem compileExpHOLExact_codeLocValueFree {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∀ expression : CrepExpHOL width,
      holLoopProgListLocValueFree (compileExpHOLExact context tmp live expression).1
  | .baseAddr => by simp [compileExpHOLExact, holLoopProgListLocValueFree]
  | .topAddr => by simp [compileExpHOLExact, holLoopProgListLocValueFree]
  | .const _ => by simp [compileExpHOLExact, holLoopProgListLocValueFree]
  | .var _ => by simp [compileExpHOLExact, holLoopProgListLocValueFree]
  | .load address => by
      have ih := compileExpHOLExact_codeLocValueFree context tmp live address
      rcases hA : compileExpHOLExact context tmp live address with ⟨code, value, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact ih
  | .load32 address => by
      have ih := compileExpHOLExact_codeLocValueFree context tmp live address
      rcases hA : compileExpHOLExact context tmp live address with ⟨code, value, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact holLoopProgListLocValueFree_append code _ ih (by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree])
  | .loadByte address => by
      have ih := compileExpHOLExact_codeLocValueFree context tmp live address
      rcases hA : compileExpHOLExact context tmp live address with ⟨code, value, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact holLoopProgListLocValueFree_append code _ ih (by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree])
  | .loadGlob _ => by simp [compileExpHOLExact, holLoopProgListLocValueFree]
  | .op operator expressions => by
      have ih := compileExpsHOLExact_codeLocValueFree context tmp live expressions
      rcases hA : compileExpsHOLExact context tmp live expressions with
        ⟨code, values, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact ih
  | .crepOp operator expressions => by
      have ih := compileExpsHOLExact_codeLocValueFree context tmp live expressions
      rcases hA : compileExpsHOLExact context tmp live expressions with
        ⟨code, values, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      rcases hC : compileCrepopHOLExact (width := width) operator context.target next (next + 1)
          (next + values.length)
          (sptListInsert ((List.range values.length).map (fun offset => next + offset)) outLive)
          with ⟨operationCode, destination⟩
      simp only [compileExpHOLExact, hA, hC]
      have hAssigned : holLoopProgListLocValueFree
          ((List.range values.length).zipWith
            (fun offset value => HolLoopProg.assign (next + offset) value) values) :=
        holLoopProgListLocValueFree_zipWith _
          (fun _ _ => by simp [holLoopProgLocValueFree]) _ _
      have hPrefix := holLoopProgListLocValueFree_append code _ ih hAssigned
      have hOperation : holLoopProgListLocValueFree operationCode := by
        have h := compileCrepopHOLExact_codeLocValueFree (width := width) operator context.target next
          (next + 1) (next + values.length)
          (sptListInsert ((List.range values.length).map (fun offset => next + offset)) outLive)
        rw [hC] at h
        exact h
      exact holLoopProgListLocValueFree_append _ operationCode hPrefix hOperation
  | .cmp operator left right => by
      have ihLeft := compileExpHOLExact_codeLocValueFree context tmp live left
      rcases hA : compileExpHOLExact context tmp live left with
        ⟨leftCode, leftValue, leftNext, leftLive⟩
      rw [hA] at ihLeft
      simp only at ihLeft
      have ihRight := compileExpHOLExact_codeLocValueFree context leftNext leftLive right
      rcases hB : compileExpHOLExact context leftNext leftLive right with
        ⟨rightCode, rightValue, rightNext, rightLive⟩
      rw [hB] at ihRight
      simp only at ihRight
      simp only [compileExpHOLExact, hA, hB, progIfHOLExact]
      have htail : holLoopProgListLocValueFree
          [.assign (rightNext + 1) leftValue,
           .assign (rightNext + 2) rightValue,
           .ite operator (rightNext + 1) (.reg (rightNext + 2))
             (.assign (rightNext + 1) (.const 1))
             (.assign (rightNext + 1) (.const 0))
             (sptListInsert [rightNext + 1, rightNext + 2] rightLive)] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree]
      exact holLoopProgListLocValueFree_append (leftCode ++ rightCode) _
        (holLoopProgListLocValueFree_append leftCode rightCode ihLeft ihRight) htail
  | .shift operator left right => by
      have ihLeft := compileExpHOLExact_codeLocValueFree context tmp live left
      rcases hA : compileExpHOLExact context tmp live left with
        ⟨leftCode, leftValue, leftNext, leftLive⟩
      rw [hA] at ihLeft
      simp only at ihLeft
      have ihRight := compileExpHOLExact_codeLocValueFree context leftNext leftLive right
      rcases hB : compileExpHOLExact context leftNext leftLive right with
        ⟨rightCode, rightValue, rightNext, rightLive⟩
      rw [hB] at ihRight
      simp only at ihRight
      simp only [compileExpHOLExact, hA, hB]
      exact holLoopProgListLocValueFree_append leftCode rightCode ihLeft ihRight
  termination_by expression => sizeOf expression

private theorem compileExpsHOLExact_codeLocValueFree {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∀ expressions : List (CrepExpHOL width),
      holLoopProgListLocValueFree (compileExpsHOLExact context tmp live expressions).1
  | [] => by simp [compileExpsHOLExact, holLoopProgListLocValueFree]
  | expression :: expressions => by
      have ihExpression :=
        compileExpHOLExact_codeLocValueFree context tmp live expression
      rcases hA : compileExpHOLExact context tmp live expression with
        ⟨code, value, next, outLive⟩
      rw [hA] at ihExpression
      simp only at ihExpression
      have ihTail := compileExpsHOLExact_codeLocValueFree context next outLive expressions
      rcases hB : compileExpsHOLExact context next outLive expressions with
        ⟨tailCode, tailValues, finalTemp, finalLive⟩
      rw [hB] at ihTail
      simp only at ihTail
      simp only [compileExpsHOLExact, hA, hB]
      exact holLoopProgListLocValueFree_append code tailCode ihExpression ihTail
  termination_by expressions => sizeOf expressions
end

private theorem compileHOLExact_locValueFree {width : Nat} [NeZero width] :
    ∀ (context : CrepToLoopContextExact) (live : NumSet)
      (program : CrepProgHOL width),
      holLoopProgLocValueFree (compileHOLExact context live program)
  | context, live, .skip => by simp [compileHOLExact, holLoopProgLocValueFree]
  | context, live, .break _ => by simp [compileHOLExact, holLoopProgLocValueFree]
  | context, live, .continue _ => by simp [compileHOLExact, holLoopProgLocValueFree]
  | context, live, .tick => by simp [compileHOLExact, holLoopProgLocValueFree]
  | context, live, .raise exception => by
      simp [compileHOLExact, holLoopProgLocValueFree]
  | context, live, .shMem operator name address => by
      cases hname : context.vars.lookup name with
      | none => simp [compileHOLExact, hname, holLoopProgLocValueFree]
      | some mappedName =>
          rcases hA : compileExpHOLExact context (context.vmax + 1) live address with
            ⟨code, compiledAddress, next, outLive⟩
          have hcode := compileExpHOLExact_codeLocValueFree context
            (context.vmax + 1) live address
          rw [hA] at hcode
          simp only at hcode
          simp only [compileHOLExact, hname, hA]
          apply loopNestedSeqHOL_preserves_locValueFree
          exact holLoopProgListLocValueFree_append code _ hcode (by
            simp [holLoopProgListLocValueFree, holLoopProgLocValueFree])
  | context, live, .store destination source => by
      rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
        ⟨destinationCode, address, nextTemporary, nextLive⟩
      rcases hS : compileExpHOLExact context nextTemporary nextLive source with
        ⟨sourceCode, value, finalTemporary, finalLive⟩
      have hDfree := compileExpHOLExact_codeLocValueFree context
        (context.vmax + 1) live destination
      have hSfree := compileExpHOLExact_codeLocValueFree context
        nextTemporary nextLive source
      rw [hD] at hDfree
      rw [hS] at hSfree
      simp only at hDfree hSfree
      simp only [compileHOLExact, hD, hS]
      apply loopNestedSeqHOL_preserves_locValueFree
      have htail : holLoopProgListLocValueFree
          [.assign finalTemporary value, .store address finalTemporary] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree]
      apply holLoopProgListLocValueFree_append
        (destinationCode ++ sourceCode) _
        (holLoopProgListLocValueFree_append destinationCode sourceCode hDfree hSfree)
      exact htail
  | context, live, .store32 destination source => by
      rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
        ⟨destinationCode, address, nextTemporary, nextLive⟩
      rcases hS : compileExpHOLExact context nextTemporary nextLive source with
        ⟨sourceCode, value, finalTemporary, finalLive⟩
      have hDfree := compileExpHOLExact_codeLocValueFree context
        (context.vmax + 1) live destination
      have hSfree := compileExpHOLExact_codeLocValueFree context
        nextTemporary nextLive source
      rw [hD] at hDfree
      rw [hS] at hSfree
      simp only at hDfree hSfree
      simp only [compileHOLExact, hD, hS]
      apply loopNestedSeqHOL_preserves_locValueFree
      have htail : holLoopProgListLocValueFree
          [.assign finalTemporary address, .assign (finalTemporary + 1) value,
           .store32 finalTemporary (finalTemporary + 1)] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree]
      apply holLoopProgListLocValueFree_append
        (destinationCode ++ sourceCode) _
        (holLoopProgListLocValueFree_append destinationCode sourceCode hDfree hSfree)
      exact htail
  | context, live, .storeByte destination source => by
      rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
        ⟨destinationCode, address, nextTemporary, nextLive⟩
      rcases hS : compileExpHOLExact context nextTemporary nextLive source with
        ⟨sourceCode, value, finalTemporary, finalLive⟩
      have hDfree := compileExpHOLExact_codeLocValueFree context
        (context.vmax + 1) live destination
      have hSfree := compileExpHOLExact_codeLocValueFree context
        nextTemporary nextLive source
      rw [hD] at hDfree
      rw [hS] at hSfree
      simp only at hDfree hSfree
      simp only [compileHOLExact, hD, hS]
      apply loopNestedSeqHOL_preserves_locValueFree
      have htail : holLoopProgListLocValueFree
          [.assign finalTemporary address, .assign (finalTemporary + 1) value,
           .storeByte finalTemporary (finalTemporary + 1)] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree]
      apply holLoopProgListLocValueFree_append
        (destinationCode ++ sourceCode) _
        (holLoopProgListLocValueFree_append destinationCode sourceCode hDfree hSfree)
      exact htail
  | context, live, .storeGlob address value => by
      rcases hA : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, compiledValue, next, outLive⟩
      have hcode := compileExpHOLExact_codeLocValueFree context
        (context.vmax + 1) live value
      rw [hA] at hcode
      simp only at hcode
      simp only [compileHOLExact, hA]
      apply loopNestedSeqHOL_preserves_locValueFree
      exact holLoopProgListLocValueFree_append code _ hcode (by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree])
  | context, live, .seq first second => by
      simp only [compileHOLExact, holLoopProgLocValueFree]
      exact ⟨compileHOLExact_locValueFree context live first,
        compileHOLExact_locValueFree context live second⟩
  | context, live, .ite condition thenBranch elseBranch => by
      rcases hC : compileExpHOLExact context (context.vmax + 1) live condition with
        ⟨conditionCode, compiledCondition, temporary, outLive⟩
      have hcode := compileExpHOLExact_codeLocValueFree context
        (context.vmax + 1) live condition
      rw [hC] at hcode
      simp only at hcode
      have hthen := compileHOLExact_locValueFree context live thenBranch
      have helse := compileHOLExact_locValueFree context live elseBranch
      simp only [compileHOLExact, hC]
      apply loopNestedSeqHOL_preserves_locValueFree
      have htail : holLoopProgListLocValueFree
          [.assign temporary compiledCondition,
           .ite .notEqual temporary (.imm (0 : BitVec width))
             (compileHOLExact context live thenBranch)
             (compileHOLExact context live elseBranch) live] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree, hthen, helse]
      exact holLoopProgListLocValueFree_append conditionCode _ hcode htail
  | context, live, .while condition body => by
      rcases hC : compileExpHOLExact context (context.vmax + 1) live condition with
        ⟨conditionCode, compiledCondition, temporary, outLive⟩
      have hcode := compileExpHOLExact_codeLocValueFree context
        (context.vmax + 1) live condition
      rw [hC] at hcode
      simp only at hcode
      have hbody := compileHOLExact_locValueFree context live body
      simp only [compileHOLExact, hC, holLoopProgLocValueFree]
      apply loopNestedSeqHOL_preserves_locValueFree
      have htail : holLoopProgListLocValueFree
          [.assign temporary compiledCondition,
           .ite .notEqual temporary (.imm (0 : BitVec width))
             (.seq (compileHOLExact context live body) (.continue 0)) (.break 0) live] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree, hbody]
      exact holLoopProgListLocValueFree_append conditionCode _ hcode htail
  | context, live, .assign name value => by
      cases hname : context.vars.lookup name with
      | none => simp [compileHOLExact, hname, holLoopProgLocValueFree]
      | some mappedName =>
          rcases hA : compileExpHOLExact context (context.vmax + 1) live value with
            ⟨code, compiledValue, next, outLive⟩
          have hcode := compileExpHOLExact_codeLocValueFree context
            (context.vmax + 1) live value
          rw [hA] at hcode
          simp only at hcode
          simp only [compileHOLExact, hname, hA]
          apply loopNestedSeqHOL_preserves_locValueFree
          exact holLoopProgListLocValueFree_append code _ hcode (by
            simp [holLoopProgListLocValueFree, holLoopProgLocValueFree])
  | context, live, .primitive destinations operator arguments => by
      cases hDest : destinations.mapM context.vars.lookup <;>
        cases hArgs : arguments.mapM context.vars.lookup <;>
          simp [compileHOLExact, hDest, hArgs, holLoopProgLocValueFree]
  | context, live, .dec name value body => by
      rcases hA : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, compiledValue, temporary, outLive⟩
      have hcode := compileExpHOLExact_codeLocValueFree context
        (context.vmax + 1) live value
      rw [hA] at hcode
      simp only at hcode
      let bodyContext :=
        { context with vars := context.vars.updateEq (name, temporary), vmax := temporary }
      let bodyLive := sptInsert temporary () live
      have hbody := compileHOLExact_locValueFree bodyContext bodyLive body
      simp only [compileHOLExact, hA, holLoopProgLocValueFree]
      exact ⟨loopNestedSeqHOL_preserves_locValueFree code hcode, True.intro, hbody⟩
  | context, live, .call none name arguments => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live arguments with
        ⟨code, values, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeLocValueFree context
        (context.vmax + 1) live arguments
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := holLoopProgListLocValueFree_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [holLoopProgLocValueFree])
        (genTemps nextTemporary values.length) values
      have hCall : holLoopProgListLocValueFree
          [HolLoopProg.call (width := width) none (some (findLabExact context name))
            (genTemps nextTemporary values.length) none] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree]
      simp only [compileHOLExact, hA]
      apply loopNestedSeqHOL_preserves_locValueFree
      exact holLoopProgListLocValueFree_append3 code
        (List.zipWith HolLoopProg.assign (genTemps nextTemporary values.length) values)
        (HolLoopProg.call none (some (findLabExact context name))
          (genTemps nextTemporary values.length) none)
        hcode hAssignments hCall
  | context, live, .call (some (returns, none)) name arguments => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live arguments with
        ⟨code, values, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeLocValueFree context
        (context.vmax + 1) live arguments
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := holLoopProgListLocValueFree_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [holLoopProgLocValueFree])
        (genTemps nextTemporary values.length) values
      have hCall : holLoopProgListLocValueFree
          [HolLoopProg.call (width := width)
            (some ((match returns.mapM context.vars.lookup with
              | none => [context.vmax + 2]
              | some names => names), live))
            (some (findLabExact context name)) (genTemps nextTemporary values.length)
            (some (context.vmax + 1, .raise (context.vmax + 1), .skip, live))] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree]
      rw [compileHOLExact]
      simp only [hA]
      apply loopNestedSeqHOL_preserves_locValueFree
      exact holLoopProgListLocValueFree_append3 code
        (List.zipWith HolLoopProg.assign (genTemps nextTemporary values.length) values)
        (HolLoopProg.call
          (some ((match returns.mapM context.vars.lookup with
            | none => [context.vmax + 2]
            | some names => names), live))
          (some (findLabExact context name)) (genTemps nextTemporary values.length)
          (some (context.vmax + 1, .raise (context.vmax + 1), .skip, live)))
        hcode hAssignments hCall
  | context, live, .call (some (returns, some (exception, handler))) name arguments => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live arguments with
        ⟨code, values, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeLocValueFree context
        (context.vmax + 1) live arguments
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := holLoopProgListLocValueFree_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [holLoopProgLocValueFree])
        (genTemps nextTemporary values.length) values
      have hhandler := compileHOLExact_locValueFree context live handler
      have hCall : holLoopProgListLocValueFree
          [HolLoopProg.call (width := width)
            (some ((match returns.mapM context.vars.lookup with
              | none => [context.vmax + 2]
              | some names => names), live))
            (some (findLabExact context name)) (genTemps nextTemporary values.length)
            (some (context.vmax + 1,
              .ite .notEqual (context.vmax + 1) (.imm exception) (.raise (context.vmax + 1))
                (.seq .tick (compileHOLExact context live handler)) live,
              .skip, live))] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree, hhandler]
      rw [compileHOLExact]
      simp only [hA]
      apply loopNestedSeqHOL_preserves_locValueFree
      exact holLoopProgListLocValueFree_append3 code
        (List.zipWith HolLoopProg.assign (genTemps nextTemporary values.length) values)
        (HolLoopProg.call
          (some ((match returns.mapM context.vars.lookup with
            | none => [context.vmax + 2]
            | some names => names), live))
          (some (findLabExact context name)) (genTemps nextTemporary values.length)
          (some (context.vmax + 1,
            .ite .notEqual (context.vmax + 1) (.imm exception)
              (.raise (context.vmax + 1)) (.seq .tick (compileHOLExact context live handler)) live,
            .skip, live)))
        hcode hAssignments hCall
  | context, live, .extCall function configuration configurationLength array arrayLength => by
      rw [compileHOLExact]
      split <;> simp [holLoopProgLocValueFree]
  | context, live, .return values => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live values with
        ⟨code, compiledValues, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeLocValueFree context
        (context.vmax + 1) live values
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := holLoopProgListLocValueFree_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [holLoopProgLocValueFree])
        (genTemps nextTemporary compiledValues.length) compiledValues
      have hReturn : holLoopProgListLocValueFree
          [HolLoopProg.return (width := width)
            (genTemps nextTemporary compiledValues.length)] := by
        simp [holLoopProgListLocValueFree, holLoopProgLocValueFree]
      unfold compileHOLExact
      simp only [hA]
      apply loopNestedSeqHOL_preserves_locValueFree
      exact holLoopProgListLocValueFree_append3 code
        (List.zipWith HolLoopProg.assign
          (genTemps nextTemporary compiledValues.length) compiledValues)
        (HolLoopProg.return (width := width)
          (genTemps nextTemporary compiledValues.length))
        hcode hAssignments hReturn
termination_by _ _ program => sizeOf program
decreasing_by
  all_goals simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepProgHOL.dec.sizeOf_spec, CrepProgHOL.seq.sizeOf_spec,
        CrepProgHOL.ite.sizeOf_spec, CrepProgHOL.while.sizeOf_spec,
        CrepProgHOL.call.sizeOf_spec]; omega)

/-- The exact loop-call optimizer does not introduce `locValue` into a
program that was recursively free of it.  The live-set parameter is
generalized so the `Seq` case can use the second induction hypothesis at the
live set returned by compiling the first child. -/
theorem loopCallCompHOL_preserves_locValueFree {width : Nat} [NeZero width]
    (program : HolLoopProg width) (live : Spt Nat)
    (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (loopCallCompHOL live program).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    ∀ live, holLoopProgLocValueFree p →
      holLoopProgLocValueFree (loopCallCompHOL live p).1
  let mPair : HolLoopProg width × NumSet → Prop := fun _ => True
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop := fun _ => True
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop := fun _ => True
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop :=
    fun _ => True
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_2 =>
      intro name value live
      intro hfree
      cases value with
      | var m => simp [loopCallCompHOL.eq_5, holLoopProgLocValueFree]
      | const value => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | lookup address => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | load address => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | op operator args => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | shift operator left right => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | baseAddr => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
      | topAddr => simp [loopCallCompHOL.eq_6, holLoopProgLocValueFree]
    case refine_4 =>
      intro operation live
      intro hfree
      cases operation with
      | longMul => simp [loopCallCompHOL.eq_19, holLoopProgLocValueFree]
      | longDiv => simp [loopCallCompHOL.eq_20, holLoopProgLocValueFree]
      | div => simp [loopCallCompHOL.eq_21, holLoopProgLocValueFree]
    case refine_23 =>
      intro returns target arguments handler ih live hfree
      cases handler with
      | none =>
          cases target with
          | some target => simp [loopCallCompHOL.eq_2, holLoopProgLocValueFree]
          | none =>
              cases hlast : arguments.getLast? with
              | none =>
                  simp [loopCallCompHOL.eq_3, hlast, holLoopProgLocValueFree]
              | some last =>
                  cases hlookup : sptLookup last live <;>
                    simp [loopCallCompHOL.eq_3, hlast, hlookup,
                      holLoopProgLocValueFree]
      | some entry =>
          rcases entry with ⟨exception, handler, normal, liveOut⟩
          simp only [holLoopProgLocValueFree] at hfree
          cases target with
          | some target =>
              simpa [loopCallCompHOL.eq_2, holLoopProgLocValueFree] using hfree
          | none =>
              cases hlast : arguments.getLast? with
              | none =>
                  simp [loopCallCompHOL.eq_3, hlast, holLoopProgLocValueFree]
              | some last =>
                  cases hlookup : sptLookup last live <;>
                    simp [loopCallCompHOL.eq_3, hlast, hlookup,
                      holLoopProgLocValueFree, hfree]
    all_goals simp_all [mProg, mPair, mTriple, mQuad, mHandler,
      holLoopProgLocValueFree, loopCallCompHOL.eq_1, loopCallCompHOL.eq_2,
      loopCallCompHOL.eq_3, loopCallCompHOL.eq_4, loopCallCompHOL.eq_5,
      loopCallCompHOL.eq_6, loopCallCompHOL.eq_7, loopCallCompHOL.eq_8,
      loopCallCompHOL.eq_9, loopCallCompHOL.eq_10, loopCallCompHOL.eq_11,
      loopCallCompHOL.eq_12, loopCallCompHOL.eq_13, loopCallCompHOL.eq_14,
      loopCallCompHOL.eq_15, loopCallCompHOL.eq_16, loopCallCompHOL.eq_17,
      loopCallCompHOL.eq_18, loopCallCompHOL.eq_19, loopCallCompHOL.eq_20,
      loopCallCompHOL.eq_21, loopCallCompHOL.eq_22]
  exact hgeneral live hfree

/-- `shrinkHOL` cannot introduce the runtime-only `locValue` constructor.
This is Flapjack-specific infrastructure: it supplies the optimizer half of
the parser-routed compile-path invariant and is not an additional HOL result.
The loop branch uses the reviewed `fixedpoint_thm` equation to reduce a
successful fixedpoint result to one structural `shrinkHOL` call on its body. -/
theorem shrinkHOL_preserves_locValueFree {width : Nat} [NeZero width]
    (program : HolLoopProg width) (live : NumSet)
    (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (shrinkHOL [] program live).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    ∀ lt live, holLoopProgLocValueFree p →
      holLoopProgLocValueFree (shrinkHOL lt p live).1
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_2 =>
      intro name value lt live hfree
      simp only [shrinkHOL.eq_15]
      cases hlookup : sptLookup name live <;>
        simp [holLoopProgLocValueFree]
    case refine_12 =>
      intro operator condition right thenBranch elseBranch branchLive
        ihThen ihElse lt live hfree
      simp only [holLoopProgLocValueFree] at hfree
      rcases hfree with ⟨hthen, helse⟩
      cases right with
      | reg r =>
          simp only [shrinkHOL.eq_3]
          rcases hsThen : shrinkHOL lt thenBranch (sptInter live branchLive) with
            ⟨then', liveThen⟩
          rcases hsElse : shrinkHOL lt elseBranch (sptInter live branchLive) with
            ⟨else', liveElse⟩
          have hthenFree := ihThen lt (sptInter live branchLive) hthen
          have helseFree := ihElse lt (sptInter live branchLive) helse
          rw [hsThen] at hthenFree
          rw [hsElse] at helseFree
          simp only [holLoopProgLocValueFree]
          exact ⟨hthenFree, helseFree⟩
      | imm value =>
          simp only [shrinkHOL.eq_4]
          rcases hsThen : shrinkHOL lt thenBranch (sptInter live branchLive) with
            ⟨then', liveThen⟩
          rcases hsElse : shrinkHOL lt elseBranch (sptInter live branchLive) with
            ⟨else', liveElse⟩
          have hthenFree := ihThen lt (sptInter live branchLive) hthen
          have helseFree := ihElse lt (sptInter live branchLive) helse
          rw [hsThen] at hthenFree
          rw [hsElse] at helseFree
          simp only [holLoopProgLocValueFree]
          exact ⟨hthenFree, helseFree⟩
    case refine_13 =>
      intro liveIn body liveOut ihBody lt live hfree
      simp only [shrinkHOL.eq_2]
      have hfreeBody : holLoopProgLocValueFree body := by
        simpa [holLoopProgLocValueFree] using hfree
      cases hfp : fixedpointHOL lt liveIn .ln
          (sptUnion liveIn (sptInter liveOut live)) body with
      | none =>
          have hbody := ihBody ((liveIn, sptInter liveOut live) :: lt)
            (sptUnion liveIn (sptInter liveOut live)) hfreeBody
          simp only [holLoopProgLocValueFree]
          exact hbody
      | some result =>
          rcases result with ⟨body', liveBody⟩
          have hfixed := fixedpoint_thm lt liveIn .ln
            (sptUnion liveIn (sptInter liveOut live)) body liveBody body' hfp
          have hfreeBody' : holLoopProgLocValueFree body' := by
            have h := ihBody
              ((sptInter liveIn liveBody, sptUnion liveIn (sptInter liveOut live)) :: lt)
              (sptUnion liveIn (sptInter liveOut live)) hfreeBody
            rw [hfixed] at h
            exact h
          simp only [holLoopProgLocValueFree]
          exact hfreeBody'
    case refine_23 =>
      intro returns target arguments handler hHandler lt live hfree
      cases returns with
      | none => simp only [shrinkHOL.eq_19, holLoopProgLocValueFree]
      | some returnData =>
          rcases returnData with ⟨returnNames, returnLive⟩
          cases handler with
          | none => simp only [shrinkHOL.eq_20, holLoopProgLocValueFree]
          | some entry =>
              rcases entry with ⟨exception, handler, normal, liveOut⟩
              rw [shrinkHOL.eq_21]
              rcases hHandler with ⟨ihHandler, ihNormal⟩
              simp only [holLoopProgLocValueFree] at hfree
              rcases hfree with ⟨hHandlerFree, hNormalFree⟩
              rcases hsNormal : shrinkHOL lt normal live with ⟨normal', liveNormal⟩
              rcases hsHandler : shrinkHOL lt handler live with ⟨handler', liveHandler⟩
              have hNormal' := ihNormal lt live hNormalFree
              have hHandler' := ihHandler lt live hHandlerFree
              rw [hsNormal] at hNormal'
              rw [hsHandler] at hHandler'
              simp only [holLoopProgLocValueFree]
              exact ⟨hHandler', hNormal'⟩
    all_goals
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        holLoopProgLocValueFree, shrinkHOL, shrinkHOL.eq_1, shrinkHOL.eq_2,
        shrinkHOL.eq_3, shrinkHOL.eq_4, shrinkHOL.eq_5, shrinkHOL.eq_6,
        shrinkHOL.eq_7, shrinkHOL.eq_8, shrinkHOL.eq_9, shrinkHOL.eq_10,
        shrinkHOL.eq_11, shrinkHOL.eq_12, shrinkHOL.eq_13, shrinkHOL.eq_14,
        shrinkHOL.eq_15, shrinkHOL.eq_16, shrinkHOL.eq_17, shrinkHOL.eq_18,
        shrinkHOL.eq_19, shrinkHOL.eq_20, shrinkHOL.eq_21, shrinkHOL.eq_22,
        shrinkHOL.eq_23, shrinkHOL.eq_24, shrinkHOL.eq_25, shrinkHOL.eq_26,
        shrinkHOL.eq_27]
  exact hgeneral [] live hfree

/-- `markAllHOL` preserves the Flapjack-only recursive absence of `locValue`,
including in both programs stored by a call handler. This is infrastructure
for the parser-routed compile-path invariant, not an additional HOL result. -/
theorem markAllHOL_preserves_locValueFree {width : Nat} [NeZero width]
    (program : HolLoopProg width)
    (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (markAllHOL program).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    holLoopProgLocValueFree p →
      holLoopProgLocValueFree (markAllHOL p).1
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_11 =>
      intro first second ihFirst ihSecond hfree
      simp only [holLoopProgLocValueFree] at hfree
      rcases hfree with ⟨hFirst, hSecond⟩
      have hFirst' := ihFirst hFirst
      have hSecond' := ihSecond hSecond
      simp only [markAllHOL]
      cases hmarkFirst : markAllHOL first with
      | mk first' firstMarked =>
              cases hmarkSecond : markAllHOL second with
              | mk second' secondMarked =>
              rw [hmarkFirst] at hFirst'
              rw [hmarkSecond] at hSecond'
              cases firstMarked <;> cases secondMarked <;>
                simp [holLoopProgLocValueFree, hFirst', hSecond']
    case refine_12 =>
      intro operator condition right thenBranch elseBranch branchLive ihThen ihElse hfree
      simp only [holLoopProgLocValueFree] at hfree
      rcases hfree with ⟨hthen, helse⟩
      have hthen' := ihThen hthen
      have helse' := ihElse helse
      simp only [markAllHOL]
      cases hmarkThen : markAllHOL thenBranch with
      | mk then' thenMarked =>
          cases hmarkElse : markAllHOL elseBranch with
          | mk else' elseMarked =>
              rw [hmarkThen] at hthen'
              rw [hmarkElse] at helse'
              cases thenMarked <;> cases elseMarked <;>
                simp [holLoopProgLocValueFree, hthen', helse']
    case refine_23 =>
      intro returns target arguments handler hHandler hfree
      cases handler with
      | none => simp only [markAllHOL, holLoopProgLocValueFree]
      | some entry =>
          rcases entry with ⟨exception, handler, normal, liveOut⟩
          rcases hHandler with ⟨ihHandler, ihNormal⟩
          simp only [holLoopProgLocValueFree] at hfree
          rcases hfree with ⟨hHandlerFree, hNormalFree⟩
          have hHandler' := ihHandler hHandlerFree
          have hNormal' := ihNormal hNormalFree
          simp only [markAllHOL]
          cases hmarkHandler : markAllHOL handler with
          | mk handler' handlerMarked =>
              cases hmarkNormal : markAllHOL normal with
              | mk normal' normalMarked =>
                  rw [hmarkHandler] at hHandler'
                  rw [hmarkNormal] at hNormal'
                  cases handlerMarked <;> cases normalMarked <;>
          simp [holLoopProgLocValueFree, hHandler', hNormal']
    all_goals
      intros
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        holLoopProgLocValueFree, markAllHOL]
  exact hgeneral hfree

private theorem compHOL_preserves_locValueFree {width : Nat} [NeZero width]
    (program : HolLoopProg width) (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (compHOL program) := by
  exact markAllHOL_preserves_locValueFree _
    (shrinkHOL_preserves_locValueFree program .ln hfree)

private theorem optimiseHOL_preserves_locValueFree {width : Nat} [NeZero width]
    (program : HolLoopProg width) (hfree : holLoopProgLocValueFree program) :
    holLoopProgLocValueFree (optimiseHOL program) := by
  apply compHOL_preserves_locValueFree
  exact loopCallCompHOL_preserves_locValueFree program .ln hfree

/-- Every body row emitted by the exact, parser-oriented `compileProgHOLExact`
entry point contains no recursive `locValue`. This is Flapjack-only path
infrastructure, not an additional HOL result. The proof covers all constructors
of `compileHOLExact`, including nested call handlers, then the exact `optimiseHOL`
composition; the list theorem covers the `MAP2`/truncate boundary. The canonical
projection to executable `LoopProg` is structural and leaves the forbidden
constructor explicit, so the free-output fact is established before projection
and does not rely on projection to erase it. `holLoopProgToExecutable_preserves_locValueFree`
and the production adapter's `rebaseHOLFunctionLabels_preserves_locValueFree`
cover the projection and label-rebase boundaries used by `Pipeline.lean`. -/
theorem compileProgHOLExact_bodiesLocValueFree {width : Nat} [NeZero width]
    (target : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (program : List
      (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width)) :
    holLoopProgListLocValueFree
      ((compileProgHOLExact target program).map (fun entry => entry.2.2)) := by
  let functionNames := (List.range program.length).map (fun n => n + firstLoopName)
  let compileFunction :=
    compFuncHOLExact (width := width) target
      (crepToLoopMakeFuncsExactExecutable program)
  have hRows : holLoopProgListLocValueFree
      (List.zipWith
        (fun _ entry =>
          optimiseHOL (compileFunction entry.2.1 (crepSimpProgHOL entry.2.2)))
        functionNames program) := by
    apply holLoopProgListLocValueFree_zipWith
    intro _ entry
    apply optimiseHOL_preserves_locValueFree
    exact compileHOLExact_locValueFree
      (mkCtxtExact target (makeVmapExact entry.2.1)
        (crepToLoopMakeFuncsExactExecutable program) (entry.2.1.length - 1))
      (listToNumSetHOLExact (List.range entry.2.1.length))
      (crepSimpProgHOL entry.2.2)
  simpa [compileProgHOLExact, functionNames, compileFunction,
    compFuncHOLExact, List.map_zipWith] using hRows

/-- Membership-oriented form of `compileProgHOLExact_bodiesLocValueFree` for
callers inspecting one exact compiler row. -/
theorem compileProgHOLExact_rowLocValueFree {width : Nat} [NeZero width]
    (target : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (program : List
      (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
    (entry : Nat × List Nat × HolLoopProg width)
    (hentry : entry ∈ compileProgHOLExact target program) :
    holLoopProgLocValueFree entry.2.2 := by
  have hmem : entry.2.2 ∈ (compileProgHOLExact target program).map (fun row => row.2.2) :=
    List.mem_map.mpr ⟨entry, hentry, rfl⟩
  exact compileProgHOLExact_bodiesLocValueFree target program _ hmem

/-- The executable Loop carrier has no nested `locValue` constructor. -/
def loopProgLocValueFree {width : Nat} : LoopProg (BitVec width) → Prop
  | .locValue _ _ => False
  | .seq first second => loopProgLocValueFree first ∧ loopProgLocValueFree second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopProgLocValueFree thenBranch ∧ loopProgLocValueFree elseBranch
  | .loop _ body _ => loopProgLocValueFree body
  | .mark body => loopProgLocValueFree body
  | .call _ _ _ none => True
  | .call _ _ _ (some (_, handler, normal, _)) =>
      loopProgLocValueFree handler ∧ loopProgLocValueFree normal
  | _ => True
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [LoopProg.call.sizeOf_spec]; omega)

/-- Structural exact-to-executable projection preserves recursive absence of
`locValue`. In particular, the projection does not make a generated
`locValue` disappear; the compiler proof establishes the constructor absent
before this boundary is crossed. -/
theorem holLoopProgToExecutable_preserves_locValueFree {width : Nat} [NeZero width]
    (projectLive : NumSet → List Nat) (program : HolLoopProg width)
    (hfree : holLoopProgLocValueFree program) :
    loopProgLocValueFree (holLoopProgToExecutable projectLive program) := by
  let mProg : HolLoopProg width → Prop := fun p =>
    holLoopProgLocValueFree p →
      loopProgLocValueFree (holLoopProgToExecutable projectLive p)
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program <;>
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        holLoopProgLocValueFree, loopProgLocValueFree, holLoopProgToExecutable]
    case refine_23 =>
      intro returns target arguments handler hHandler hfree
      cases handler with
      | none => simp [loopProgLocValueFree, holLoopProgToExecutable]
      | some entry =>
          rcases entry with ⟨exception, first, second, live⟩
          rcases hHandler with ⟨ihFirst, ihSecond⟩
          simp only [holLoopProgLocValueFree] at hfree
          rcases hfree with ⟨hFirst, hSecond⟩
          have hFirst' := ihFirst hFirst
          have hSecond' := ihSecond hSecond
          simp [loopProgLocValueFree, holLoopProgToExecutable, hFirst', hSecond']
  exact hgeneral hfree

end Flapjack
