import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.PanSem.TotalMeasureIf
import Flapjack.Pancake.Semantics.CrepSem.TotalEval
import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
# Total evaluator cases for Pan-to-Crep correctness

The declarations here assemble selected constructor cases from the total,
HOL-result-shaped source and target evaluator clauses. They are induction-case
support for `pc_compile_correct`; they do not claim the complete evaluator
induction or receive a standalone `@[hol]` reference.
-/

namespace Flapjack

/-! The `Skip` constructor case uses the total result×state clauses on both
  sides. The source evaluator uses the production `PanSemState`, and the target
  evaluator uses the code-bearing runtime state converted by `toHolState`. The
  compiled target syntax is exactly `Skip`. The returned runtime post-state is
  the original target state, so all four state/code/exception/local relations
  are established at the post-state boundary without a target-run premise. -/
theorem panToCrepTotalSkipStateCase
    {σ : Type _}
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code)
      targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateExprIfFragmentRiscV64ByMeasure (.leaf .skip) sourceState =
        (none, sourceState) ∧
    compileCodeRelProg context (.skip : Prog (RiscV.Word 64)) =
        (CrepProg.skip : CrepProg (BitVec 64)) ∧
    ∃ targetPost : CrepRuntimeState (RiscV.Word 64) σ,
      evalCrepClockLeaf .skip targetState.toHolState =
          (none, targetPost.toHolState) ∧
      stateRel sourceState targetPost ∧
      codeRel context (panSemCodeAsLookup sourceState.code) targetPost.code ∧
      excpRel context.eids sourceState.exceptionShapes ∧
      localsRel context sourceState.locals targetPost.locals := by
  refine ⟨by simp [panSemEvaluateExprIfFragmentRiscV64ByMeasure], rfl, ?_⟩
  refine ⟨targetState, by simp, hstate, ?_, hexcp, hlocals⟩
  exact hcode

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Break]`.
The HOL proof resumes this nonrecursive case at
`pan_to_crepProofScript.sml:499-503`; the source evaluator equation is
`panSemScript.sml:623`, the compiler equation is `pan_to_crepScript.sml:219`,
and the target evaluator equation is `crepSemScript.sml:309`. They give source
`Break`, compiled `Break 0`, and target `Break 0`, all with unchanged states.
This helper checks those equations over the finite-support HOL-shaped carriers
and records preservation of the exact state/local relations. It does not state
the full `pc_compile_correct` case: exact `code_rel` and `excp_rel` assembly
remain outside this slice, so this Flapjack-specific equation carries no
`@[hol]` tag. -/
theorem panToCrepExactBreakTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.break : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (some .break, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.break : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.break 0 : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.break : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (some (.break 0), targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals := by
  refine ⟨?_, ?_, ?_, hstate, hlocals⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.break : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.break 0 : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_break targetState memDec shMemDec 0

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Continue]`.
The proof resumes the nonrecursive constructor at
`pan_to_crepProofScript.sml:505-509`; the source evaluator equation is
`panSemScript.sml:624`, the exact compiler clause is
`pan_to_crepScript.sml:220`, and the target evaluator equation is
`crepSemScript.sml:313`. This slice establishes source `Continue`, compiled
`Continue 0`, and target `Continue 0`, preserving the exact source/target
state and local relations. It is not the full `pc_compile_correct` case:
assembling the exact code and exception relations remains open, so this
Flapjack-specific helper carries no `@[hol]` tag. The production-codec bridge
`compileProgExactHOLW_continue_bridge` is a distinct theorem and is not
duplicated here. -/
theorem panToCrepExactContinueTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.continue : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (some .continue, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.continue : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.continue 0 : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.continue : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (some (.continue 0), targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals := by
  refine ⟨?_, ?_, ?_, hstate, hlocals⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.continue : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.continue 0 : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_continue targetState memDec shMemDec 0

end Flapjack
