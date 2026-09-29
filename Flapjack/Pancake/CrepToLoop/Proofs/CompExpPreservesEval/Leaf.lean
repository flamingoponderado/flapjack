import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact

/-!
# `crep_to_loop` expression simulation: constant leaf

The Const evaluator-induction case of HOL `comp_exp_preserves_eval`
(`crep_to_loopProofScript.sml:772`, proof case at `:973-976`).
-/

namespace Flapjack

namespace CompExpPreservesEvalLeafFmapWitnesses

/-- Same-module canonical roundtrip required by the finite-map representation
qualifier for the exact Crep state fields used by this case. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {ffiState : Type}
    (state : CrepSemHOLState width ffiState) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

/-- Same-module canonical roundtrip required by the finite-map representation
qualifier for the exact context fields used by this case. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

/-- Same-module canonical roundtrip required by the finite-map representation
qualifier for the exact Loop state fields used by this case. -/
theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {ffiState : Type} :
    (∀ (state : LoopSemStateBroad width ffiState) (h : state.FiniteSupport),
      (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width ffiState,
      LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end CompExpPreservesEvalLeafFmapWitnesses

/-- Const case of HOL `comp_exp_preserves_eval`. This is the genuine
    `Const w` evaluator-induction case: it retains the original successful
    source evaluation, exact state/memory/globals/code/locals relations,
    `compile_exp` equation, fresh-temporary side condition, and the target run
    plus all post-state relations. It adds no target-result premise or other
    strengthening. The HOL proof discharges this case by unfolding the Crep
    evaluator/compiler clauses, `nested_seq`, and Loop evaluation; the exact
    zero-code compilation leaves the Loop state unchanged. This theorem is
    proof-side; it does not route the production `loopCompileExp` path. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compExpPreservesEval_const_case {width : Nat} [NeZero width]
    {ffiState : Type}
    (s : CrepSemHOLState width ffiState) (word : BitVec width)
    (v : HolWordLab width) (t : LoopSemStateFiniteExact width ffiState)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width)
    (ntmp : Nat) (nl : NumSet)
    (hEval : evalCrepSemHOLExp s (.const word) = some v)
    (hState : crepToLoopStateRelExact s t)
    (hMem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt s.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt l s.locals t.locals)
    (hCompile : compileExpHOLExact ctxt tmp l (.const word) = (p, le, ntmp, nl))
    (_hFresh : ctxt.vmax < tmp) :
    ∃ ck st,
      LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
          { t with clock := t.clock + ck } = (none, st) ∧
      LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
      crepToLoopStateRelExact s st ∧
      crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
      crepToLoopCodeRelExact ctxt s.code st.code ∧
      crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  have hv : v = HolWordLab.word word := by
    have h := Option.some.inj (by simpa [evalCrepSemHOLExp] using hEval)
    exact h.symm
  have hCompile' : ([], HolLoopExp.const word, tmp, l) = (p, le, ntmp, nl) := by
    simpa [compileExpHOLExact] using hCompile
  cases hCompile'
  subst v
  refine ⟨0, t, ?_, ?_, hState, hMem, hGlobals, hCode, hLocals⟩
  · simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate]
  · simp [LoopSemStateFiniteExact.eval, wlabWlocExact]

end Flapjack
