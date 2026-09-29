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

/-- Var case of HOL `comp_exp_preserves_eval`. The source `Var` lookup is
    transferred through the exact `locals_rel` premise and the same
    `context.vars` mapping used by `compile_exp`; the theorem keeps the HOL
    premises and target existential unchanged. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compExpPreservesEval_var_case {width : Nat} [NeZero width]
    {ffiState : Type}
    (s : CrepSemHOLState width ffiState) (name : Nat)
    (v : HolWordLab width) (t : LoopSemStateFiniteExact width ffiState)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width)
    (ntmp : Nat) (nl : NumSet)
    (hEval : evalCrepSemHOLExp s (.var name) = some v)
    (hState : crepToLoopStateRelExact s t)
    (hMem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt s.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt l s.locals t.locals)
    (hCompile : compileExpHOLExact ctxt tmp l (.var name) = (p, le, ntmp, nl))
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
  have hEval' : s.locals.lookup name = some v := by
    simpa [evalCrepSemHOLExp] using hEval
  simp [compileExpHOLExact] at hCompile
  rcases hCompile with ⟨rfl, rfl, rfl, rfl⟩
  rcases crepToLoopLocalsRelExact_intro ctxt l s.locals t.locals hLocals with
    ⟨_, _, _, hLookup⟩
  obtain ⟨mapped, hMapped, _, hValue⟩ := hLookup name v hEval'
  refine ⟨0, t, ?_, ?_, hState, hMem, hGlobals, hCode, hLocals⟩
  · simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate]
  · simpa [LoopSemStateFiniteExact.eval, hMapped, wlabWlocHOL,
      wlabWlocExact] using hValue

/-- `LoadGlob` case of HOL `comp_exp_preserves_eval`: exact global lookup
    preservation for the source load and target lookup expression. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compExpPreservesEval_loadGlob_case {width : Nat} [NeZero width]
    {ffiState : Type}
    (s : CrepSemHOLState width ffiState) (address : BitVec 5)
    (v : HolWordLab width) (t : LoopSemStateFiniteExact width ffiState)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width)
    (ntmp : Nat) (nl : NumSet)
    (hEval : evalCrepSemHOLExp s (.loadGlob address) = some v)
    (hState : crepToLoopStateRelExact s t)
    (hMem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt s.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt l s.locals t.locals)
    (hCompile : compileExpHOLExact ctxt tmp l (.loadGlob address) =
      (p, le, ntmp, nl))
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
  have hEval' : s.globals.lookup address = some v := by
    simpa [evalCrepSemHOLExp] using hEval
  have hCompile' : ([], HolLoopExp.lookup address, tmp, l) =
      (p, le, ntmp, nl) := by
    simpa [compileExpHOLExact] using hCompile
  cases hCompile'
  have hTarget := hGlobals address v hEval'
  refine ⟨0, t, ?_, ?_, hState, hMem, hGlobals, hCode, hLocals⟩
  · simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate]
  · simpa [LoopSemStateFiniteExact.eval, wlabWlocExact] using hTarget

/-- `BaseAddr` case of HOL `comp_exp_preserves_eval`; the target value follows
    from the corresponding exact `state_rel` field. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compExpPreservesEval_baseAddr_case {width : Nat} [NeZero width]
    {ffiState : Type}
    (s : CrepSemHOLState width ffiState) (v : HolWordLab width)
    (t : LoopSemStateFiniteExact width ffiState)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width)
    (ntmp : Nat) (nl : NumSet)
    (hEval : evalCrepSemHOLExp s .baseAddr = some v)
    (hState : crepToLoopStateRelExact s t)
    (hMem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt s.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt l s.locals t.locals)
    (hCompile : compileExpHOLExact ctxt tmp l .baseAddr = (p, le, ntmp, nl))
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
  have hv : v = HolWordLab.word s.baseAddr := by
    have h := Option.some.inj (by simpa [evalCrepSemHOLExp] using hEval)
    exact h.symm
  have hBase : s.baseAddr = t.baseAddr := by
    rcases hState with ⟨_, _, _, _, _, hBase, _⟩
    exact hBase
  have hCompile' : ([], HolLoopExp.baseAddr, tmp, l) =
      (p, le, ntmp, nl) := by
    simpa [compileExpHOLExact] using hCompile
  cases hCompile'
  subst v
  refine ⟨0, t, ?_, ?_, hState, hMem, hGlobals, hCode, hLocals⟩
  · simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate]
  · simp [LoopSemStateFiniteExact.eval, wlabWlocExact, hBase]

/-- `TopAddr` case of HOL `comp_exp_preserves_eval`; the target value follows
    from the corresponding exact `state_rel` field. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compExpPreservesEval_topAddr_case {width : Nat} [NeZero width]
    {ffiState : Type}
    (s : CrepSemHOLState width ffiState) (v : HolWordLab width)
    (t : LoopSemStateFiniteExact width ffiState)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width)
    (ntmp : Nat) (nl : NumSet)
    (hEval : evalCrepSemHOLExp s .topAddr = some v)
    (hState : crepToLoopStateRelExact s t)
    (hMem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt s.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt l s.locals t.locals)
    (hCompile : compileExpHOLExact ctxt tmp l .topAddr = (p, le, ntmp, nl))
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
  have hv : v = HolWordLab.word s.topAddr := by
    have h := Option.some.inj (by simpa [evalCrepSemHOLExp] using hEval)
    exact h.symm
  have hTop : s.topAddr = t.topAddr := by
    rcases hState with ⟨_, _, _, _, _, _, hTop⟩
    exact hTop
  have hCompile' : ([], HolLoopExp.topAddr, tmp, l) =
      (p, le, ntmp, nl) := by
    simpa [compileExpHOLExact] using hCompile
  cases hCompile'
  subst v
  refine ⟨0, t, ?_, ?_, hState, hMem, hGlobals, hCode, hLocals⟩
  · simp [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate]
  · simp [LoopSemStateFiniteExact.eval, wlabWlocExact, hTop]

end Flapjack
