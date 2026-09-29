import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval.Leaf

/-!
# `crep_to_loop` expression simulation: load case

The `Load e` evaluator-induction case of HOL `comp_exp_preserves_eval`
(`crep_to_loopProofScript.sml:772`, proof case at `:982-995`). The memory
domain and both memories use the exact HOL-shaped carriers from `mem_rel_def`
and `state_rel_def`; this theorem is proof-side and does not route production
`loopCompileExp` through `compileExpHOLExact`.
-/

namespace Flapjack

namespace CompExpPreservesEvalLoadFmapWitnesses

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

end CompExpPreservesEvalLoadFmapWitnesses

/-- `Load e` case of HOL `comp_exp_preserves_eval`. The premise `hIH` is the
    evaluator-induction hypothesis for the source subexpression `address`,
    with exactly the parent theorem's assumptions/conclusion specialized to
    that subexpression. The case keeps HOL's successful source evaluation,
    exact state/memory/globals/code/locals relations, compiler equation, and
    fresh-temporary condition; it adds no target-result premise. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "comp_exp_preserves_eval"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals,
    CrepSemHOLState.globals, CrepSemHOLState.code,
    CrepToLoopContextExact.vars, CrepToLoopContextExact.funcs,
    LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem compExpPreservesEval_load_case {width : Nat} [NeZero width]
    {ffiState : Type}
    (s : CrepSemHOLState width ffiState) (address : CrepExpHOL width)
    (v : HolWordLab width) (t : LoopSemStateFiniteExact width ffiState)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width)
    (ntmp : Nat) (nl : NumSet)
    (hEval : evalCrepSemHOLExp s (.load address) = some v)
    (hState : crepToLoopStateRelExact s t)
    (hMem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hCode : crepToLoopCodeRelExact ctxt s.code t.code)
    (hLocals : crepToLoopLocalsRelExact ctxt l s.locals t.locals)
    (hCompile : compileExpHOLExact ctxt tmp l (.load address) =
      (p, le, ntmp, nl))
    (_hFresh : ctxt.vmax < tmp)
    (hIH : ∀ (addressValue : HolWordLab width)
      (addressCode : List (HolLoopProg width))
      (addressResult : HolLoopExp width) (addressNext : Nat)
      (addressLocals : NumSet),
      evalCrepSemHOLExp s address = some addressValue →
      crepToLoopStateRelExact s t →
      crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs →
      crepToLoopGlobalsRelHOLExact s.globals t.globals →
      crepToLoopCodeRelExact ctxt s.code t.code →
      crepToLoopLocalsRelExact ctxt l s.locals t.locals →
      compileExpHOLExact ctxt tmp l address =
        (addressCode, addressResult, addressNext, addressLocals) →
      ctxt.vmax < tmp →
      ∃ ck st,
        LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL addressCode)
            { t with clock := t.clock + ck } = (none, st) ∧
        LoopSemStateFiniteExact.eval st addressResult =
            some (wlabWlocExact addressValue) ∧
        crepToLoopStateRelExact s st ∧
        crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
        crepToLoopCodeRelExact ctxt s.code st.code ∧
      crepToLoopLocalsRelExact ctxt addressLocals s.locals st.locals) :
    ∃ ck st,
      LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
          { t with clock := t.clock + ck } = (none, st) ∧
      LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
      crepToLoopStateRelExact s st ∧
      crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
      crepToLoopCodeRelExact ctxt s.code st.code ∧
      crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  cases hAddress : evalCrepSemHOLExp s address with
  | none => simp [evalCrepSemHOLExp, hAddress] at hEval
  | some addressValue =>
      cases addressValue with
      | word addressWord =>
          simp only [evalCrepSemHOLExp, hAddress] at hEval
          by_cases hDomain : s.memaddrs addressWord
          · simp [hDomain] at hEval
            subst v
            rcases hCompileAddress :
                compileExpHOLExact ctxt tmp l address with
              ⟨addressCode, addressResult, addressNext, addressLocals⟩
            rw [compileExpHOLExact, hCompileAddress] at hCompile
            simp only [Prod.mk.injEq] at hCompile
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hCompile
            obtain ⟨ck, st, hRun, hAddressResult, hState', hMem',
              hGlobals', hCode', hLocals'⟩ :=
                hIH (.word addressWord) addressCode addressResult
                  addressNext addressLocals hAddress hState hMem hGlobals
                  hCode hLocals hCompileAddress _hFresh
            refine ⟨ck, st, hRun, ?_, hState', hMem', hGlobals',
              hCode', hLocals'⟩
            have hDomain' : st.mdomain addressWord = true := by
              have h := congrFun hState'.1 addressWord
              simpa [hDomain] using h.symm
            simp only [LoopSemStateFiniteExact.eval, hAddressResult,
              wlabWlocExact, LoopSemStateFiniteExact.memLoad,
              hDomain', if_true]
            exact congrArg some (hMem' addressWord hDomain).symm
          · simp [hDomain] at hEval

end Flapjack
