import Flapjack.Pancake.Proofs.CrepInline.NoReturn
import Flapjack.Pancake.Proofs.CrepInline.UnreachElim

namespace Flapjack.CrepInlineNotBranchReturn

/-- Flapjack syntactic proof factoring, with no separate HOL original:
    a fixed point reporting no unconditional exit and satisfying the source
    branch restriction contains no return, including tail calls. -/
private theorem fixedNoneNotBranch_hasNoReturn {width : Nat} [NeZero width] :
    ∀ p : CrepProgHOL width,
      unreachElimHOLExact p = (p, none) → notBranchRetHOLExact p = true →
      hasReturnHOLExact p = false := by
  intro p
  fun_induction unreachElimHOLExact p <;> intro hu hb <;>
    simp_all [notBranchRetHOLExact, hasReturnHOLExact]

/-- Canonical finite-support state roundtrip for the representation qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- HOL `crep_inlineProofScript.sml:1781-1800`: the same fixed-point,
    branch restriction and evaluation equality premises exclude every Return
    payload. The proof factors through the syntactic no-return fact and the
    reviewed evaluator theorem; no logical premise or decider is added. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml"
  "not_branch_ret_evaluate_return_unreach_elim"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem notBranchRetEvaluateReturnUnreachElim {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ)
    (result : Option (CrepResultHOLExact width)) (next : CrepSemHOLState width σ)
    (h : unreachElimHOLExact program = (program, none) ∧
      notBranchRetHOLExact program = true ∧
      evalCrepSemHOLProgExact state program = (result, next)) :
    ∀ value, result ≠ some (.return value) := by
  intro value
  exact CrepInlineNoReturn.notHasReturnNotEvaluateReturnPrime program state result next value
    ⟨fixedNoneNotBranch_hasNoReturn program h.1 h.2.1, h.2.2⟩

end Flapjack.CrepInlineNotBranchReturn
