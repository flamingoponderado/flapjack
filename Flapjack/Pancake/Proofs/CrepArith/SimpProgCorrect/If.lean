import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# If case of HOL `crep_arith$simp_prog_correct`

This counterpart submodule contains the exact `If` case of
`crep_arithProofScript.sml:186-212`.  The condition is simplified with
`simp_exp` and still evaluates to the same word (`simp_exp_correct`); the
selected branch, in the same state, is related by the `evaluate_ind` If
induction hypothesis.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectIfSupport

/-- Same-module canonical finite-support witness for the named state fields
    used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectIfSupport

private theorem crepSimpProgHOL_ite {width : Nat} [NeZero width]
    (condition : CrepExpHOL width) (thenBranch elseBranch : CrepProgHOL width) :
    crepSimpProgHOL (.ite condition thenBranch elseBranch) =
      .ite (crepSimpExpHOL condition) (crepSimpProgHOL thenBranch)
        (crepSimpProgHOL elseBranch) := by
  conv => lhs; unfold crepSimpProgHOL

/-- The `If` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:186-212`), with exactly the `evaluate_ind` If
    induction hypothesis (`evalCrepSemHOLProgExact_induct` `hite`): when the
    condition evaluates to `Word w`, the predicate for the selected branch
    `if w ≠ 0w then c1 else c2` in the same state. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectIfCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (e : CrepExpHOL width) (c1 c2 : CrepProgHOL width)
      (state : CrepSemHOLState width σ),
      (∀ (v1 : HolWordLab width) (w : BitVec width),
        crepExactEvalExpClassical state e = some v1 → v1 = .word w →
        simpProgCorrectAt (if w ≠ 0 then c1 else c2) state) →
      ∀ (result : Option (CrepResultHOLExact width))
        (finalState : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact state (.ite e c1 c2) = (result, finalState) →
        result ≠ some .error →
        evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
            (crepSimpProgHOL (.ite e c1 c2)) =
          (result, crepSimpMapcsHOL finalState) := by
  intro e c1 c2 state ih result finalState he hne
  rw [crepSimpProgHOL_ite, evalCrepSemHOLProgExact_ite_holShape]
  rw [evalCrepSemHOLProgExact_ite_holShape] at he
  cases hexp : evalCrepSemHOLExp state e with
  | none =>
      rw [hexp] at he
      exact (hne (congrArg Prod.fst he).symm).elim
  | some value =>
  cases value with
  | word w =>
  have hexpT : evalCrepSemHOLExp (crepSimpMapcsHOL state) (crepSimpExpHOL e) =
      some (.word w) := by
    rw [crepSimpMapcsHOL_eq_mapc]
    exact crepSimpExpCorrectNativeHOL _ state e _ hexp
  rw [hexp] at he
  rw [hexpT]
  simp only at he ⊢
  have hvalue : crepExactEvalExpClassical state e = some (.word w) := by
    rw [crepExactEvalExpClassical_eq]
    exact hexp
  have hbranch := ih (.word w) w hvalue rfl result finalState he hne
  by_cases hw : w ≠ 0
  · rw [if_pos hw] at hbranch ⊢
    exact hbranch
  · rw [if_neg hw] at hbranch ⊢
    exact hbranch

end Flapjack
