import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# Dec case of HOL `crep_arith$simp_prog_correct`

This counterpart submodule contains the exact `Dec` case of
`crep_arithProofScript.sml:186-212`.  The declared expression is simplified
with `simp_exp` and still evaluates to the same value (`simp_exp_correct`).
The body is related by the `evaluate_ind` Dec induction hypothesis at the
extended locals, and `mapcs` commutes with the locals update and the
`res_var` restore.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectDecSupport

/-- Same-module canonical finite-support witness for the named state fields
    used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectDecSupport

private theorem crepSimpProgHOL_dec {width : Nat} [NeZero width]
    (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width) :
    crepSimpProgHOL (.dec name value body) =
      .dec name (crepSimpExpHOL value) (crepSimpProgHOL body) := by
  conv => lhs; unfold crepSimpProgHOL

/-- The `Dec` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:186-212`), with exactly the `evaluate_ind` Dec
    induction hypothesis (`evalCrepSemHOLProgExact_induct` `hdec`): for every
    value of the declared expression, the predicate for the body at
    `set_var v value s`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectDecCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (v : Nat) (e : CrepExpHOL width) (prog : CrepProgHOL width)
      (state : CrepSemHOLState width σ),
      (∀ value, crepExactEvalExpClassical state e = some value →
        simpProgCorrectAt prog (CrepSemHOLState.setVar v value state)) →
      ∀ (result : Option (CrepResultHOLExact width))
        (finalState : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact state (.dec v e prog) = (result, finalState) →
        result ≠ some .error →
        evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
            (crepSimpProgHOL (.dec v e prog)) =
          (result, crepSimpMapcsHOL finalState) := by
  intro v e prog state ih result finalState he hne
  rw [crepSimpProgHOL_dec, evalCrepSemHOLProgExact_dec_holShape]
  rw [evalCrepSemHOLProgExact_dec_holShape] at he
  cases hexp : evalCrepSemHOLExp state e with
  | none =>
      rw [hexp] at he
      exact (hne (congrArg Prod.fst he).symm).elim
  | some value =>
  have hexpT : evalCrepSemHOLExp (crepSimpMapcsHOL state) (crepSimpExpHOL e) = some value := by
    rw [crepSimpMapcsHOL_eq_mapc]
    exact crepSimpExpCorrectNativeHOL _ state e value hexp
  rw [hexp] at he
  rw [hexpT]
  simp only at he ⊢
  rcases hbody : evalCrepSemHOLProgExact
      { state with locals := state.locals.updateEq (v, value) } prog with ⟨r, st⟩
  rw [hbody] at he
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hvalue : crepExactEvalExpClassical state e = some value := by
    rw [crepExactEvalExpClassical_eq]
    exact hexp
  have hbodyT : evalCrepSemHOLProgExact
      { crepSimpMapcsHOL state with
        locals := (crepSimpMapcsHOL state).locals.updateEq (v, value) }
      (crepSimpProgHOL prog) = (r, crepSimpMapcsHOL st) :=
    ih value hvalue r st hbody hne
  rw [hbodyT]
  rfl

end Flapjack
