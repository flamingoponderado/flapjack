import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# While case of HOL `crep_arith$simp_prog_correct`

This counterpart submodule contains the exact `While` case of
`crep_arithProofScript.sml:186-212` (the `Case (While _ _)` branch).  The
condition is simplified with `simp_exp` and still evaluates to the same word
(`simp_exp_correct`).  The body, run at `dec_clock s`, and the loop re-entry
after a `NONE` or `Continue 0` body result are related by the three
`evaluate_ind` While induction hypotheses.  `mapcs` commutes with `dec_clock`
and `empty_locals`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectWhileSupport

/-- Same-module canonical finite-support witness for the named state fields
    used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectWhileSupport

private theorem crepSimpProgHOL_while {width : Nat} [NeZero width]
    (condition : CrepExpHOL width) (body : CrepProgHOL width) :
    crepSimpProgHOL (.while condition body) =
      .while (crepSimpExpHOL condition) (crepSimpProgHOL body) := by
  conv => lhs; unfold crepSimpProgHOL

/-- The `While` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:186-212`), with exactly the three `evaluate_ind`
    While induction hypotheses (`evalCrepSemHOLProgExact_induct` `hwhile`):
    after a true condition and nonzero clock, the predicate for the loop at the
    body's final state when the body returns `Continue 0` or `NONE`, and the
    predicate for the body at `dec_clock s`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectWhileCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (e : CrepExpHOL width) (c : CrepProgHOL width) (state : CrepSemHOLState width σ),
      (∀ (v2 : HolWordLab width) (w : BitVec width)
          (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
          (v1 : CrepResultHOLExact width) (v8 : Nat),
        crepExactEvalExpClassical state e = some v2 → v2 = .word w → w ≠ 0 →
        state.clock ≠ 0 →
        (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL state) c →
        res = some v1 → v1 = .continue v8 → v8 = 0 →
        simpProgCorrectAt (.while e c) s1) →
      (∀ (v2 : HolWordLab width) (w : BitVec width)
          (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ),
        crepExactEvalExpClassical state e = some v2 → v2 = .word w → w ≠ 0 →
        state.clock ≠ 0 →
        (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL state) c →
        res = none →
        simpProgCorrectAt (.while e c) s1) →
      (∀ (v2 : HolWordLab width) (w : BitVec width),
        crepExactEvalExpClassical state e = some v2 → v2 = .word w → w ≠ 0 →
        state.clock ≠ 0 →
        simpProgCorrectAt c (decClockCrepSemHOL state)) →
      ∀ (result : Option (CrepResultHOLExact width))
        (finalState : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact state (.while e c) = (result, finalState) →
        result ≠ some .error →
        evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
            (crepSimpProgHOL (.while e c)) =
          (result, crepSimpMapcsHOL finalState) := by
  intro e c state ihContinue ihNone ihBody result finalState he hne
  have herr : ∀ {st : CrepSemHOLState width σ},
      (some CrepResultHOLExact.error, st) = (result, finalState) → False := by
    intro st h
    exact hne (congrArg Prod.fst h).symm
  rw [crepSimpProgHOL_while, evalCrepSemHOLProgExact_while_holShape]
  rw [evalCrepSemHOLProgExact_while_holShape] at he
  cases hexp : evalCrepSemHOLExp state e with
  | none =>
      rw [hexp] at he
      exact (herr he).elim
  | some value =>
  cases value with
  | word w =>
  have hexpT : evalCrepSemHOLExp (crepSimpMapcsHOL state) (crepSimpExpHOL e) =
      some (.word w) := by
    rw [crepSimpMapcsHOL_eq_mapc]
    exact crepSimpExpCorrectNativeHOL _ state e _ hexp
  have hvalue : crepExactEvalExpClassical state e = some (.word w) := by
    rw [crepExactEvalExpClassical_eq]
    exact hexp
  rw [hexp] at he
  rw [hexpT]
  simp only at he ⊢
  by_cases hw0 : ¬ w ≠ 0
  · rw [if_neg hw0] at he
    rw [if_neg hw0]
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rfl
  have hw : w ≠ 0 := Classical.not_not.mp hw0
  rw [if_pos hw] at he
  rw [if_pos hw]
  by_cases hc : state.clock = 0
  · rw [if_pos hc] at he
    rw [if_pos (show (crepSimpMapcsHOL state).clock = 0 from hc)]
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rfl
  rw [if_neg hc] at he
  rw [if_neg (show ¬ (crepSimpMapcsHOL state).clock = 0 from hc)]
  rcases hbody : evalCrepSemHOLProgExact (decClockCrepSemHOL state) c with ⟨res, s1⟩
  rw [hbody] at he
  simp only at he ⊢
  have hres : res ≠ some .error := by
    intro h
    subst h
    exact herr he
  have hbodyT : evalCrepSemHOLProgExact (decClockCrepSemHOL (crepSimpMapcsHOL state))
      (crepSimpProgHOL c) = (res, crepSimpMapcsHOL s1) :=
    ihBody (.word w) w hvalue rfl hw hc res s1 hbody hres
  rw [hbodyT]
  simp only
  rcases res with _ | r
  · have hloop := ihNone (.word w) w none s1 hvalue rfl hw hc hbody.symm rfl
      result finalState he hne
    rw [crepSimpProgHOL_while] at hloop
    exact hloop
  cases r with
  | «continue» label =>
      cases label with
      | zero =>
          have hloop := ihContinue (.word w) w (some (.continue 0)) s1 (.continue 0) 0
            hvalue rfl hw hc hbody.symm rfl rfl rfl result finalState he hne
          rw [crepSimpProgHOL_while] at hloop
          exact hloop
      | succ label =>
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          rfl
  | «break» label =>
      cases label with
      | zero =>
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          rfl
      | succ label =>
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          rfl
  | _ =>
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rfl

end Flapjack
