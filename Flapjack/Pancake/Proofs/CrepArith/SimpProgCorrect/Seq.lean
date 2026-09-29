import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# Seq case of HOL `crep_arith$simp_prog_correct`

This counterpart submodule ports the `Seq` induction case. Its two induction
hypotheses match HOL `crepSem$evaluate_ind`: the first proves the property for
the first program, and the second proves it for the second program when the
first evaluation returns `NONE`, at the exact intermediate state. Both source
and simplified executions use the exact total Crep evaluator.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectSeqSupport

/-- Same-module canonical finite-support witness for the named state fields
    used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectSeqSupport

/-- The `Seq` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`), with the two induction hypotheses
    from the `Seq` clause of `crepSem$evaluate_ind` (`crepSemScript.sml:440`).
    The second hypothesis is available only after the first program evaluates
    to `NONE`, and uses its exact intermediate state. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectSeqCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (first second : CrepProgHOL width),
      (∀ (firstResult : Option (CrepResultHOLExact width))
          (firstState : CrepSemHOLState width σ),
          (firstResult, firstState) = evalCrepSemHOLProgExact state first →
          firstResult = none →
          ∀ (result : Option (CrepResultHOLExact width))
            (finalState : CrepSemHOLState width σ),
            evalCrepSemHOLProgExact firstState second = (result, finalState) →
            result ≠ some .error →
            evalCrepSemHOLProgExact (crepSimpMapcsHOL firstState)
                (crepSimpProgHOL second) =
              (result, crepSimpMapcsHOL finalState)) →
      (∀ (result : Option (CrepResultHOLExact width))
          (finalState : CrepSemHOLState width σ),
          evalCrepSemHOLProgExact state first = (result, finalState) →
          result ≠ some .error →
          evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
              (crepSimpProgHOL first) =
            (result, crepSimpMapcsHOL finalState)) →
      ∀ (result : Option (CrepResultHOLExact width))
        (finalState : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact state (.seq first second : CrepProgHOL width) =
            (result, finalState) →
        result ≠ some .error →
        evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
            (crepSimpProgHOL (.seq first second : CrepProgHOL width)) =
          (result, crepSimpMapcsHOL finalState) := by
  intro state first second ihSecond ihFirst result finalState heval hresult
  rw [evalCrepSemHOLProgExact_seq_holShape] at heval
  cases hfirst : evalCrepSemHOLProgExact state first with
  | mk firstResult firstState =>
      simp only [hfirst] at heval
      by_cases hnormal : firstResult = none
      · simp [hnormal] at heval
        have hfirstNone :
            evalCrepSemHOLProgExact state first = (none, firstState) := by
          simpa [hnormal] using hfirst
        have hfirstTarget := ihFirst none firstState hfirstNone (by simp)
        have hsecondTarget :=
          ihSecond none firstState hfirstNone.symm rfl result finalState heval hresult
        rw [crepSimpProgHOL, evalCrepSemHOLProgExact_seq_holShape, hfirstTarget]
        simpa using hsecondTarget
      · simp [hnormal] at heval
        rcases heval with ⟨hresultEq, hstateEq⟩
        subst result
        subst finalState
        have hfirstTarget := ihFirst firstResult firstState hfirst hresult
        rw [crepSimpProgHOL, evalCrepSemHOLProgExact_seq_holShape, hfirstTarget]
        simp [hnormal]

end Flapjack
