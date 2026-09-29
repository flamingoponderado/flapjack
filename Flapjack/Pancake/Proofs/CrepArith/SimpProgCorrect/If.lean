import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# If case of HOL `crep_arith$simp_prog_correct`

This counterpart submodule ports the `If` induction case
(`crep_arithProofScript.sml:184-212`).  The single induction hypothesis is
exactly HOL `crepSem$evaluate_ind`'s `If` clause
(`crepSemScript.sml:440`, captured verbatim in
`scripts/hol-probes/crep_sem_evaluate_ind_probe.out`):

```
∀e c1 c2 s. (∀v1 w. eval s e = SOME v1 ∧ v1 = Word w ⇒
  P (if w ≠ 0w then c1 else c2, s)) ⇒ P (If e c1 c2, s)
```

so it is a guarded single hypothesis over the branch selected by the condition
word, at the same input state.  The condition is transported across the shared
code-only `mapcs` update by the tagged exact `simp_exp_correct`; no target-run
assumption, post-state relation, or extra success premise is taken.
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

/-- The `If` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`), with the `If` clause of
    `crepSem$evaluate_ind` (`crepSemScript.sml:440`).  Its single induction
    hypothesis carries the exact same guard `eval s e = SOME v1`, the equation
    `v1 = Word w`, and the selected branch program `if w ≠ 0w then c1 else c2`
    at the input state. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectIfCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (condition : CrepExpHOL width)
      (thenBranch elseBranch : CrepProgHOL width),
      (∀ (value : HolWordLab width) (w : BitVec width),
          evalCrepSemHOLExp state condition = some value →
          value = .word w →
          ∀ (result : Option (CrepResultHOLExact width))
            (finalState : CrepSemHOLState width σ),
            evalCrepSemHOLProgExact state
                (if w ≠ 0 then thenBranch else elseBranch) = (result, finalState) →
            result ≠ some .error →
            evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
                (crepSimpProgHOL (if w ≠ 0 then thenBranch else elseBranch)) =
              (result, crepSimpMapcsHOL finalState)) →
      ∀ (result : Option (CrepResultHOLExact width))
        (finalState : CrepSemHOLState width σ),
        evalCrepSemHOLProgExact state (.ite condition thenBranch elseBranch) =
            (result, finalState) →
        result ≠ some .error →
        evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
            (crepSimpProgHOL (.ite condition thenBranch elseBranch)) =
          (result, crepSimpMapcsHOL finalState) := by
  classical
  intro state condition thenBranch elseBranch ih result finalState heval hresult
  rw [evalCrepSemHOLProgExact_ite_holShape] at heval
  cases hcond : evalCrepSemHOLExp state condition with
  | none =>
      simp only [hcond] at heval
      exact absurd (Prod.ext_iff.mp heval).1.symm hresult
  | some value =>
      cases value with
      | word w =>
          simp only [hcond] at heval
          have htarget :=
            ih (.word w) w hcond rfl result finalState heval hresult
          have hcondition : evalCrepSemHOLExp (crepSimpMapcsHOL state)
              (crepSimpExpHOL condition) = some (.word w) := by
            have hsimpExp := crepSimpExpCorrectNativeHOL
              (fun entry : MlString × (List Nat × CrepProgHOL width) =>
                (entry.2.1, crepSimpProgHOL entry.2.2)) state condition (.word w)
              hcond
            simpa [crepSimpMapcsHOL] using hsimpExp
          have hsimpIte : crepSimpProgHOL
                (if w ≠ 0 then thenBranch else elseBranch) =
              (if w ≠ 0 then crepSimpProgHOL thenBranch
                else crepSimpProgHOL elseBranch) := by
            by_cases hw : w ≠ 0 <;> simp only [if_pos hw, if_neg hw]
          simp only [crepSimpProgHOL]
          rw [evalCrepSemHOLProgExact_ite_holShape]
          simp only [hcondition]
          rw [← hsimpIte]
          exact htarget

end Flapjack
