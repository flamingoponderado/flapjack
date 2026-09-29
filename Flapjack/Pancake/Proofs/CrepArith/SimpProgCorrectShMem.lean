import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# `ShMem` case of HOL `crep_arith$simp_prog_correct`

`crep_arithProofScript.sml` proves `simp_prog_correct` by a case split matching
HOL's `eval_ind`; the leaf cases live in `SimpProgCorrect.lean`.  This module
adds the shared-memory induction case.  The source evaluation is the native
exact evaluator `evalCrepSemHOLProgExact` at the original state; the target
evaluates `crepSimpProgHOL` at the proof-script-local `mapc`-rewritten state
`crepSimpMapcsHOL`.

The `ShMem` clause only simplifies its address expression, and the code-only
`mapc` update leaves locals, the shared-memory domain and the FFI unchanged.
The address equivalence is HOL `simp_exp_correct`
(`crepSimpExpCorrectNativeHOL`), and the shared-memory commutation is HOL
`sh_mem_op_code` (`crepShMemOpExactHOL_mapc`).  As in HOL, the `result ≠
SOME Error` side condition discharges every failing arm (a bad address
expression or a missing/mis-typed local).
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectShMemSupport

/-- Same-module canonical witness for the named finite-map fields on the
    `CrepSemHOLState` carrier used by the ShMem case theorem below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectShMemSupport

/-- The `ShMem` case of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`), over the native exact Crep evaluator
    and the exact finite-support `mapc` update.  HOL's `mapcs` is the local
    overload `SimpProgCorrect.lean` renders as `crepSimpMapcsHOL`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectShMemCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (operator : WordMemOp) (name : Nat)
      (address : CrepExpHOL width)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.shMem operator name address) = (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.shMem operator name address)) =
        (result, crepSimpMapcsHOL finalState) := by
  classical
  intro state operator name address result finalState heval hresult
  let f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width :=
    fun (_, entry) => (entry.1, crepSimpProgHOL entry.2)
  have hmapped : crepSimpMapcsHOL state = state.mapc f := rfl
  have hmapped' : crepSimpMapcsHOL finalState = finalState.mapc f := rfl
  simp only [crepSimpProgHOL]
  rw [hmapped, evalCrepSemHOLProgExact_shMem_holShape, hmapped']
  rw [evalCrepSemHOLProgExact_shMem_holShape] at heval
  generalize hsrc : evalCrepSemHOLExp state address = src
  cases src with
  | none =>
      have heval' : (some .error, state) = (result, finalState) := by
        rw [hsrc] at heval
        simpa using heval
      exact absurd (congrArg Prod.fst heval').symm hresult
  | some w =>
      cases w with
      | word addr =>
          have htargetEval :
              evalCrepSemHOLExp (state.mapc f) (crepSimpExpHOL address) =
                some (.word addr) :=
            crepSimpExpCorrectNativeHOL f state address (.word addr) hsrc
          rw [htargetEval]
          dsimp only [CrepSemHOLState.mapc] at heval ⊢
          rw [hsrc] at heval
          generalize hc : crepIsLoadMemOp operator = c at heval ⊢
          cases c <;>
            simp only [Bool.false_eq_true, if_true, if_false] at heval ⊢
          all_goals
            generalize hl : state.locals.lookup name = l at heval ⊢
            cases l
            case none =>
              have heval' : (some .error, state) = (result, finalState) := heval
              exact absurd (congrArg Prod.fst heval').symm hresult
            case some val =>
              cases val
              case word v =>
                have heval' : crepShMemOpExactHOL operator name addr state =
                    (result, finalState) := heval
                rw [crepShMemOpExactHOL_mapc f operator name addr state, heval']
                rfl

end Flapjack
