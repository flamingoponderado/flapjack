import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# Return case of HOL `crep_arith$simp_prog_correct`

The Return branch is a leaf of `crepSem$evaluate_ind`: it needs no induction
hypothesis.  It preserves the original source evaluation equation and
non-Error premise, and concludes the exact evaluator equation on the
`mapcs`-mapped state and `simp_prog` result.  The only successful branch is
proved with HOL `opt_mmap_simp_exp_correct`; a failed expression list would
produce `Error` and is excluded by the source premise.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectReturnSupport

/-- Same-module canonical finite-support witness for the state fields used by
    this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

private theorem crepSimpMapcsHOL_emptyLocals {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ) :
    crepSimpMapcsHOL (CrepSemHOLState.emptyLocals state) =
      CrepSemHOLState.emptyLocals (crepSimpMapcsHOL state) := by
  cases state
  rfl

end SimpProgCorrectReturnSupport

/-- The `Return` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`).  This is the nonrecursive
    `Return` clause of `crepSem$evaluate_ind` (`crepSemScript.sml:440`), so it
    has no induction-hypothesis parameter.  The statement retains HOL's source
    evaluation equation, non-`Error` premise, and mapped-state conclusion. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectReturnCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (values : List (CrepExpHOL width))
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.return values : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.return values : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  classical
  intro state values result finalState heval hresult
  rw [evalCrepSemHOLProgExact_return_holShape] at heval
  cases hvalues : values.mapM (evalCrepSemHOLExp state) with
  | none =>
      simp only [hvalues] at heval
      exact False.elim (hresult (congrArg Prod.fst heval).symm)
  | some words =>
      simp only [hvalues] at heval
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      let update : MlString × (List Nat × CrepProgHOL width) →
          List Nat × CrepProgHOL width :=
        fun (_, entry) => (entry.1, crepSimpProgHOL entry.2)
      have hmap : crepSimpMapcsHOL state = CrepSemHOLState.mapc update state := by
        cases state
        rfl
      have hvaluesSimp := crepOptMmapSimpExpCorrectNativeHOL
        update state values words hvalues
      rw [crepSimpProgHOL, evalCrepSemHOLProgExact_return_holShape, hmap,
        hvaluesSimp]
      rw [SimpProgCorrectReturnSupport.crepSimpMapcsHOL_emptyLocals]
      rw [← hmap]

end Flapjack
