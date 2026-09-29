import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# Assign case of HOL `crep_arith$simp_prog_correct`

This counterpart submodule contains the exact nonrecursive `Assign` case.
The local `mapcs` transformation maps stored code bodies, while the evaluator's
assignment updates locals; those state fields are disjoint. The proof uses the
exact tagged `simp_exp_correct` theorem to preserve the assigned word.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectAssignSupport

/-- Same-module canonical finite-support witness for the named state fields
    used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectAssignSupport

/-- The `Assign` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`). Its source equation and non-Error
    premise imply successful expression evaluation and an existing local
    binding. The tagged `simp_exp_correct` preserves the assigned word after
    `mapcs`; the local update commutes with this code-only map. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectAssignCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (name : Nat) (src : CrepExpHOL width)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.assign name src : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.assign name src : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  intro state name src result finalState heval hresult
  rw [evalCrepSemHOLProgExact_assign_holShape] at heval
  cases hsrc : evalCrepSemHOLExp state src with
  | none =>
      simp [hsrc] at heval
      exact False.elim (hresult heval.1.symm)
  | some value =>
      cases hlocal : state.locals.lookup name with
      | none =>
          simp [hsrc, hlocal] at heval
          exact False.elim (hresult heval.1.symm)
      | some oldValue =>
          simp only [hsrc, hlocal] at heval
          cases heval
          let update : MlString × (List Nat × CrepProgHOL width) →
              List Nat × CrepProgHOL width :=
              fun (_, entry) => (entry.1, crepSimpProgHOL entry.2)
          have hcode : state.code.map2 update = state.code.map2
              (fun (_, entry) => (entry.1, crepSimpProgHOL entry.2)) := by
            cases state.code with
            | mk lookup support =>
                simp only [HolFiniteMapExact.map2]
                congr 1
          have hmap : crepSimpMapcsHOL state = CrepSemHOLState.mapc update state := by
            cases state
            simp only [crepSimpMapcsHOL, CrepSemHOLState.mapc]
            congr 1
          have hexp := crepSimpExpCorrectNativeHOL update state src value hsrc
          rw [crepSimpProgHOL, evalCrepSemHOLProgExact_assign_holShape, hmap, hexp]
          simp [CrepSemHOLState.mapc, crepSimpMapcsHOL, hlocal]
          rw [hcode]

end Flapjack
