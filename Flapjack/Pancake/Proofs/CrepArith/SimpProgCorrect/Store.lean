import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

/-!
# Store case of HOL `crep_arith$simp_prog_correct`

This counterpart covers the word-width `Store` constructor.  It retains the
source evaluator equation and non-Error premise, and follows the exact
`mem_store` success/domain-failure split in Crep's evaluator.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectStoreSupport

/-- Same-module canonical finite-support witness for the named state fields
    used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectStoreSupport

/-- The `Store dst src` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:186-212`).  Successful source evaluation and
    the non-Error premise force both expressions and the `mem_store` update to
    succeed.  `simp_exp_correct` preserves the address and stored word after
    `mapcs`; the target still follows the evaluator's memory-domain branch. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectStoreCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (dst src : CrepExpHOL width)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.store dst src : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.store dst src : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  classical
  intro state dst src result finalState heval hresult
  rw [evalCrepSemHOLProgExact_store_holShape] at heval
  let update : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width :=
      fun (_, entry) => (entry.1, crepSimpProgHOL entry.2)
  have hmap : crepSimpMapcsHOL state = CrepSemHOLState.mapc update state := by
    cases state
    simp only [crepSimpMapcsHOL, CrepSemHOLState.mapc]
    congr 1
  cases hdst : evalCrepSemHOLExp state dst with
  | none =>
      simp [hdst] at heval
      exact False.elim (hresult (by simpa using heval.1.symm))
  | some address =>
      cases hsrc : evalCrepSemHOLExp state src with
      | none =>
          simp [hdst, hsrc] at heval
          exact False.elim (hresult (by simpa using heval.1.symm))
      | some value =>
          cases address with
          | word address =>
              have hdstSimp :
                  evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
                      (crepSimpExpHOL dst) = some (.word address) :=
                crepSimpExpCorrectNativeHOL update state dst (.word address) hdst
              have hsrcSimp :
                  evalCrepSemHOLExp (CrepSemHOLState.mapc update state)
                      (crepSimpExpHOL src) = some value :=
                crepSimpExpCorrectNativeHOL update state src value hsrc
              cases hstore : panMemStoreHOL address value state.memaddrs state.memory with
              | none =>
                  simp [hdst, hsrc, hstore] at heval
                  exact False.elim (hresult (by simpa using heval.1.symm))
              | some nextMemory =>
                  simp only [hdst, hsrc, hstore] at heval
                  rcases Prod.mk.inj heval with ⟨rfl, rfl⟩
                  have hmapStore :
                      CrepSemHOLState.mapc update {state with memory := nextMemory} =
                        {CrepSemHOLState.mapc update state with memory := nextMemory} := by
                    cases state
                    rfl
                  have hmapFinal :
                      crepSimpMapcsHOL {state with memory := nextMemory} =
                        CrepSemHOLState.mapc update {state with memory := nextMemory} := by
                    cases state
                    rfl
                  rw [crepSimpProgHOL, evalCrepSemHOLProgExact_store_holShape, hmap]
                  simp only [hdstSimp, hsrcSimp]
                  rw [hstore, hmapFinal, hmapStore]

end Flapjack
