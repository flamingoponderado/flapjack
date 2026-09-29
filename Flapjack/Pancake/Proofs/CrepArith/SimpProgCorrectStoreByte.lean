import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# `StoreByte` case of HOL `crep_arith$simp_prog_correct`

This module specializes HOL's `simp_prog_correct`
(`crep_arithProofScript.sml:184-212`) to the `StoreByte dst src` program
constructor.  HOL's `simp_prog` rewrites both stored expressions,
`simp_prog (StoreByte dst src) = StoreByte (simp_exp dst) (simp_exp src)`
(`crep_arithScript.sml:88`), and its `evaluate` clause evaluates both into
words and stores the low byte through the endian-aware `mem_store_byte`
(`crepSemScript.sml:281-287`):
`case (eval s dst, eval s src) of (SOME (Word adr), SOME (Word w)) =>
 (case mem_store_byte s.memory s.memaddrs s.be adr (w2w w) of
  SOME m => (NONE, s with memory := m) | NONE => (SOME Error, s)) | _ => (SOME Error, s)`.
The case keeps the source evaluation equation, the `result ≠ SOME Error` side
condition, and the target evaluation conclusion over the exact `CrepProgHOL`,
`CrepSemHOLState` and `CrepResultHOLExact` carriers.

Like `StoreGlob`, this case consumes the tagged exact `simp_exp_correct`
(`crepSimpExpCorrectNativeHOL`): the simplified address and value evaluate to
the same words under the shared code-map update, the resulting memory update
commutes with the code-only `mapcs`, and the `result ≠ SOME Error` side
condition discharges both failing arms (a failed expression evaluation or a
failed `mem_store_byte`).
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectStoreByteSupport

/-- Same-module canonical witness for the named finite-map fields on the
    `CrepSemHOLState` carrier used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectStoreByteSupport

/-- Flapjack-only commuting law: the proof script's local `mapcs` rendering
    changes only the code map, so it commutes with the exact `memory`
    update performed by the byte store. -/
theorem crepSimpMapcsHOL_withMemory {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (memory : BitVec width → HolWordLab width) :
    crepSimpMapcsHOL { state with memory := memory } =
      { crepSimpMapcsHOL state with memory := memory } := by
  cases state
  rfl

/-- The `StoreByte dst src` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`).  Its non-`Error` premise forces both
    source evaluations to have produced words and the exact
    `panMemStoreByteWord8HOL` store to have succeeded; the tagged exact
    `simp_exp_correct` transports both values across the code-only `mapcs`
    update, and the resulting memory update commutes with `mapcs`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectStoreByteCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (dst src : CrepExpHOL width)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.storeByte dst src : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.storeByte dst src : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  classical
  intro state dst src result finalState heval hresult
  have hsimp : crepSimpProgHOL (.storeByte dst src : CrepProgHOL width) =
      (.storeByte (crepSimpExpHOL dst) (crepSimpExpHOL src) : CrepProgHOL width) := by
    simp only [crepSimpProgHOL]
  rw [hsimp]
  rw [evalCrepSemHOLProgExact_storeByte_holShape] at heval ⊢
  cases hdst : evalCrepSemHOLExp state dst with
  | none =>
      rw [hdst] at heval
      exact absurd (Prod.ext_iff.mp heval).1.symm hresult
  | some dstValue =>
      cases hsrc : evalCrepSemHOLExp state src with
      | none =>
          rw [hdst, hsrc] at heval
          exact absurd (Prod.ext_iff.mp heval).1.symm hresult
      | some srcValue =>
          cases dstValue with
          | word adr =>
              cases srcValue with
              | word w =>
                  simp only [hdst, hsrc] at heval
                  cases hm : panMemStoreByteWord8HOL state.memory state.memaddrs
                      state.be adr (BitVec.ofNat 8 w.toNat) with
                  | none =>
                      simp only [hm] at heval
                      exact absurd (Prod.ext_iff.mp heval).1.symm hresult
                  | some newMemory =>
                      simp only [hm] at heval
                      obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp heval
                      have hr' : result = none := hr.symm
                      have hs'' : finalState = { state with memory := newMemory } := hs'.symm
                      subst hr'
                      subst hs''
                      have hdst' : evalCrepSemHOLExp (crepSimpMapcsHOL state)
                          (crepSimpExpHOL dst) = some (.word adr) := by
                        have h := crepSimpExpCorrectNativeHOL
                          (fun entry : MlString × (List Nat × CrepProgHOL width) =>
                            (entry.2.1, crepSimpProgHOL entry.2.2)) state dst
                          (.word adr) hdst
                        simpa [crepSimpMapcsHOL] using h
                      have hsrc' : evalCrepSemHOLExp (crepSimpMapcsHOL state)
                          (crepSimpExpHOL src) = some (.word w) := by
                        have h := crepSimpExpCorrectNativeHOL
                          (fun entry : MlString × (List Nat × CrepProgHOL width) =>
                            (entry.2.1, crepSimpProgHOL entry.2.2)) state src
                          (.word w) hsrc
                        simpa [crepSimpMapcsHOL] using h
                      have hmem : panMemStoreByteWord8HOL (crepSimpMapcsHOL state).memory
                          (crepSimpMapcsHOL state).memaddrs (crepSimpMapcsHOL state).be
                          adr (BitVec.ofNat 8 w.toNat) = some newMemory := hm
                      rw [hdst', hsrc']
                      simp only [hmem]
                      apply congrArg (fun s : CrepSemHOLState width σ => (none, s))
                      rw [crepSimpMapcsHOL_withMemory]
                      rfl

end Flapjack
