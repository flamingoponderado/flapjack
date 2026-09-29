import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# `StoreGlob` case of HOL `crep_arith$simp_prog_correct`

This module specializes HOL's `simp_prog_correct`
(`crep_arithProofScript.sml:184-212`) to the `StoreGlob dst src` program
constructor.  HOL's `simp_prog` rewrites the stored expression,
`simp_prog (StoreGlob g exp) = StoreGlob g (simp_exp exp)`
(`crep_arithScript.sml:89`), and its `evaluate` clause is
`case eval s src of SOME w => (NONE, set_globals dst w s) | _ => (SOME Error, s)`
(`crepSemScript.sml:288-291`).  The case keeps the source evaluation equation,
the `result ≠ SOME Error` side condition, and the target evaluation
conclusion over the exact `CrepProgHOL`, `CrepSemHOLState` and
`CrepResultHOLExact` carriers.

Unlike the leaf cases, this case consumes the tagged exact `simp_exp_correct`
(`crepSimpExpCorrectNativeHOL`): when the source evaluation of `src` succeeds,
the expression simplifier preserves its value under the shared code-map update,
and the code-only `mapcs` update commutes with `set_globals`, so no
target-result assumption is taken.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectStoreGlobSupport

/-- Same-module canonical witness for the named finite-map fields on the
    `CrepSemHOLState` carrier used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectStoreGlobSupport

/-- Flapjack-only commuting law: the proof script's local `mapcs` rendering
    changes only the code map, so it commutes with the exact `set_globals`
    update. -/
theorem crepSimpMapcsHOL_setGlobals {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (dst : BitVec 5) (value : HolWordLab width) :
    crepSimpMapcsHOL (CrepSemHOLState.setGlobals dst value state) =
      CrepSemHOLState.setGlobals dst value (crepSimpMapcsHOL state) := by
  cases state
  rfl

/-- The `StoreGlob dst src` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`).  Its non-`Error` premise forces the
    source `StoreGlob` evaluation to have succeeded, and the tagged exact
    `simp_exp_correct` transports the evaluated source value across the
    code-only `mapcs` update; the resulting globals update commutes with
    `mapcs`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectStoreGlobCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (dst : BitVec 5) (src : CrepExpHOL width)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.storeGlob dst src : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.storeGlob dst src : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  intro state dst src result finalState heval hresult
  have hsimp : crepSimpProgHOL (.storeGlob dst src : CrepProgHOL width) =
      (.storeGlob dst (crepSimpExpHOL src) : CrepProgHOL width) := by
    simp only [crepSimpProgHOL]
  rw [hsimp]
  rw [evalCrepSemHOLProgExact_storeGlob_holShape] at heval ⊢
  rcases hsrc : evalCrepSemHOLExp state src with _ | value
  · rw [hsrc] at heval
    exact absurd (Prod.ext_iff.mp heval).1.symm hresult
  · rw [hsrc] at heval
    obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp heval
    have hr' : result = none := hr.symm
    have hs'' : finalState = CrepSemHOLState.setGlobals dst value state := hs'.symm
    subst hr'
    subst hs''
    have hmap : evalCrepSemHOLExp (crepSimpMapcsHOL state) (crepSimpExpHOL src) =
        some value := by
      have hsimpExp := crepSimpExpCorrectNativeHOL
        (fun entry : MlString × (List Nat × CrepProgHOL width) =>
          (entry.2.1, crepSimpProgHOL entry.2.2)) state src value hsrc
      simpa [crepSimpMapcsHOL] using hsimpExp
    rw [hmap, crepSimpMapcsHOL_setGlobals]

end Flapjack
