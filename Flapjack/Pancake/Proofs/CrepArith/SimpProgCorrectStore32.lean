import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# `Store32` case of HOL `crep_arith$simp_prog_correct`

This module specializes HOL's `simp_prog_correct`
(`crep_arithProofScript.sml:184-212`) to the `Store32 dst src` program
constructor.  HOL's `simp_prog` rewrites both stored operands,
`simp_prog (Store32 exp1 exp2) = Store32 (simp_exp exp1) (simp_exp exp2)`
(`crep_arithScript.sml:87`), and its `evaluate` clause is
`case (eval s dst, eval s src) of
  | (SOME (Word adr), SOME (Word w)) =>
      (case mem_store_32 s.memory s.memaddrs s.be adr (w2w w) of
        | SOME m => (NONE, s with memory := m)
        | NONE => (SOME Error, s))
  | _ => (SOME Error, s)`
(`crepSemScript.sml:274-280`).  The case keeps the source evaluation equation,
the `result ≠ SOME Error` side condition, and the target evaluation conclusion
over the exact `CrepProgHOL`, `CrepSemHOLState` and `CrepResultHOLExact`
carriers.

Unlike the leaf cases, this case consumes the tagged exact `simp_exp_correct`
(`crepSimpExpCorrectNativeHOL`): when the source evaluation of both operands
succeeds, the expression simplifier preserves their words under the shared
code-map update, and the code-only `mapcs` update commutes with the `memory`
update, so no target-result assumption is taken.  The memory-domain, alignment
and `Error` arms of HOL's `mem_store_32` are handled by the tagged exact
`evalCrepSemHOLProgExact_store32_holShape` clause, which delegates to the
reviewed `panMemStore32HOL` (`mem_store_32_def`).
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectStore32Support

/-- Same-module canonical witness for the named finite-map fields on the
    `CrepSemHOLState` carrier used by this HOL-shaped case theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectStore32Support

/-- Flapjack-only commuting law: the proof script's local `mapcs` rendering
    changes only the code map, so it commutes with an exact `memory` update. -/
theorem crepSimpMapcsHOL_setMemory {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (memory : BitVec width → HolWordLab width) :
    crepSimpMapcsHOL { state with memory := memory } =
      { crepSimpMapcsHOL state with memory := memory } := by
  cases state
  rfl

/-- The `Store32 dst src` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`).  Its non-`Error` premise forces the
    source `Store32` evaluation to have succeeded, and the tagged exact
    `simp_exp_correct` transports both evaluated operand words across the
    code-only `mapcs` update; the resulting `memory` update commutes with
    `mapcs`. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectStore32Case {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (dst src : CrepExpHOL width)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.store32 dst src : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.store32 dst src : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  classical
  intro state dst src result finalState heval hresult
  have hsimp : crepSimpProgHOL (.store32 dst src : CrepProgHOL width) =
      (.store32 (crepSimpExpHOL dst) (crepSimpExpHOL src) : CrepProgHOL width) := by
    simp only [crepSimpProgHOL]
  rw [hsimp]
  rw [evalCrepSemHOLProgExact_store32_holShape] at heval
  cases hdst : evalCrepSemHOLExp state dst with
  | none =>
      simp only [hdst] at heval
      exact absurd (Prod.ext_iff.mp heval).1.symm hresult
  | some vdst =>
    cases vdst with
    | word adr =>
      cases hsrc : evalCrepSemHOLExp state src with
      | none =>
          simp only [hdst, hsrc] at heval
          exact absurd (Prod.ext_iff.mp heval).1.symm hresult
      | some vsrc =>
        cases vsrc with
        | word w =>
          cases hm : panMemStore32HOL state.memory state.memaddrs state.be adr
              (BitVec.ofNat 32 w.toNat) with
          | none =>
              simp only [hdst, hsrc, hm] at heval
              exact absurd (Prod.ext_iff.mp heval).1.symm hresult
          | some m =>
              simp only [hdst, hsrc, hm] at heval
              obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp heval
              have hr' : result = none := hr.symm
              have hs'' : finalState = { state with memory := m } := hs'.symm
              subst hr'
              subst hs''
              have hmapDst : evalCrepSemHOLExp (crepSimpMapcsHOL state)
                  (crepSimpExpHOL dst) = some (.word adr) := by
                have hsimpExp := crepSimpExpCorrectNativeHOL
                  (fun entry : MlString × (List Nat × CrepProgHOL width) =>
                    (entry.2.1, crepSimpProgHOL entry.2.2)) state dst (.word adr) hdst
                simpa [crepSimpMapcsHOL] using hsimpExp
              have hmapSrc : evalCrepSemHOLExp (crepSimpMapcsHOL state)
                  (crepSimpExpHOL src) = some (.word w) := by
                have hsimpExp := crepSimpExpCorrectNativeHOL
                  (fun entry : MlString × (List Nat × CrepProgHOL width) =>
                    (entry.2.1, crepSimpProgHOL entry.2.2)) state src (.word w) hsrc
                simpa [crepSimpMapcsHOL] using hsimpExp
              have hstore : panMemStore32HOL (crepSimpMapcsHOL state).memory
                  (crepSimpMapcsHOL state).memaddrs (crepSimpMapcsHOL state).be adr
                  (BitVec.ofNat 32 w.toNat) = some m := by
                rw [crepSimpMapcsHOL]
                exact hm
              simp only [evalCrepSemHOLProgExact_store32_holShape, hmapDst, hmapSrc,
                hstore, crepSimpMapcsHOL_setMemory]

end Flapjack
