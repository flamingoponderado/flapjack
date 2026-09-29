import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# `Primitive` and `Raise` cases of HOL `crep_arith$simp_prog_correct`

The two cases below specialize HOL's `simp_prog_correct` predicate to the
`Primitive lhss pop rhss` and `Raise eid` program constructors.  Both retain
the source evaluation equation, the `result ≠ SOME Error` side condition, and
the target evaluation conclusion, over the exact `CrepProgHOL`,
`CrepSemHOLState`, and `CrepResultHOLExact` carriers and the tagged exact
`crepSimpProgHOL`.  Neither case needs `simp_exp_correct`, and neither takes a
target-result assumption: the post-state equality is derived from the source
equation together with the fact that `mapcs` changes only the code map.

HOL's `mapcs` is only a local overload in `crep_arithProofScript.sml:160`
(`mapc (λ(key, (params, body)). (params, simp_prog body))`), and `mapc` applies
`FMAP_MAP2` to the state's code map (`crep_arithProofScript.sml:109-110`).  It
has no named HOL declaration to tag, so the finite-support state update below
is untagged Flapjack support.  It is given a slice-local name so that it
coexists with the leaf-case scaffold in `SimpProgCorrect.lean`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

namespace SimpProgCorrectPrimitiveRaiseSupport

/-- Same-module canonical witness for the named finite-map fields on the
    `CrepSemHOLState` carrier used by these HOL-shaped case theorems. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end SimpProgCorrectPrimitiveRaiseSupport

/-- The `Primitive lhss pop rhss` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`).  Its non-`Error` premise forces the
    three HOL guard conjuncts; the resulting locals update is independent of the
    code map that `mapcs` rewrites. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectPrimitiveCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (names : List Nat) (operator : PrimOp)
      (args : List Nat)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.primitive names operator args : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.primitive names operator args : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  intro state names operator args result finalState heval hresult
  have hsimp : crepSimpProgHOL (.primitive names operator args : CrepProgHOL width) =
      (.primitive names operator args : CrepProgHOL width) := by
    simp only [crepSimpProgHOL]
  rw [hsimp]
  rw [evalCrepSemHOLProgExact_primitive] at heval ⊢
  rw [show (crepSimpMapcsHOL state).locals = state.locals from rfl] at ⊢
  rcases hargs : args.mapM state.locals.lookup with _ | ws
  · simp only [hargs] at heval ⊢
    exact absurd (Prod.ext_iff.mp heval).1.symm hresult
  · rcases hop : crepPrimopHOLExact operator ws with _ | results
    · simp only [hargs, hop] at heval ⊢
      exact absurd (Prod.ext_iff.mp heval).1.symm hresult
    · simp only [hargs, hop] at heval ⊢
      by_cases hg :
          (decide (names.length = results.length) &&
            names.all (fun v => (state.locals.lookup v).isSome) &&
            decide names.Nodup) = true
      · rw [if_pos hg] at heval ⊢
        obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp heval
        have hr' : result = none := hr.symm
        have hs'' : finalState =
            { state with locals := state.locals.updateListEq (names.zip results) } := hs'.symm
        subst hr'
        subst hs''
        rfl
      · rw [if_neg hg] at heval ⊢
        exact absurd (Prod.ext_iff.mp heval).1.symm hresult

/-- The `Raise eid` specialization of HOL `simp_prog_correct`
    (`crep_arithProofScript.sml:184-212`).  HOL raises `Result.Exception eid`
    and clears locals, both untouched by the code-only `mapcs` update. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "simp_prog_correct"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem simpProgCorrectRaiseCase {width : Nat} [NeZero width] {σ : Type} :
    ∀ (state : CrepSemHOLState width σ) (exception : BitVec width)
      (result : Option (CrepResultHOLExact width))
      (finalState : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact state (.raise exception : CrepProgHOL width) =
          (result, finalState) →
      result ≠ some .error →
      evalCrepSemHOLProgExact (crepSimpMapcsHOL state)
          (crepSimpProgHOL (.raise exception : CrepProgHOL width)) =
        (result, crepSimpMapcsHOL finalState) := by
  intro state exception result finalState heval _hresult
  have hsimp : crepSimpProgHOL (.raise exception : CrepProgHOL width) =
      (.raise exception : CrepProgHOL width) := by
    simp only [crepSimpProgHOL]
  rw [hsimp]
  rw [evalCrepSemHOLProgExact_raise] at heval
  obtain ⟨hr, hs'⟩ := Prod.ext_iff.mp heval
  have hr' : result = some (.exception exception) := hr.symm
  have hs'' : finalState = CrepSemHOLState.emptyLocals state := hs'.symm
  subst hr'
  subst hs''
  rw [evalCrepSemHOLProgExact_raise]
  rfl

end Flapjack
