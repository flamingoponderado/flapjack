import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Leaves
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

/-!
# `evaluate_stack_swap` `MustTerminate` case

The `MustTerminate` case of `wordPropsScript.sml:2316-2363`
`evaluate_stack_swap` (proof `wordPropsScript.sml:2449-2460`), with the
induction hypothesis of HOL `evaluate_ind`. The untagged helpers are Flapjack
proof infrastructure for the tagged case.
-/

namespace Flapjack

namespace WordSemStackEq

open WordSemStateFiniteExact

section MustTerminateCase

variable {width : Nat} [NeZero width] {C F : Type}

/-- The `MustTerminate` post-processing of a body run: a `TimeOut` becomes an
`Error` at the initial state, every other result restores the clock and
termination depth. -/
def mtPost (s : WordSemStateFiniteExact width C F)
    (r : Option (WordSemResult width) × WordSemStateFiniteExact width C F) :
    Option (WordSemResult width) × WordSemStateFiniteExact width C F :=
  match r with
  | (some .timeOut, _) => (some .error, s)
  | (res, s1) => (res, { s1 with clock := s.clock, termdep := s.termdep })

theorem evaluate_mustTerminate_eq (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (hz : ¬ s.termdep = 0) :
    evaluate (.mustTerminate p) s =
      mtPost s (evaluate p { s with clock := wordSemMustTerminateLimit width,
                                    termdep := s.termdep - 1 }) := by
  rw [evaluate, dif_neg hz]
  generalize evaluate p _ = r
  rcases r with ⟨res, s1⟩
  rcases res with _ | r
  · rfl
  · cases r <;> rfl

/-- The `evaluate_stack_swap` conclusion survives the `MustTerminate`
post-processing. -/
theorem stackSwapRel_mt (s : WordSemStateFiniteExact width C F)
    (r : Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (E : List (WordSemStackFrame width) →
      Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (hr : stackSwapRel { s with clock := wordSemMustTerminateLimit width,
                                termdep := s.termdep - 1 } r E) :
    stackSwapRel s (mtPost s r) (fun xs => mtPost { s with stack := xs } (E xs)) := by
  rcases r with ⟨res, s1⟩
  rcases res with _ | res
  · obtain ⟨hk, hh, hx⟩ := hr
    refine ⟨hk, hh, fun xs hxs => ?_⟩
    obtain ⟨st, he, hv, hkx⟩ := hx xs hxs
    exact ⟨st, by dsimp only; rw [he]; rfl, hv, hkx⟩
  · cases res with
    | error => trivial
    | timeOut => trivial
    | notEnoughSpace =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, fun xs hxs => by dsimp only; rw [hx xs hxs]; rfl⟩
    | finalFfi e =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, fun xs hxs => by dsimp only; rw [hx xs hxs]; rfl⟩
    | exception x y =>
        obtain ⟨hlt, e0, e, n, ls, m, lss, hl, hm, hloc, hks, hhn, hx⟩ := hr
        refine ⟨hlt, e0, e, n, ls, m, lss, hl, hm, hloc, hks, hhn, fun xs e0' e' ls' h => ?_⟩
        obtain ⟨st, locs, he, rest⟩ := hx xs e0' e' ls' h
        exact ⟨st, locs, by dsimp only; rw [he]; rfl, rest⟩
    | result v vs =>
        obtain ⟨hk, hh, hx⟩ := hr
        refine ⟨hk, hh, fun xs hxs => ?_⟩
        obtain ⟨st, he, hv, hkx⟩ := hx xs hxs
        exact ⟨st, by dsimp only; rw [he]; rfl, hv, hkx⟩
    | «break» k =>
        obtain ⟨hk, hh, hx⟩ := hr
        refine ⟨hk, hh, fun xs hxs => ?_⟩
        obtain ⟨st, he, hv, hkx⟩ := hx xs hxs
        exact ⟨st, by dsimp only; rw [he]; rfl, hv, hkx⟩
    | «continue» k =>
        obtain ⟨hk, hh, hx⟩ := hr
        refine ⟨hk, hh, fun xs hxs => ?_⟩
        obtain ⟨st, he, hv, hkx⟩ := hx xs hxs
        exact ⟨st, by dsimp only; rw [he]; rfl, hv, hkx⟩

end MustTerminateCase

namespace EvaluateStackSwapMustTerminateWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateStackSwapMustTerminateWitnesses

open EvaluateStackSwapMustTerminateWitnesses

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `MustTerminate`
case (proof `wordPropsScript.sml:2449-2460`): the HOL conclusion at
`MustTerminate p`, from exactly HOL `evaluate_ind`'s `MustTerminate` induction
hypothesis (the body at the reset clock and decremented termination depth when
that depth is nonzero); no extra premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackSwap_MustTerminate {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) :
    ∀ s : WordSemStateFiniteExact width C F,
      (s.termdep ≠ 0 →
        stackSwapPost p { s with clock := wordSemMustTerminateLimit width,
                                 termdep := s.termdep - 1 }) →
      stackSwapPost (.mustTerminate p) s := by
  intro s ih
  rw [stackSwapPost_iff]
  by_cases hz : s.termdep = 0
  · rw [evaluate, dif_pos hz]
    trivial
  · have hr := (stackSwapPost_iff _ _).mp (ih hz)
    rw [evaluate_mustTerminate_eq p s hz]
    have e2 : (fun xs => evaluate (.mustTerminate p) { s with stack := xs }) =
        fun xs => mtPost { s with stack := xs }
          (evaluate p { { s with clock := wordSemMustTerminateLimit width,
                                 termdep := s.termdep - 1 } with stack := xs }) :=
      funext fun xs => evaluate_mustTerminate_eq p { s with stack := xs } hz
    rw [e2]
    exact stackSwapRel_mt s _ _ hr

end WordSemStackEq

end Flapjack
