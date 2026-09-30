import Flapjack.Compiler.Backend.Semantics.WordSem.EventsMono

/-! Exact counterpart of wordPropsScript.sml's evaluate_io_events_mono. -/

namespace Flapjack

namespace WordSemEventsMonoSupport

/-- Canonical roundtrip witness for the exact evaluator's finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEventsMonoSupport

namespace WordSemStateFiniteExact

/-- Exact HOL event monotonicity over the faithful wordSem evaluator. The
    projection induction follows HOL's evaluator cases; there are no
    additional assumptions on the program, state, result or FFI oracle. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "evaluate_io_events_mono"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_io_events_mono {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (exps : WordLangProgHOL (BitVec width)) (s1 : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (s2 : WordSemStateFiniteExact width C F),
      evaluate exps s1 = (res, s2) → s1.ffi.ioEvents <+: s2.ffi.ioEvents := by
  intro exps s1 res s2 h
  have hp := evaluate_ioEvents_prefix exps s1
  rw [h] at hp
  exact hp

end WordSemStateFiniteExact

end Flapjack
