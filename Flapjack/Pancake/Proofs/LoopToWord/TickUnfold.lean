import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

/-!
# `loop_to_wordProof` `Tick` unfolding lemmas

Counterpart of `cakeml/pancake/proofs/loop_to_wordProofScript.sml:510-531`
(bead `flapjack-pxn.18.5.9.20.2`).  These are the two local wordSem unfolding
lemmas used by the `Loop` cases of `compile_correct`.  `loop_to_word` compiles
a `Loop` to `Seq Tick (Seq (Loop ...) Tick)`.  Both lemmas are stated over the
tagged exact wordSem `evaluate` (`WordSemStateFiniteExact.evaluate`).
-/

namespace Flapjack

namespace LoopToWordTickUnfoldSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LoopToWordTickUnfoldSupport

namespace WordSemStateFiniteExact

/-- Exact HOL `evaluate_tick_unfold` (`loop_to_wordProofScript.sml:510-515`):

    ```
    evaluate (Tick, s) = if s.clock = 0 then (SOME TimeOut, flush_state T s)
                         else (NONE, dec_clock s)
    ```

    HOL's free `s` is a parameter. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_tick_unfold {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.tick) s =
      if s.clock = 0 then (some .timeOut, flushState true s) else (none, decClock s) := by
  rw [evaluate]

open Classical in
/-- Exact HOL `evaluate_tick_loop_tick_unfold`
    (`loop_to_wordProofScript.sml:517-531`):

    ```
    t1.clock ≠ 0 ⇒
    evaluate (Seq Tick (Seq (Loop names body exit_names) Tick), t1) =
    (λ(res',s1).
       if res' = NONE then
         if s1.clock = 0 then (SOME TimeOut, flush_state T s1)
         else (NONE, s1 with clock := s1.clock − 1)
       else (res', s1))
      (evaluate (Loop names body exit_names, t1 with clock := t1.clock − 1))
    ```

    HOL's free `t1`, `names`, `body` and `exit_names` are parameters.  The
    paired lambda is a `match` on the pair.  HOL's `res' = NONE` is decided
    classically, because `WordSemResult` has no `DecidableEq`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_tick_loop_tick_unfold {width : Nat} [NeZero width] {C : Type} {F : Type}
    (t1 : WordSemStateFiniteExact width C F) (names : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec width)) (exit_names : WordLangNumSetHOL) :
    t1.clock ≠ 0 →
    evaluate (.seq .tick (.seq (.loop names body exit_names) .tick)) t1 =
      (fun (p : Option (WordSemResult width) × WordSemStateFiniteExact width C F) =>
        match p with
        | (res', s1) =>
          if res' = none then
            if s1.clock = 0 then (some .timeOut, flushState true s1)
            else (none, { s1 with clock := s1.clock - 1 })
          else (res', s1))
        (evaluate (.loop names body exit_names) { t1 with clock := t1.clock - 1 }) := by
  intro h
  rw [evaluate_def_rebound.2.2.2.2.2.2.2.2.2.2.2.2.1, evaluate_tick_unfold, if_neg h]
  simp only [evaluate_def_rebound.2.2.2.2.2.2.2.2.2.2.2.2.1, decClock]
  rcases evaluate (.loop names body exit_names) { t1 with clock := t1.clock - 1 } with ⟨res, s1⟩
  cases res with
  | none => simp [evaluate_tick_unfold, decClock]
  | some r => simp

end WordSemStateFiniteExact

end Flapjack
