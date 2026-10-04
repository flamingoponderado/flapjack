import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Leaves
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

/-!
# `evaluate_stack_swap` `Seq` case

The `Seq` case of `wordPropsScript.sml:2316-2363` `evaluate_stack_swap`
(proof `wordPropsScript.sml:2461-2508`), with the induction hypotheses of HOL
`evaluate_ind`. The untagged helpers are Flapjack proof infrastructure for the
tagged case.
-/

namespace Flapjack

namespace WordSemStackEq

open WordSemStateFiniteExact

section SeqCase

variable {width : Nat} [NeZero width] {C F : Type}

/-- A run with a non-`NONE` result keeps its `evaluate_stack_swap` conclusion
when the swapped runs are changed only where their result is `NONE`. -/
theorem stackSwapRel_mono (s : WordSemStateFiniteExact width C F)
    (r : Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (E E' : List (WordSemStackFrame width) →
      Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (hr : stackSwapRel s r E) (hE : ∀ xs, (E xs).1 ≠ none → E' xs = E xs)
    (hn : r.1 ≠ none) : stackSwapRel s r E' := by
  rcases r with ⟨res, s1⟩
  rcases res with _ | res
  · exact absurd rfl hn
  · have hE' : ∀ xs t, E xs = (some res, t) → E' xs = (some res, t) := by
      intro xs t h
      rw [hE xs (by rw [h]; simp), h]
    cases res with
    | error => trivial
    | timeOut =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, fun xs hxs => hE' xs _ (hx xs hxs)⟩
    | notEnoughSpace =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, fun xs hxs => hE' xs _ (hx xs hxs)⟩
    | finalFfi e =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, fun xs hxs => hE' xs _ (hx xs hxs)⟩
    | exception x y =>
        obtain ⟨hlt, e0, e, n, ls, m, lss, hl, hm, hloc, hks, hhn, hx⟩ := hr
        refine ⟨hlt, e0, e, n, ls, m, lss, hl, hm, hloc, hks, hhn, fun xs e0' e' ls' h => ?_⟩
        obtain ⟨st, locs, he, rest⟩ := hx xs e0' e' ls' h
        exact ⟨st, locs, hE' xs _ he, rest⟩
    | result v vs =>
        obtain ⟨a, b, hx⟩ := hr
        refine ⟨a, b, fun xs hxs => ?_⟩
        obtain ⟨st, he, rest⟩ := hx xs hxs
        exact ⟨st, hE' xs _ he, rest⟩
    | «break» k =>
        obtain ⟨a, b, hx⟩ := hr
        refine ⟨a, b, fun xs hxs => ?_⟩
        obtain ⟨st, he, rest⟩ := hx xs hxs
        exact ⟨st, hE' xs _ he, rest⟩
    | «continue» k =>
        obtain ⟨a, b, hx⟩ := hr
        refine ⟨a, b, fun xs hxs => ?_⟩
        obtain ⟨st, he, rest⟩ := hx xs hxs
        exact ⟨st, hE' xs _ he, rest⟩

/-- The second statement of a sequence, run from a key-equal stack with the
same handler, gives the conclusion at the sequence's initial state. -/
theorem stackSwapRel_seqTail (s s1 : WordSemStateFiniteExact width C F)
    (r : Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (E E2 : List (WordSemStackFrame width) →
      Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (hr : stackSwapRel s1 r E2) (hk : sKeyEq s.stack s1.stack) (hh : s1.handler = s.handler)
    (hE : ∀ xs, sValEq s.stack xs → ∃ st, E xs = E2 st ∧ sValEq s1.stack st ∧ sKeyEq xs st) :
    stackSwapRel s r E := by
  rcases r with ⟨res, s2⟩
  have hother : sKeyEq s1.stack s2.stack → s2.handler = s1.handler →
      (∀ ys, sValEq s1.stack ys → ∃ st, E2 ys = (res, { s2 with stack := st }) ∧
        sValEq s2.stack st ∧ sKeyEq ys st) →
      sKeyEq s.stack s2.stack ∧ s2.handler = s.handler ∧
        ∀ xs, sValEq s.stack xs → ∃ st, E xs = (res, { s2 with stack := st }) ∧
          sValEq s2.stack st ∧ sKeyEq xs st := by
    intro hk2 hh2 hx2
    refine ⟨sKeyEqTrans _ _ _ ⟨hk, hk2⟩, hh2.trans hh, fun xs hxs => ?_⟩
    obtain ⟨st, hE', hv, hkx⟩ := hE xs hxs
    obtain ⟨st2, he2, hv2, hk2'⟩ := hx2 st hv
    exact ⟨st2, hE'.trans he2, hv2, sKeyEqTrans _ _ _ ⟨hkx, hk2'⟩⟩
  have hflush : ∀ q, (∀ ys, sValEq s1.stack ys → E2 ys = q) →
      ∀ xs, sValEq s.stack xs → E xs = q := by
    intro q hx xs hxs
    obtain ⟨st, hE', hv, -⟩ := hE xs hxs
    exact hE'.trans (hx st hv)
  rcases res with _ | res
  · obtain ⟨hk2, hh2, hx2⟩ := hr
    exact hother hk2 hh2 hx2
  · cases res with
    | error => trivial
    | timeOut =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, hflush _ hx⟩
    | notEnoughSpace =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, hflush _ hx⟩
    | finalFfi e =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, hflush _ hx⟩
    | result v vs =>
        obtain ⟨hk2, hh2, hx2⟩ := hr
        exact hother hk2 hh2 hx2
    | «break» k =>
        obtain ⟨hk2, hh2, hx2⟩ := hr
        exact hother hk2 hh2 hx2
    | «continue» k =>
        obtain ⟨hk2, hh2, hx2⟩ := hr
        exact hother hk2 hh2 hx2
    | exception x y =>
        obtain ⟨hlt, e0, e, n, ls, m, lss, hl, hm, ⟨hfe, hloc⟩, hks, hhn, hx⟩ := hr
        have hlen := sKeyEqLength _ _ hk
        obtain ⟨e', ls', hl', hfe', hkls⟩ := sKeyEqLastNExists s1.stack s.stack
          (s1.handler + 1) m e0 e n ls ⟨(sKeyEqSym _ _).mp hk, hl⟩
        refine ⟨?_, e0, e', n, ls', m, lss, ?_, hm, ⟨hfe'.trans hfe, hloc⟩,
          sKeyEqTrans _ _ _ ⟨hks, hkls⟩, hhn, ?_⟩
        · rw [← hh, hlen]; exact hlt
        · rw [← hh]; exact hl'
        · rintro xs e0x ex lsx ⟨hlx, hxs⟩
          obtain ⟨st, hE', hv, hkx⟩ := hE xs hxs
          obtain ⟨e3, ls3, hlst, hfe3, hk3⟩ := sKeyEqLastNExists xs st
            (s.handler + 1) m e0x ex n lsx ⟨hkx, hlx⟩
          rw [← hh] at hlst
          obtain ⟨st2, locs, he2, ⟨lss', hf2, hloc2, hsnd⟩, hv2, hk2⟩ :=
            hx st e0x e3 ls3 ⟨hlst, hv⟩
          exact ⟨st2, locs, hE'.trans he2, ⟨lss', hfe3.symm.trans hf2, hloc2, hsnd⟩, hv2,
            sKeyEqTrans _ _ _ ⟨hk3, hk2⟩⟩

end SeqCase

namespace EvaluateStackSwapSeqWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateStackSwapSeqWitnesses

open EvaluateStackSwapSeqWitnesses

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Seq` case
(proof `wordPropsScript.sml:2461-2508`): the HOL conclusion at `Seq c1 c2`,
from exactly HOL `evaluate_ind`'s two `Seq` induction hypotheses (the second
statement from every `NONE`-result state of the first, and the first statement
at `s`); no extra premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackSwap_Seq {width : Nat} [NeZero width] {C F : Type}
    (c1 c2 : WordLangProgHOL (BitVec width)) :
    ∀ s : WordSemStateFiniteExact width C F,
      (∀ res s1, (res, s1) = evaluate c1 s ∧ res = none → stackSwapPost c2 s1) ∧
        stackSwapPost c1 s →
      stackSwapPost (.seq c1 c2) s := by
  rintro s ⟨ih2, ih1⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [stackSwapPost_iff] at ih1 ⊢
  simp only [ht]
  rcases he1 : evaluate c1 s with ⟨r1, s1⟩
  rw [he1] at ih1
  cases r1 with
  | none =>
    obtain ⟨hk, hh, hx⟩ := ih1
    have ih2' := (stackSwapPost_iff _ _).mp (ih2 none s1 ⟨he1.symm, rfl⟩)
    refine stackSwapRel_seqTail s s1 _ _ _ ih2' hk hh (fun xs hxs => ?_)
    obtain ⟨st, he, hv, hkx⟩ := hx xs hxs
    dsimp only at he
    exact ⟨st, by rw [he], hv, hkx⟩
  | some r =>
    refine stackSwapRel_mono s _ _ _ ih1 (fun xs hne => ?_) (by simp)
    rcases h : evaluate c1 { s with stack := xs } with ⟨r', t⟩
    rw [h] at hne
    cases r' with
    | none => exact absurd rfl hne
    | some _ => rfl

end WordSemStackEq

end Flapjack
