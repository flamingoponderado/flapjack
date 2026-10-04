import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap.Seq

/-!
# `evaluate_stack_swap` `Loop` case

The `Loop` case of `wordPropsScript.sml:2316-2363` `evaluate_stack_swap`
(proof `wordPropsScript.sml:2533-2833`), with the induction hypotheses of HOL
`evaluate_ind`. The untagged helpers are Flapjack proof infrastructure for the
tagged case.
-/

namespace Flapjack

namespace WordSemStackEq

open WordSemStateFiniteExact

section LoopCase

variable {width : Nat} [NeZero width] {C F : Type}

/-- Cutting the locals does not read the stack. -/
theorem cutState_withStack (names : WordLangCutsetsHOL) (t : WordSemStateFiniteExact width C F)
    (xs : List (WordSemStackFrame width)) :
    cutState names { t with stack := xs } =
      (cutState names t).map (fun v => { v with stack := xs }) := by
  simp only [cutState]
  cases wordSemCutEnv names t.locals <;> rfl

theorem cutState_stack_handler (names : WordLangCutsetsHOL)
    (t v : WordSemStateFiniteExact width C F) (h : cutState names t = some v) :
    v.stack = t.stack ∧ v.handler = t.handler := by
  unfold cutState at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- A body result that leaves the loop (`exit_loop`) keeps the
`evaluate_stack_swap` conclusion, moved from the cut state to the loop's
initial state (same stack and handler). -/
theorem stackSwapRel_exitLoop (s x : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
    (E E' : List (WordSemStackFrame width) →
      Option (WordSemResult width) × WordSemStateFiniteExact width C F)
    (hr : stackSwapRel x (res, s1) E) (hxs : x.stack = s.stack) (hxh : x.handler = s.handler)
    (hcl : wordSemContLoop res = false)
    (hE : ∀ xs t, E xs = (res, t) → E' xs = (wordSemExitLoop res, t)) :
    stackSwapRel s (wordSemExitLoop res, s1) E' := by
  have hv : ∀ xs, sValEq s.stack xs → sValEq x.stack xs := fun xs h => by rw [hxs]; exact h
  have hother : ∀ res' : Option (WordSemResult width), wordSemExitLoop res = res' →
      sKeyEq x.stack s1.stack → s1.handler = x.handler →
      (∀ ys, sValEq x.stack ys → ∃ st, E ys = (res, { s1 with stack := st }) ∧
        sValEq s1.stack st ∧ sKeyEq ys st) →
      sKeyEq s.stack s1.stack ∧ s1.handler = s.handler ∧
        ∀ xs, sValEq s.stack xs → ∃ st, E' xs = (res', { s1 with stack := st }) ∧
          sValEq s1.stack st ∧ sKeyEq xs st := by
    intro res' hres' hk hh hx
    refine ⟨hxs ▸ hk, hh.trans hxh, fun xs h => ?_⟩
    obtain ⟨st, he, hvs, hks⟩ := hx xs (hv xs h)
    exact ⟨st, hres' ▸ hE xs _ he, hvs, hks⟩
  have hflush : (∀ ys, sValEq x.stack ys → E ys = (res, s1)) →
      ∀ xs, sValEq s.stack xs → E' xs = (wordSemExitLoop res, s1) :=
    fun hx xs h => hE xs _ (hx xs (hv xs h))
  rcases res with _ | r
  · cases hcl
  · cases r with
    | error => trivial
    | timeOut =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, hflush hx⟩
    | notEnoughSpace =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, hflush hx⟩
    | finalFfi e =>
        obtain ⟨a, b, hx⟩ := hr
        exact ⟨a, b, hflush hx⟩
    | result v vs =>
        obtain ⟨hk, hh, hx⟩ := hr
        exact hother _ rfl hk hh hx
    | «break» k =>
        obtain ⟨hk, hh, hx⟩ := hr
        exact hother _ rfl hk hh hx
    | «continue» k =>
        obtain ⟨hk, hh, hx⟩ := hr
        exact hother _ rfl hk hh hx
    | exception a b =>
        obtain ⟨hlt, e0, e, n, ls, m, lss, hl, hm, hloc, hks, hhn, hx⟩ := hr
        rw [hxs, hxh] at hlt hl
        refine ⟨hlt, e0, e, n, ls, m, lss, hl, hm, hloc, hks, hhn, ?_⟩
        rintro xs e0' e' ls' ⟨hlx, h⟩
        rw [← hxh] at hlx
        obtain ⟨st, locs, he, rest⟩ := hx xs e0' e' ls' ⟨hlx, hv xs h⟩
        exact ⟨st, locs, hE xs _ he, rest⟩

end LoopCase

namespace EvaluateStackSwapLoopWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateStackSwapLoopWitnesses

open EvaluateStackSwapLoopWitnesses

/-- HOL `evaluate_stack_swap` (`wordPropsScript.sml:2316-2363`), `Loop` case
(proof `wordPropsScript.sml:2533-2833`): the HOL conclusion at
`Loop names c exitNames`, from exactly HOL `evaluate_ind`'s two `Loop`
induction hypotheses (the next iteration after a continuing body result with a
nonzero clock, and the body at the cut state); no extra premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackSwap_Loop {width : Nat} [NeZero width] {C F : Type}
    (names : WordLangNumSetHOL) (c : WordLangProgHOL (BitVec width))
    (exitNames : WordLangNumSetHOL) :
    ∀ s : WordSemStateFiniteExact width C F,
      (∀ v res s1, cutState (names, .ln) s = some v ∧ (res, s1) = evaluate c v ∧
          wordSemContLoop res = true ∧ s1.clock ≠ 0 →
          stackSwapPost (wordSemSTOP (.loop names c exitNames)) (decClock s1)) ∧
        (∀ v, cutState (names, .ln) s = some v → stackSwapPost c v) →
      stackSwapPost (.loop names c exitNames) s := by
  rintro s ⟨ihL, ihC⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)
    ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [stackSwapPost_iff, ht s names exitNames c]
  cases hc : cutState (names, .ln) s with
  | none => trivial
  | some x =>
  dsimp only
  obtain ⟨hxs, hxh⟩ := cutState_stack_handler _ _ _ hc
  have ihB := (stackSwapPost_iff _ _).mp (ihC x hc)
  have hv : ∀ xs, sValEq s.stack xs → sValEq x.stack xs := fun xs h => by rw [hxs]; exact h
  rcases hb : evaluate c x with ⟨res, s1⟩
  rw [hb] at ihB
  dsimp only
  by_cases hcl : wordSemContLoop res = true
  · rw [if_pos hcl]
    have hres : res = none ∨ res = some (.continue 0) := by
      rcases res with _ | r
      · exact Or.inl rfl
      · cases r <;> simp_all [wordSemContLoop]
    obtain ⟨hk, hh, hxx⟩ : sKeyEq x.stack s1.stack ∧ s1.handler = x.handler ∧
        ∀ ys, sValEq x.stack ys → ∃ st, evaluate c { x with stack := ys } =
          (res, { s1 with stack := st }) ∧ sValEq s1.stack st ∧ sKeyEq ys st := by
      rcases hres with rfl | rfl <;> exact ihB
    have hEq : ∀ xs, sValEq s.stack xs → ∃ st,
        evaluate (.loop names c exitNames) { s with stack := xs } =
          (if s1.clock = 0 then (some .timeOut, flushState true { s1 with stack := st })
           else evaluate (wordSemSTOP (.loop names c exitNames))
             (decClock { s1 with stack := st })) ∧
        sValEq s1.stack st ∧ sKeyEq xs st := by
      intro xs hxs
      obtain ⟨st, he, hvs, hks⟩ := hxx xs (hv xs hxs)
      refine ⟨st, ?_, hvs, hks⟩
      rw [ht, cutState_withStack, hc]
      dsimp only [Option.map]
      rw [he]
      dsimp only
      rw [if_pos hcl]
    by_cases hz : s1.clock = 0
    · rw [if_pos hz]
      refine ⟨rfl, rfl, fun xs hxs => ?_⟩
      obtain ⟨st, he, -, -⟩ := hEq xs hxs
      show evaluate _ _ = _
      rw [he, if_pos hz]
      rfl
    · rw [if_neg hz]
      have ihL' := (stackSwapPost_iff _ _).mp (ihL x res s1 ⟨hc, hb.symm, hcl, hz⟩)
      refine stackSwapRel_seqTail s (decClock s1) _ _ _ ihL' (hxs ▸ hk) (hh.trans hxh)
        (fun xs hxs => ?_)
      obtain ⟨st, he, hvs, hks⟩ := hEq xs hxs
      refine ⟨st, ?_, hvs, hks⟩
      show evaluate _ _ = evaluate _ _
      rw [he, if_neg hz]
      rfl
  · have hcl' : wordSemContLoop res = false := by simpa using hcl
    rw [if_neg hcl]
    split
    · -- `Break 0`: leave through the exit cut
      obtain ⟨hk, hh, hxx⟩ : sKeyEq x.stack s1.stack ∧ s1.handler = x.handler ∧
          ∀ ys, sValEq x.stack ys → ∃ st, evaluate c { x with stack := ys } =
            (some (.break 0), { s1 with stack := st }) ∧ sValEq s1.stack st ∧ sKeyEq ys st :=
        ihB
      cases hce : cutState (exitNames, .ln) s1 with
      | none => trivial
      | some s2 =>
        dsimp only
        obtain ⟨hs2, hh2⟩ := cutState_stack_handler _ _ _ hce
        refine ⟨by rw [hs2, ← hxs]; exact hk, hh2.trans (hh.trans hxh), fun xs hxs' => ?_⟩
        obtain ⟨st, he, hvs, hks⟩ := hxx xs (hv xs hxs')
        refine ⟨st, ?_, by rw [hs2]; exact hvs, hks⟩
        show evaluate _ _ = _
        rw [ht, cutState_withStack, hc]
        dsimp only [Option.map]
        rw [he]
        dsimp only
        rw [if_neg hcl, cutState_withStack, hce]
        rfl
    · rename_i hnb
      refine stackSwapRel_exitLoop s x res s1 _ _ ihB hxs hxh hcl' (fun xs t he => ?_)
      show evaluate _ _ = _
      rw [ht, cutState_withStack, hc]
      dsimp only [Option.map]
      rw [he]
      dsimp only
      rw [if_neg hcl]
      split
      · exact absurd rfl hnb
      · rfl

end WordSemStackEq

end Flapjack
