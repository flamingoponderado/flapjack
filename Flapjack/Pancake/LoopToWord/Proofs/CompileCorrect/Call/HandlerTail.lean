import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.Support

/-!
# Handler continuation tail for the `Call_SOMEhandler` piece

This is Flapjack-only proof support for HOL `compile_correct[Call_SOMEhandler]`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1223-1407`, bead
`flapjack-pxn.18.5.9.27.3`).  A handled call compiles to
`Seq (Call ... (SOME handler)) Tick`, and loopSem wraps the handler
continuation in `cut_res live_out`.  `handlerTail` relates the two ends for
either continuation (the returning `r` or the exception handler `h`), given
the continuation's induction-hypothesis conclusion.  HOL proves this inline
(the `qNONE`/`qSOME` steps), so nothing here is tagged.
-/

namespace Flapjack.LoopToWord.CompileCorrect

open Flapjack

/-- Restricting the source locals by `inter` keeps `locals_rel`. -/
theorem localsRel_inter {width : Nat} [NeZero width] (ctxt : Spt Nat)
    (a : Spt (WordLocW width)) (b : NumSet) (c : Spt (WordLocW width))
    (h : localsRelHOL ctxt a c) : localsRelHOL ctxt (sptInter a b) c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun n v hv => h3 n v ?_⟩
  rw [sptLookup_sptInter] at hv
  split at hv
  · exact hv
  · cases hv

/-- `resultCase` only reads the initial target state's `stack` and
    `handler`. -/
theorem resultCase_congr {width : Nat} [NeZero width] {C F : Type} (ctxt : Spt Nat)
    (retv : WordLocW width) (T t : WordSemStateFiniteExact width C F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F) (res1 : Option (WordSemResult width))
    (t1 : WordSemStateFiniteExact width C F)
    (hstk : T.stack = t.stack) (hhd : T.handler = t.handler)
    (h : resultCase ctxt retv T res s1 res1 t1) : resultCase ctxt retv t res s1 res1 t1 := by
  unfold resultCase at h ⊢
  rw [hstk, hhd] at h
  exact h

/-- The shared tail of both handler continuations: loopSem
    `cut_res live_out` of the continuation's result, against the wordSem
    trailing `Tick` after the returning call. -/
theorem handlerTail {width : Nat} [NeZero width] {C F : Type} (ctxt : Spt Nat)
    (retv : WordLocW width) (t T : WordSemStateFiniteExact width C F) (liveOut : NumSet)
    (q : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s2 : LoopSemStateFiniteExact width F) (res1' : Option (WordSemResult width))
    (t1' : WordSemStateFiniteExact width C F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F)
    (hrc : resultCase ctxt retv T q s2 res1' t1') (hf : t1'.ffi = s2.ffi)
    (hstk : T.stack = t.stack) (hhd : T.handler = t.handler)
    (hloop : LoopSemStateFiniteExact.cutRes liveOut (q, s2) = (res, s1))
    (hNE : res ≠ some .error) :
    ∃ t1 res1,
      (match res1' with
        | none => WordSemStateFiniteExact.evaluate .tick t1'
        | _ => (res1', t1')) = (res1, t1) ∧
      t1.ffi = s1.ffi ∧ resultCase ctxt retv t res s1 res1 t1 := by
  have htick := (WordSemStateFiniteExact.evaluate_def_rebound (width := width) (C := C)
    (F := F)).2.2.2.2.2.2.2.2.2.2.1
  have hrc' := resultCase_congr ctxt retv T t q s2 res1' t1' hstk hhd hrc
  unfold LoopSemStateFiniteExact.cutRes at hloop
  cases q with
  | some x =>
    simp only [Prod.mk.injEq] at hloop
    obtain ⟨rfl, rfl⟩ := hloop
    have hsome : res1' ≠ none := by
      intro hn
      subst hn
      cases x with
      | result v => exact absurd hrc.2.1 (by simp)
      | exception v =>
        obtain ⟨_, himp, _⟩ := hrc
        obtain ⟨u1, u2, h⟩ := himp (by simp)
        cases h
      | «break» k => exact absurd hrc.2.1 (by simp)
      | «continue» k => exact absurd hrc.2.1 (by simp)
      | timeOut => simp [resultCase] at hrc
      | finalFfi f => simp [resultCase] at hrc
      | error => exact absurd rfl hNE
    cases res1' with
    | none => exact absurd rfl hsome
    | some r => exact ⟨t1', some r, rfl, hf, hrc'⟩
  | none =>
    obtain ⟨hst, hr1, h0, hl, hstk', hhd'⟩ := hrc
    subst hr1
    simp only at hloop
    cases hcs : LoopSemStateFiniteExact.cutState liveOut s2 with
    | none =>
      rw [hcs] at hloop
      simp only [Prod.mk.injEq] at hloop
      exact absurd hloop.1.symm hNE
    | some cut =>
      rw [hcs] at hloop
      simp only at hloop
      unfold LoopSemStateFiniteExact.cutState at hcs
      split at hcs
      · cases hcs
        obtain ⟨len, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hst
        simp only [htick]
        by_cases hz : s2.clock = 0
        · simp only [hz, if_true, Prod.mk.injEq] at hloop
          obtain ⟨rfl, rfl⟩ := hloop
          rw [if_pos (by rw [e4]; exact hz)]
          exact ⟨_, _, rfl, by simp [WordSemStateFiniteExact.flushState, e6], rfl⟩
        · simp only [hz, if_false, Prod.mk.injEq] at hloop
          obtain ⟨rfl, rfl⟩ := hloop
          rw [if_neg (by rw [e4]; exact hz)]
          refine ⟨_, _, rfl, e6, ⟨len, e1, e2, e3, ?_, e5, e6, e7, e8, e9, e10, e11⟩, rfl,
            h0, localsRel_inter ctxt _ _ _ hl, hstk'.trans hstk, hhd'.trans hhd⟩
          simp [WordSemStateFiniteExact.decClock, LoopSemStateFiniteExact.decClock, e4]
      · cases hcs

end Flapjack.LoopToWord.CompileCorrect
