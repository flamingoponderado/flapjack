import Flapjack.Pancake.Semantics.CrepProps.EvaluateAddClock
import Flapjack.Pancake.Semantics.CrepSem.AddClock
import Flapjack.Pancake.Semantics.CrepSem.EventsMono

/-!
# Combined clock-shift / event-prefix lemma for the exact Crep evaluator

FLAPJACK-SPECIFIC (untagged) infrastructure for HOL
`crepPropsScript.sml:1020 evaluate_add_clock_io_events_mono`, plus the tagged
port itself.  The combined statement `CrepAddClockCombined` couples the
cross-clock `ffi.io_events` prefix with the clock-shift equality
`evaluate_add_clock_eq` (`crepPropsScript.sml:886`), which is what the exact
evaluator needs in the `Seq`/`Dec`/`Call` clauses.  The external prerequisite
`Flapjack.evalCrepSemHOLProgExact_add_clock_eq` lives in the sibling module
`CrepProps/EvaluateAddClock.lean`.  Untagged helpers below are Flapjack-internal;
the public port carries the qualified `@[hol]` tag.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- If the low-clock run does not time out, the combined statement follows from
the already-proved clock-shift equality `evalCrepSemHOLProgExact_add_clock_eq`. -/
theorem combined_of_not_timeout {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ) (extra : Nat)
    (hnt : (evalCrepSemHOLProgExact state program).1 ≠ some .timeOut) :
    CrepAddClockCombined program state extra := by
  refine ⟨?_, ?_⟩
  · have h := evalCrepSemHOLProgExact_add_clock_eq program state
      (evalCrepSemHOLProgExact state program).1
      (evalCrepSemHOLProgExact state program).2 extra (by rfl) hnt
    rw [h]
    exact List.prefix_refl _
  · intro _
    exact evalCrepSemHOLProgExact_add_clock_eq program state
      (evalCrepSemHOLProgExact state program).1
      (evalCrepSemHOLProgExact state program).2 extra (by rfl) hnt

/-- The clock-shift equality conjunct of `CrepAddClockCombined` for an explicit
non-timeout hypothesis. -/
theorem combined_second' {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ) (extra : Nat)
    (hnt : (evalCrepSemHOLProgExact state program).1 ≠ some .timeOut) :
    evalCrepSemHOLProgExact (crepStateAddClock state extra) program =
      ((evalCrepSemHOLProgExact state program).1,
        crepStateAddClock (evalCrepSemHOLProgExact state program).2 extra) :=
  evalCrepSemHOLProgExact_add_clock_eq program state
    (evalCrepSemHOLProgExact state program).1
    (evalCrepSemHOLProgExact state program).2 extra (by rfl) hnt

set_option linter.unusedVariables false in
/-- The named-`match` spelling of the `While` loop-control dispatch (with the
equation binder) is propositionally equal to its plain-`match` spelling, so the
goal can be rewritten to a form where `cases` on the body result reduces it. -/
theorem whileMatch_ffi {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (r : Option (CrepResultHOLExact width)) (st : CrepSemHOLState width σ) :
    (match hfixed : (r, st) with
     | (none, loopState) => evalCrepSemHOLProgExact loopState (.while e c)
     | (some (.continue 0), loopState) => evalCrepSemHOLProgExact loopState (.while e c)
     | (some (.break 0), loopState) => (none, loopState)
     | (result, loopState) => (exitLoopCrepResult result, loopState)).snd.ffi.ioEvents =
    (match (r, st) with
     | (none, loopState) => evalCrepSemHOLProgExact loopState (.while e c)
     | (some (.continue 0), loopState) => evalCrepSemHOLProgExact loopState (.while e c)
     | (some (.break 0), loopState) => (none, loopState)
     | (result, loopState) => (exitLoopCrepResult result, loopState)).snd.ffi.ioEvents := by
  cases r with
  | none => rfl
  | some val =>
      cases val with
      | «continue» k => cases k <;> rfl
      | «break» k => cases k <;> rfl
      | _ => rfl

/-- The `Call` callee-result dispatch cannot discard an earlier event prefix: the
exception-handler branch uses the handler run, and every other branch keeps (or
empties the locals of) the body result state.  This is the unstamped analogue of
`crepCallFixed_ioEvents_prefix` for the `_holShape` `Call` equation. -/
theorem callStep_prefix {width : Nat} [NeZero width] {σ : Type}
    (caltyp : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (s : CrepSemHOLState width σ)
    (rh : Option (CrepResultHOLExact width)) (sh : CrepSemHOLState width σ) :
    sh.ffi.ioEvents <+:
      (match (rh, sh) with
       | (none, st) => (some .error, st)
       | (some (.break _), st) => (some .error, st)
       | (some (.continue _), st) => (some .error, st)
       | (some (.return retvs), st) =>
           match caltyp with
           | none => (some (.return retvs), CrepSemHOLState.emptyLocals st)
           | some (rts, _) =>
               if retvs.length ≠ rts.length then (some .error, st)
               else match rts.mapM s.locals.lookup with
                    | some _ =>
                        (none, { st with locals := s.locals.updateListEq (rts.zip retvs) })
                    | none => (some .error, st)
       | (some (.exception eid), st) =>
           match caltyp with
           | none => (some (.exception eid), CrepSemHOLState.emptyLocals st)
           | some (_, none) => (some (.exception eid), CrepSemHOLState.emptyLocals st)
           | some (_, some (eid', p)) =>
               if eid = eid' then
                 evalCrepSemHOLProgExact { st with locals := s.locals } p
               else (some (.exception eid), CrepSemHOLState.emptyLocals st)
       | (res, st) => (res, st.emptyLocals)
       : Option (CrepResultHOLExact width) × CrepSemHOLState width σ).snd.ffi.ioEvents := by
  cases rh with
  | none => exact List.prefix_refl _
  | some r =>
      cases r with
      | «break» _ => exact List.prefix_refl _
      | «continue» _ => exact List.prefix_refl _
      | «return» retvs =>
          simp only []
          rcases caltyp with _ | ⟨rts, handler⟩
          · exact List.prefix_refl _
          · simp only []
            by_cases hlen : retvs.length ≠ rts.length
            · rw [if_pos hlen]; exact List.prefix_refl _
            · rw [if_neg hlen]
              cases hmap : rts.mapM s.locals.lookup <;> exact List.prefix_refl _
      | «exception» eid =>
          simp only []
          rcases caltyp with _ | ⟨rts, handler⟩
          · exact List.prefix_refl _
          · rcases handler with _ | ⟨eid', p⟩
            · exact List.prefix_refl _
            · simp only []
              by_cases heq : eid = eid'
              · subst heq
                rw [if_pos rfl]
                simpa using evalCrepSemHOLProgExact_ioEvents_prefix
                  { sh with locals := s.locals } p
              · rw [if_neg heq]; exact List.prefix_refl _
      | _ => exact List.prefix_refl _


set_option maxHeartbeats 4000000 in
theorem evalCrepSemHOLProgExact_addClock_mono_aux {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ) (extra : Nat) :
    CrepAddClockCombined program state extra := by
  have hmain :=
    evalCrepSemHOLProgExact_induct
      (P := fun pair : CrepProgHOL width × CrepSemHOLState width σ =>
        match pair with
        | (prog, state) => ∀ extra, CrepAddClockCombined prog state extra)
      (by intro s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_skip] at h; simp at h))
      (by
        intro v e prog s ih extra
        refine ⟨?_, ?_⟩
        · rw [evalCrepSemHOLProgExact_dec, evalCrepSemHOLProgExact_dec]
          rw [crepExactEvalExpClassical_addClock]
          cases h : crepExactEvalExpClassical s e with
          | none => simp only []; exact List.prefix_refl _
          | some value =>
              simp only []
              rw [setVar_crepStateAddClock]
              have hih := (ih value h extra).1
              simpa only [crepStateAddClock_ffi] using hih
        · intro hnt; exact combined_second' _ _ _ hnt)
      (by intro lhss pop rhss s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_primitive] at h
                split at h <;> (try split at h) <;> (try split at h) <;> simp_all))
      (by intro v src s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_assign] at h
                split at h <;> (try split at h) <;> (try split at h) <;> simp_all))
      (by intro dst src s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_store] at h
                split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> simp_all))
      (by intro dst src s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_store32] at h
                split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> simp_all))
      (by intro dst src s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_storeByte] at h
                split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> simp_all))
      (by intro dst src s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_storeGlob] at h
                split at h <;> (try split at h) <;> simp_all))
      (by
        intro op v ad s extra
        refine ⟨?_, ?_⟩
        · rw [evalCrepSemHOLProgExact_shMem, evalCrepSemHOLProgExact_shMem]
          rw [crepExactEvalExp_addClock]
          split
          · split
            · rw [crepShMemLoadHOL_addClock]
              simp only []
              split <;> exact List.prefix_refl _
            · rw [crepShMemStoreHOL_addClock]
              simp only []
              split <;> exact List.prefix_refl _
          · exact List.prefix_refl _
        · intro hnt; exact combined_second' _ _ _ hnt)
      (by
        intro c1 c2 s ihc2 ihc1 extra
        refine ⟨?_, ?_⟩
        · rw [evalCrepSemHOLProgExact_seq_fixClockFree, evalCrepSemHOLProgExact_seq_fixClockFree]
          cases hlow : evalCrepSemHOLProgExact s c1 with
          | mk r1 st1 =>
            cases hhigh : evalCrepSemHOLProgExact (crepStateAddClock s extra) c1 with
            | mk r1h st1h =>
              dsimp only
              have hc1 := ihc1 extra
              unfold CrepAddClockCombined at hc1
              rw [hlow, hhigh] at hc1
              cases r1 with
              | none =>
                  have heq := hc1.2 (by simp)
                  obtain ⟨hr1h, hst1h⟩ := Prod.mk.inj heq
                  subst hr1h; subst hst1h
                  exact (ihc2 none st1 hlow.symm rfl extra).1
              | some r =>
                  by_cases hr : r = .timeOut
                  · subst hr
                    cases r1h with
                    | none =>
                        exact hc1.1.trans
                          (evalCrepSemHOLProgExact_ioEvents_prefix st1h c2)
                    | some r2 => exact hc1.1
                  · have heq := hc1.2 (by simp [hr])
                    obtain ⟨hr1h, hst1h⟩ := Prod.mk.inj heq
                    subst hr1h; subst hst1h
                    exact hc1.1
        · intro hnt; exact combined_second' _ _ _ hnt)
      (by
        intro e c1 c2 s ih extra
        refine ⟨?_, ?_⟩
        · rw [evalCrepSemHOLProgExact_ite, evalCrepSemHOLProgExact_ite]
          rw [crepExactEvalExp_addClock]
          cases h : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) e with
          | none => simp only []; exact List.prefix_refl _
          | some value =>
              cases value with
              | word w =>
                  simp only []
                  by_cases hw : w ≠ 0
                  · simp only [if_pos hw]
                    have hthis := ih (.word w) w h rfl extra
                    rw [if_pos hw] at hthis
                    exact hthis.1
                  · simp only [if_neg hw]
                    have hthis := ih (.word w) w h rfl extra
                    rw [if_neg hw] at hthis
                    exact hthis.1
        · intro hnt; exact combined_second' _ _ _ hnt)
      (by intro n s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_break] at h; simp at h))
      (by intro n s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_continue] at h; simp at h))
      (by
        intro e c s ih1 ih2 ih3 extra
        refine ⟨?_, ?_⟩
        · rw [evalCrepSemHOLProgExact_while_fixClockFree,
              evalCrepSemHOLProgExact_while_fixClockFree]
          rw [crepExactEvalExp_addClock]
          cases h : crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) e with
          | none => simp only []; exact List.prefix_refl _
          | some v0 =>
              cases v0 with
              | word w =>
                  simp only []
                  by_cases hw : w ≠ 0
                  · simp only [if_pos hw]
                    by_cases hclk : s.clock = 0
                    · simp only [dif_pos hclk]
                      by_cases hclkH : (crepStateAddClock s extra).clock = 0
                      · simp only [dif_pos hclkH]; exact List.prefix_refl _
                      · simp only [dif_neg hclkH]
                        have hsp := evalCrepSemHOLProgExact_ioEvents_prefix
                          (crepStateAddClock s extra) (.while e c)
                        rw [evalCrepSemHOLProgExact_while_fixClockFree] at hsp
                        rw [crepExactEvalExp_addClock] at hsp
                        simp only [h] at hsp
                        rw [if_pos hw] at hsp
                        rw [dif_neg hclkH] at hsp
                        simpa [CrepSemHOLState.emptyLocals, crepStateAddClock_ffi] using hsp
                    · simp only [dif_neg hclk]
                      rw [dif_neg (show ¬ s.clock + extra = 0 by omega)]
                      rw [decClockCrepSemHOL_addClock s extra hclk]
                      cases hbodyL : evalCrepSemHOLProgExact (decClockCrepSemHOL s) c with
                      | mk r1 st1 =>
                        cases hbodyH : evalCrepSemHOLProgExact
                            (crepStateAddClock (decClockCrepSemHOL s) extra) c with
                        | mk rh sh =>
                          have hb := ih3 (.word w) w h rfl hw hclk extra
                          unfold CrepAddClockCombined at hb
                          rw [hbodyL, hbodyH] at hb
                          cases r1 with
                          | none =>
                              have heq := hb.2 (by simp)
                              obtain ⟨hrh, hsh⟩ := Prod.mk.inj heq
                              subst hrh; subst hsh
                              simp only []
                              exact (ih2 (.word w) w none st1 h rfl hw hclk
                                hbodyL.symm rfl extra).1
                          | some r =>
                              by_cases hr : r = CrepResultHOLExact.timeOut
                              · subst hr
                                cases rh with
                                | none =>
                                    simp only []
                                    exact hb.1.trans
                                      (evalCrepSemHOLProgExact_ioEvents_prefix sh (.while e c))
                                | some r2 =>
                                    cases r2 with
                                    | «continue» k =>
                                        cases k with
                                        | zero =>
                                            simp only []
                                            exact hb.1.trans
                                              (evalCrepSemHOLProgExact_ioEvents_prefix sh
                                                (.while e c))
                                        | succ k' => simp only []; exact hb.1
                                    | «break» k => cases k <;> (simp only []; exact hb.1)
                                    | _ => simp only []; exact hb.1
                              · by_cases hc0 : r = CrepResultHOLExact.continue 0
                                · subst hc0
                                  have heq := hb.2 (by intro hcontra; exact hr (Option.some.inj hcontra))
                                  obtain ⟨hrh, hsh⟩ := Prod.mk.inj heq
                                  subst hrh; subst hsh
                                  simp only []
                                  exact (ih1 (.word w) w (some (CrepResultHOLExact.continue 0)) st1
                                    (CrepResultHOLExact.continue 0) 0 h rfl hw hclk
                                    hbodyL.symm rfl rfl rfl extra).1
                                · have heq := hb.2 (by intro hcontra; exact hr (Option.some.inj hcontra))
                                  obtain ⟨hrh, hsh⟩ := Prod.mk.inj heq
                                  subst hrh; subst hsh
                                  cases r with
                                  | «continue» k =>
                                      cases k with
                                      | zero => exact absurd rfl hc0
                                      | succ k' => simp only []; exact hb.1
                                  | «break» k =>
                                      cases k <;> (simp only []; exact hb.1)
                                  | _ => simp only []; exact hb.1
                  · simp only [if_neg hw]; exact List.prefix_refl _
        · intro hnt; exact combined_second' _ _ _ hnt)
      (by intro es s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_return] at h
                split at h <;> simp_all))
      (by intro eid s extra
          exact combined_of_not_timeout _ _ _
            (by intro h; rw [evalCrepSemHOLProgExact_raise] at h; simp at h))
      (by intro s extra
          refine ⟨?_, ?_⟩
          · rw [evalCrepSemHOLProgExact_tick, evalCrepSemHOLProgExact_tick]
            simp only [CrepSemHOLState.emptyLocals, decClockCrepSemHOL]
            split <;> split <;> exact List.prefix_refl _
          · intro hnt; exact combined_second' _ _ _ hnt)
      (by
        intro caltyp fname argexps s ihexn ihnormal extra
        refine ⟨?_, ?_⟩
        · classical
          rw [evalCrepSemHOLProgExact_call_holShape]
          rw [evalCrepSemHOLProgExact_call_holShape]
          rw [evalCrepSemHOLExps_addClock]
          have hargsconv : List.mapM (evalCrepSemHOLExp s) argexps =
              List.mapM (crepExactEvalExpClassical s) argexps := by
            have heq := optMmapCongHOL argexps argexps
              (crepExactEvalExpClassical s) (evalCrepSemHOLExp s) rfl
              (fun expression _ => crepExactEvalExpClassical_eq s expression)
            exact heq.symm
          rw [hargsconv]
          rw [crepStateAddClock_code]
          cases hargs : List.mapM (crepExactEvalExpClassical s) argexps with
          | none => simp only []; exact List.prefix_refl _
          | some args =>
            simp only []
            cases hcode : lookupCodeFiniteHOL s.code fname args args.length with
            | none => simp only []; exact List.prefix_refl _
            | some pair =>
              obtain ⟨prog, newlocals⟩ := pair
              simp only []
              have hcode' : lookupCodeHOL s.code.lookup fname args args.length =
                  some (prog, newlocals.lookup) := by
                have h := lookupCodeFiniteHOL_lookup s.code fname args args.length
                rw [hcode] at h
                simpa using h.symm
              have hcodeFin : lookupCodeHOLFinite s.code.lookup fname args args.length =
                  some (prog, newlocals) :=
                (lookupCodeHOLFinite_eq_some_iff s.code.lookup fname args args.length
                  prog newlocals).mpr hcode'
              by_cases hbad : crepReturnInfoNodupError caltyp
              · rw [if_pos hbad]
                rw [if_pos hbad]
                exact List.prefix_refl _
              · rw [if_neg hbad]
                rw [if_neg hbad]
                by_cases hclk : s.clock = 0
                · rw [if_pos hclk]
                  by_cases hclkH : (crepStateAddClock s extra).clock = 0
                  · rw [if_pos hclkH]
                    exact List.prefix_refl _
                  · rw [if_neg hclkH]
                    cases hbodyH : evalCrepSemHOLProgExact
                        { decClockCrepSemHOL (crepStateAddClock s extra) with
                          locals := newlocals } prog with
                    | mk rh sh =>
                      have hbodypref : s.ffi.ioEvents <+: sh.ffi.ioEvents := by
                        have hh := evalCrepSemHOLProgExact_ioEvents_prefix
                          { decClockCrepSemHOL (crepStateAddClock s extra) with
                            locals := newlocals } prog
                        rw [hbodyH] at hh
                        simpa [decClockCrepSemHOL, crepStateAddClock_ffi,
                          CrepSemHOLState.emptyLocals] using hh
                      exact hbodypref.trans (callStep_prefix caltyp s rh sh)
                · rw [if_neg hclk]
                  rw [if_neg (show ¬ (crepStateAddClock s extra).clock = 0 by
                    rw [crepStateAddClock_clock]
                    omega)]
                  rw [decClockCrepSemHOL_addClock s extra hclk]
                  rw [show ({ CrepAddClock (decClockCrepSemHOL s) extra with
                        locals := newlocals } : CrepSemHOLState width σ) =
                      crepStateAddClock ({ decClockCrepSemHOL s with
                        locals := newlocals } : CrepSemHOLState width σ) extra from rfl]
                  cases hbodyL : evalCrepSemHOLProgExact
                      { decClockCrepSemHOL s with locals := newlocals } prog with
                  | mk r st =>
                    cases hbodyH : evalCrepSemHOLProgExact
                        (crepStateAddClock { decClockCrepSemHOL s with
                          locals := newlocals } extra) prog with
                    | mk rh sh =>
                      have hb := ihnormal args (prog, newlocals) prog newlocals
                        hargs hcodeFin rfl
                        (by
                          intro hnotBad
                          cases caltyp with
                          | none => cases hnotBad
                          | some info =>
                              rcases info with ⟨rts, snd⟩
                              have hnodup : rts.Nodup := by
                                by_cases hnodup : rts.Nodup
                                · exact hnodup
                                · exact False.elim
                                    (hbad (by simp [crepReturnInfoNodupError, hnodup]))
                              exact hnotBad hnodup)
                        hclk extra
                      unfold CrepAddClockCombined at hb
                      rw [hbodyL, hbodyH] at hb
                      by_cases hto : r = some CrepResultHOLExact.timeOut
                      · subst hto
                        try simp only []
                        exact hb.1.trans (callStep_prefix caltyp s rh sh)
                      · have heq := hb.2 hto
                        obtain ⟨hrh, hsh⟩ := Prod.mk.inj heq
                        subst rh; subst sh
                        cases r with
                        | none => (try simp only []); exact List.prefix_refl _
                        | some rr =>
                          cases rr with
                          | «return» retvs =>
                              cases caltyp with
                              | none => (try simp only []); exact List.prefix_refl _
                              | some cval =>
                                  obtain ⟨rts, _⟩ := cval
                                  try simp only []
                                  by_cases hlen : retvs.length ≠ rts.length
                                  · simp only [if_pos hlen]
                                    exact List.prefix_refl _
                                  · simp only [if_neg hlen]
                                    cases hm : List.mapM s.locals.lookup rts <;>
                                      (try simp only []) <;> exact List.prefix_refl _
                          | «exception» eid =>
                              cases caltyp with
                              | none => (try simp only []); exact List.prefix_refl _
                              | some cval =>
                                  obtain ⟨rts, handler⟩ := cval
                                  cases handler with
                                  | none => (try simp only []); exact List.prefix_refl _
                                  | some hval =>
                                      obtain ⟨eid', p⟩ := hval
                                      try simp only []
                                      by_cases heq2 : eid = eid'
                                      · simp only [if_pos heq2]
                                        have hnodup : rts.Nodup := by
                                          by_cases hnodup : rts.Nodup
                                          · exact hnodup
                                          · exact False.elim
                                              (hbad (by simp [crepReturnInfoNodupError, hnodup]))
                                        rw [show ({ crepStateAddClock st extra with
                                              locals := s.locals } : CrepSemHOLState width σ) =
                                            crepStateAddClock ({ st with
                                              locals := s.locals } : CrepSemHOLState width σ)
                                              extra from rfl]
                                        exact (ihexn args (prog, newlocals) prog newlocals
                                          (evalCrepSemHOLProgExact
                                            { decClockCrepSemHOL s with locals := newlocals } prog)
                                          (some (.exception eid)) st (.exception eid) eid
                                          (rts, some (eid', p)) rts (some (eid', p)) (eid', p) eid' p
                                          hargs hcodeFin rfl
                                          (by intro hnotBad; exact hnotBad hnodup)
                                          hclk rfl hbodyL rfl rfl rfl rfl rfl
                                          rfl heq2 extra).1
                                      · simp only [if_neg heq2]
                                        exact List.prefix_refl _
                          | _ => (try simp only []); exact List.prefix_refl _
        · intro hnt; exact combined_second' _ _ _ hnt)
      (by
        intro ffi_index ptr1 len1 ptr2 len2 s extra
        have hpref :
            (evalCrepSemHOLProgExact s
              (.extCall ffi_index ptr1 len1 ptr2 len2)).2.ffi.ioEvents <+:
            (evalCrepSemHOLProgExact (crepStateAddClock s extra)
              (.extCall ffi_index ptr1 len1 ptr2 len2)).2.ffi.ioEvents := by
          simp only [evalCrepSemHOLProgExact_extCall]
          simp only [crepExactMemLoadByteWord8_addClock]
          split <;> (try split) <;> (try split) <;> (try split) <;>
            (try split) <;> (try split) <;> (try split) <;>
            exact List.prefix_refl _
        exact ⟨hpref, fun hnt => combined_second' _ _ _ hnt⟩)
  exact hmain program state extra

/-- The combined clock-shift/event-prefix statement for the exact evaluator:
the low-clock run's `ffi.io_events` prefix the clock-raised run's, and when the
low-clock run does not time out the raised run is exactly the low-clock run with
its final clock raised by `extra` (HOL `evaluate_add_clock_eq`). -/
theorem evalCrepSemHOLProgExact_addClockCombined {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ) (extra : Nat) :
    CrepAddClockCombined program state extra :=
  evalCrepSemHOLProgExact_addClock_mono_aux program state extra

namespace CrepPropsEvaluateAddClockIoEventsMonoFiniteSupport

/-- Local same-module witness for the canonical finite-support `CrepSemHOLState`
carrier used by the qualified `evaluate_add_clock_io_events_mono` port below (an
imported witness may be re-exported as a local one). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end CrepPropsEvaluateAddClockIoEventsMonoFiniteSupport

/-- Exact port of HOL `Theorem evaluate_add_clock_io_events_mono`
(`cakeml/pancake/semantics/crepPropsScript.sml:1020`):
`!exps s extra. (SND(evaluate (exps,s))).ffi.io_events ≼
(SND(evaluate (exps,s with clock := s.clock + extra))).ffi.io_events`.
The evaluator is the exact `crepSem$evaluate` port `evalCrepSemHOLProgExact`;
`CrepSemHOLState`'s `locals`/`globals`/`code` are the canonical
`HolFiniteMapExact` translation (same-module witness above), HOL's type-indexed
`'a word` is `BitVec width` under `[NeZero width]`, and `'ffi` is `σ : Type`;
hence the combined qualifiers.  The proof composes the combined induction
`evalCrepSemHOLProgExact_addClock_mono_aux`: non-timeout clauses use
`evalCrepSemHOLProgExact_add_clock_eq`, timeout clauses use the single-run
prefix `evalCrepSemHOLProgExact_ioEvents_prefix` and `List.IsPrefix.trans`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "evaluate_add_clock_io_events_mono" 1020
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem crepPropsEvaluateAddClockIoEventsMono {width : Nat} [NeZero width] {σ : Type}
    (program : CrepProgHOL width) (state : CrepSemHOLState width σ) (extra : Nat) :
    (evalCrepSemHOLProgExact state program).2.ffi.ioEvents <+:
      (evalCrepSemHOLProgExact (crepStateAddClock state extra) program).2.ffi.ioEvents :=
  (evalCrepSemHOLProgExact_addClock_mono_aux program state extra).1

end Flapjack
