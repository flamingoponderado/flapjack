import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact

/-!
# loopProps FFI-event monotonicity over the exact loopSem evaluator

Counterparts of `cakeml/pancake/semantics/loopPropsScript.sml`'s
`evaluate_io_events_mono` (line 1135) and `evaluate_add_clock_io_events_mono`
(line 1217) over `LoopSemStateFiniteExact.evaluate` (bead `flapjack-pxgp.10`).
-/

namespace Flapjack
namespace LoopSemStateFiniteExact

variable {width : Nat} [NeZero width] {F : Type}

theorem memStore_ffi {a : BitVec width} {v : WordLocW width}
    {s st : LoopSemStateFiniteExact width F} (h : memStore a v s = some st) : st.ffi = s.ffi := by
  unfold memStore at h; split at h <;> simp at h; subst h; rfl

theorem loopArith_ffi {op : LoopArith} {s st : LoopSemStateFiniteExact width F}
    (h : loopArith s op = some st) : st.ffi = s.ffi := by
  cases op <;> simp only [loopArith] at h <;> split at h <;> (try split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> (subst h; rfl)

theorem cutState_ffi {live : NumSet} {s s1 : LoopSemStateFiniteExact width F}
    (h : cutState live s = some s1) : s1.ffi = s.ffi := by
  unfold cutState at h; split at h <;> simp at h; subst h; rfl

theorem cutRes_ffi (live : NumSet)
    (r : Option (LoopResultExact width) × LoopSemStateFiniteExact width F) :
    (cutRes live r).2.ffi = r.2.ffi := by
  obtain ⟨res, s⟩ := r
  cases res with
  | some _ => simp [cutRes]
  | none =>
    simp only [cutRes]
    cases hc : cutState live s with
    | none => simp
    | some s1 => simp only; have := cutState_ffi hc; split <;> simp [decClock, this]

theorem fixClock_ffi {β : Type} (old : LoopSemStateFiniteExact width F)
    (step : β × LoopSemStateFiniteExact width F) : (fixClock old step).2.ffi = step.2.ffi := rfl

theorem shMemLoad_ioEvents (v : Nat) (a : BitVec width) (nb : Nat)
    (s : LoopSemStateFiniteExact width F) :
    s.ffi.ioEvents <+: (shMemLoad v a nb s).2.ffi.ioEvents := by
  unfold shMemLoad
  split <;> split <;> (try exact List.prefix_refl _) <;> split <;>
    (try exact List.prefix_refl _) <;>
    exact callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ ‹_›

theorem shMemStore_ioEvents (v : Nat) (a : BitVec width) (nb : Nat)
    (s : LoopSemStateFiniteExact width F) :
    s.ffi.ioEvents <+: (shMemStore v a nb s).2.ffi.ioEvents := by
  unfold shMemStore
  split <;> (try exact List.prefix_refl _) <;> split <;> split <;>
    (try exact List.prefix_refl _) <;> split <;> (try exact List.prefix_refl _) <;>
    exact callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ ‹_›

theorem shMemOp_ioEvents (op : CrepMemOp) (v : Nat) (a : BitVec width)
    (s : LoopSemStateFiniteExact width F) :
    s.ffi.ioEvents <+: (shMemOp op v a s).2.ffi.ioEvents := by
  cases op <;> simp only [shMemOp] <;> first | exact shMemLoad_ioEvents .. | exact shMemStore_ioEvents ..

theorem fixClock_eq_ffi {β : Type} {old s' : LoopSemStateFiniteExact width F}
    {step : β × LoopSemStateFiniteExact width F} {r : β}
    (h : fixClock old step = (r, s')) : s'.ffi = step.2.ffi := by
  have := fixClock_ffi old step; rw [h] at this; exact this

theorem cutRes_eq_ffi {live : NumSet} {r r' : Option (LoopResultExact width)}
    {s s' : LoopSemStateFiniteExact width F}
    (h : cutRes live (r, s) = (r', s')) : s'.ffi = s.ffi := by
  have := cutRes_ffi live (r, s); rw [h] at this; exact this

theorem evaluate_io_events_mono_snd (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    s.ffi.ioEvents <+: (evaluate p s).2.ffi.ioEvents := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock, sizeOf p) = x → s.ffi.ioEvents <+: (evaluate p s).2.ffi.ioEvents := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx
      have ih : ∀ (p' : HolLoopProg width) (s' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (s'.clock, sizeOf p') (s.clock, sizeOf p) →
            s'.ffi.ioEvents <+: (evaluate p' s').2.ffi.ioEvents :=
        fun p' s' hlt => ih0 _ (hx ▸ hlt) p' s' rfl
      clear ih0 hx
      cases p
      case seq c1 c2 =>
        rw [evaluate]; rw [fix_clock_evaluate]
        have h1 := ih c1 s (lexLt (Nat.le_refl _) (by simp +arith))
        split
        · rename_i s1 he
          rw [he] at h1
          exact h1.trans (ih c2 s1 (lexLt (by have := evaluate_clock _ _ _ _ he; omega)
            (by simp +arith)))
        · rename_i r1 s1 _ he; rw [he] at h1; exact h1
      case ite cmp r1 ri c1 c2 live =>
        rw [evaluate]
        split
        · split
          · rw [cutRes_ffi]; exact ih c1 s (lexLt (Nat.le_refl _) (by simp +arith))
          · rw [cutRes_ffi]; exact ih c2 s (lexLt (Nat.le_refl _) (by simp +arith))
        · exact List.prefix_refl _
      case store e v =>
        rw [evaluate]
        repeat' split
        all_goals (try exact List.prefix_refl _)
        rename_i hms
        have := memStore_ffi hms
        simp only [this]
        exact List.prefix_refl _
      case arith op =>
        rw [evaluate]
        repeat' split
        all_goals (try exact List.prefix_refl _)
        rename_i hla
        have := loopArith_ffi hla
        simp only [this]
        exact List.prefix_refl _
      case loop li body lo =>
        rw [evaluate]
        split
        · rename_i s1 hc
          have e1 := cutRes_eq_ffi hc
          have hs1 := cutRes_none_clock hc
          rw [fix_clock_evaluate]
          have hb := ih body s1 (lexLtClock hs1)
          rw [← e1]
          split
          · rename_i s2 he; rw [he] at hb
            exact hb.trans (ih _ s2 (lexLtClock (Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1)))
          · rename_i s2 he; rw [he] at hb
            exact hb.trans (ih _ s2 (lexLtClock (Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1)))
          · rename_i s2 he; rw [he] at hb; rw [cutRes_ffi]; exact hb
          · rename_i r s2 _ _ _ he; rw [he] at hb; exact hb
        · rw [cutRes_ffi]; exact List.prefix_refl _
      case ffi idx p1 l1 p2 l2 cutset =>
        rw [evaluate]
        repeat' split
        all_goals (try exact List.prefix_refl _)
        all_goals (have hcs := cutState_ffi ‹cutState _ _ = some _›)
        all_goals (try (simp only [callEnv, hcs]; exact List.prefix_refl _))
        all_goals (try (dsimp only; rw [← hcs]; exact callFFIHOL_return_ioEvents_prefix _ _ _ _ _ _ ‹_›))
      case call ret dest args handler =>
        rw [evaluate]
        split
        · exact List.prefix_refl _
        rename_i argvals _
        split
        · exact List.prefix_refl _
        rename_i env prog _
        cases ret with
        | none =>
          simp only
          split
          · exact List.prefix_refl _
          split
          · exact List.prefix_refl _
          rename_i hz
          have hp := ih prog { decClock s with locals := env }
            (lexLtClock (by simp only [decClock]; omega))
          split <;> (rename_i he; rw [he] at hp; exact hp)
        | some nl =>
          obtain ⟨ns, live⟩ := nl
          simp only
          split
          · exact List.prefix_refl _
          split
          · rename_i s1 hc
            have e1 := cutRes_eq_ffi hc
            have hs1 := cutRes_none_clock hc
            rw [fix_clock_evaluate, ← e1]
            have hp := ih prog { s1 with locals := env } (lexLtClock hs1)
            split
            · rename_i retvs st1 he
              rw [he] at hp
              have hst1 : st1.clock < s.clock :=
                Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1
              split
              · exact hp
              · cases handler with
                | none => exact hp
                | some hd =>
                  obtain ⟨_, _, r, liveOut⟩ := hd
                  simp only; rw [cutRes_ffi]
                  exact hp.trans (ih r (setVars ns retvs { st1 with locals := s1.locals })
                    (lexLtClock (by simp only [setVars]; omega)))
            · rename_i exn st1 he
              rw [he] at hp
              have hst1 : st1.clock < s.clock :=
                Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1
              cases handler with
              | none => exact hp
              | some hd =>
                obtain ⟨n, hp', _, liveOut⟩ := hd
                simp only; rw [cutRes_ffi]
                exact hp.trans (ih hp' (setVar n exn { st1 with locals := s1.locals })
                  (lexLtClock (by simp only [setVar]; omega)))
            · rename_i _ st1 he; rw [he] at hp; exact hp
            · rename_i _ st1 he; rw [he] at hp; exact hp
            · rename_i st1 he; rw [he] at hp; exact hp
            · exact hp
          · rw [cutRes_ffi]; exact List.prefix_refl _
      case mark q =>
        rw [evaluate]; exact ih q s (lexLt (Nat.le_refl _) (by simp +arith))
      all_goals (try rw [evaluate])
      all_goals (repeat' split)
      all_goals (try dsimp only)
      all_goals (try (exact List.prefix_refl _))
      all_goals (try (rw [memStore_ffi ‹memStore _ _ _ = some _›]; exact List.prefix_refl _))
      all_goals (try (rw [loopArith_ffi ‹loopArith _ _ = some _›]; exact List.prefix_refl _))
      all_goals (try (exact shMemOp_ioEvents _ _ _ _))
  exact key _ p s rfl

/-- Exact HOL `evaluate_io_events_mono` (`loopPropsScript.sml:1135-1139`):
    `!exps s1 res s2. evaluate (exps,s1) = (res, s2) ⇒
      s1.ffi.io_events ≼ s2.ffi.io_events`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_io_events_mono"
  (words_as_type_indexed_bitvec)]
theorem evaluate_io_events_mono (exps : HolLoopProg width) (s1 : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (s2 : LoopSemStateFiniteExact width F)
    (h : evaluate exps s1 = (res, s2)) : s1.ffi.ioEvents <+: s2.ffi.ioEvents := by
  have := evaluate_io_events_mono_snd exps s1; rw [h] at this; exact this

theorem add_clock_events_of_not_timeout (p : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F) (extra : Nat)
    (hnt : (evaluate p s).1 ≠ some .timeOut) :
    (evaluate p s).2.ffi.ioEvents <+:
      (evaluate p { s with clock := s.clock + extra }).2.ffi.ioEvents := by
  rw [evaluate_add_clock_eq p s _ _ extra rfl hnt]; exact List.prefix_refl _

theorem add_clock_events_big (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (extra : Nat) :
    s.ffi.ioEvents <+: (evaluate p { s with clock := s.clock + extra }).2.ffi.ioEvents :=
  evaluate_io_events_mono_snd p { s with clock := s.clock + extra }

theorem shMemOp_not_timeout (op : CrepMemOp) (v : Nat) (a : BitVec width)
    (s : LoopSemStateFiniteExact width F) : (shMemOp op v a s).1 ≠ some .timeOut := by
  cases op <;> simp only [shMemOp, shMemLoad, shMemStore] <;>
    (repeat' split) <;> simp

theorem evaluate_add_clock_io_events_mono_snd (p : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F) (extra : Nat) :
    (evaluate p s).2.ffi.ioEvents <+:
      (evaluate p { s with clock := s.clock + extra }).2.ffi.ioEvents := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock, sizeOf p) = x → ∀ extra, (evaluate p s).2.ffi.ioEvents <+:
        (evaluate p { s with clock := s.clock + extra }).2.ffi.ioEvents := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx extra
      have ih : ∀ (p' : HolLoopProg width) (s' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (s'.clock, sizeOf p') (s.clock, sizeOf p) → ∀ extra,
            (evaluate p' s').2.ffi.ioEvents <+:
              (evaluate p' { s' with clock := s'.clock + extra }).2.ffi.ioEvents :=
        fun p' s' hlt => ih0 _ (hx ▸ hlt) p' s' rfl
      clear ih0 hx
      by_cases hnt : (evaluate p s).1 ≠ some .timeOut
      · exact add_clock_events_of_not_timeout p s extra hnt
      have hto : (evaluate p s).1 = some .timeOut := Classical.not_not.mp hnt
      clear hnt
      -- If the small run ends with the initial FFI state, the big run's monotonicity suffices.
      have viaStart : (evaluate p s).2.ffi = s.ffi →
          (evaluate p s).2.ffi.ioEvents <+:
            (evaluate p { s with clock := s.clock + extra }).2.ffi.ioEvents := by
        intro hf; rw [hf]; exact add_clock_events_big p s extra
      cases p
      case seq c1 c2 =>
        have lex1 : Prod.Lex (· < ·) (· < ·) (s.clock, sizeOf c1) (s.clock, sizeOf (c1.seq c2)) :=
          lexLt (Nat.le_refl _) (by simp +arith)
        rw [evaluate, evaluate, fix_clock_evaluate, fix_clock_evaluate]
        have h1 := ih c1 s lex1 extra
        cases he : evaluate c1 s with
        | mk r1 s1 =>
          rw [he] at h1
          by_cases hr1 : r1 = some .timeOut
          · subst hr1
            simp only
            cases he' : evaluate c1 { s with clock := s.clock + extra } with
            | mk r1' s1' =>
              rw [he'] at h1; simp only at h1
              cases r1' with
              | none => simp only; exact h1.trans (evaluate_io_events_mono_snd c2 s1')
              | some v => simp only; exact h1
          · have e1 := evaluate_add_clock_eq c1 s r1 s1 extra he hr1
            rw [e1]
            cases r1 with
            | none =>
              simp only
              exact ih c2 s1 (lexLt (evaluate_clock _ _ _ _ he) (by simp +arith)) extra
            | some v => simp only; exact List.prefix_refl _
      case ite cmp r1 ri c1 c2 live =>
        rw [evaluate, evaluate]; simp only [getVarImm_upd_clock]
        split
        · split
          · rw [cutRes_ffi, cutRes_ffi]
            exact ih c1 s (lexLt (Nat.le_refl _) (by simp +arith)) extra
          · rw [cutRes_ffi, cutRes_ffi]
            exact ih c2 s (lexLt (Nat.le_refl _) (by simp +arith)) extra
        · exact List.prefix_refl _
      case mark q =>
        rw [evaluate, evaluate]; exact ih q s (lexLt (Nat.le_refl _) (by simp +arith)) extra
      case loop li body lo =>
        generalize hbig : evaluate (HolLoopProg.loop li body lo)
          { s with clock := s.clock + extra } = big
        rw [evaluate]
        cases hc : cutRes li (none, s) with
        | mk r0 s1 =>
          cases r0 with
          | some v =>
            simp only
            rw [cutRes_eq_ffi hc, ← hbig]
            exact add_clock_events_big _ s extra
          | none =>
            simp only
            rw [fix_clock_evaluate]
            have hs1 := cutRes_none_clock hc
            have hc' := cutRes_add_clock li none s s1 none extra hc (by simp)
            rw [evaluate] at hbig
            rw [← hbig, hc']
            simp only
            rw [fix_clock_evaluate]
            have hb := ih body s1 (lexLtClock hs1) extra
            cases hbe : evaluate body s1 with
            | mk rb s2 =>
              rw [hbe] at hb
              by_cases hrb : rb = some .timeOut
              · subst hrb
                simp only
                cases hbe' : evaluate body { s1 with clock := s1.clock + extra } with
                | mk rb' s2' =>
                  rw [hbe'] at hb; simp only at hb
                  refine hb.trans ?_
                  rcases rb' with _ | (vs | e | l | l | _ | o | _)
                  · simp only; exact evaluate_io_events_mono_snd _ s2'
                  · simp only; exact List.prefix_refl _
                  · simp only; exact List.prefix_refl _
                  · cases l <;> simp only
                    · rw [cutRes_ffi]; exact List.prefix_refl _
                    · exact List.prefix_refl _
                  · cases l <;> simp only
                    · exact evaluate_io_events_mono_snd _ s2'
                    · exact List.prefix_refl _
                  · simp only; exact List.prefix_refl _
                  · simp only; exact List.prefix_refl _
                  · simp only; exact List.prefix_refl _
              · have eb := evaluate_add_clock_eq body s1 rb s2 extra hbe hrb
                rw [eb]
                have hs2 : s2.clock < s.clock := Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ hbe) hs1
                rcases rb with _ | (vs | e | l | l | _ | o | _)
                · simp only; exact ih _ s2 (lexLtClock hs2) extra
                · simp only; exact List.prefix_refl _
                · simp only; exact List.prefix_refl _
                · cases l <;> simp only
                  · rw [cutRes_ffi, cutRes_ffi]; exact List.prefix_refl _
                  · exact List.prefix_refl _
                · cases l <;> simp only
                  · exact ih _ s2 (lexLtClock hs2) extra
                  · exact List.prefix_refl _
                · exact absurd rfl hrb
                · simp only; exact List.prefix_refl _
                · simp only; exact List.prefix_refl _
      case call ret dest args handler =>
        have hmono := add_clock_events_big (HolLoopProg.call ret dest args handler) s extra
        generalize hbig : evaluate (HolLoopProg.call ret dest args handler)
          { s with clock := s.clock + extra } = big at hmono
        rw [evaluate]
        cases hg : getVars args s with
        | none => simp only; exact hmono
        | some argvals =>
          simp only
          cases hfc : findCode dest argvals s.code with
          | none => simp only; exact hmono
          | some ep =>
            obtain ⟨env, prog⟩ := ep
            simp only
            rw [evaluate] at hbig
            simp only [getVars_upd_clock, hg, hfc] at hbig
            cases ret with
            | none =>
              simp only at hbig ⊢
              by_cases hh : handler.isSome = true
              · simp only [hh, if_true]; exact hmono
              · simp only [hh, if_false, Bool.false_eq_true] at hbig ⊢
                by_cases hz : s.clock = 0
                · simp only [hz, dite_true]; exact hmono
                · have hz' : s.clock + extra ≠ 0 := by omega
                  simp only [hz, hz', dite_false] at hbig ⊢
                  have hst : ({ decClock { s with clock := s.clock + extra } with locals := env } :
                      LoopSemStateFiniteExact width F) =
                      { ({ decClock s with locals := env } : LoopSemStateFiniteExact width F) with
                        clock := ({ decClock s with locals := env } :
                          LoopSemStateFiniteExact width F).clock + extra } := by
                    cases s; simp only [decClock, LoopSemStateFiniteExact.mk.injEq, true_and,
                      and_true] at hz ⊢; omega
                  rw [hst] at hbig
                  have hcal := ih prog { decClock s with locals := env }
                    (lexLtClock (by simp only [decClock]; omega)) extra
                  rw [← hbig]
                  split
                  all_goals (rename_i he1; rw [he1] at hcal)
                  all_goals split
                  all_goals (rename_i he2; rw [he2] at hcal; exact hcal)
            | some nl =>
              obtain ⟨ns, live⟩ := nl
              simp only at hbig ⊢
              by_cases hnd : ¬ ns.Nodup
              · simp only [hnd]; exact hmono
              simp only [hnd, if_false] at hbig ⊢
              cases hc : cutRes live (none, s) with
              | mk r0 s1 =>
                cases r0 with
                | some v => simp only; rw [cutRes_eq_ffi hc]; exact hmono
                | none =>
                  simp only
                  have hs1 := cutRes_none_clock hc
                  have hc' := cutRes_add_clock live none s s1 none extra hc (by simp)
                  rw [hc'] at hbig; simp only at hbig
                  rw [fix_clock_evaluate] at hbig ⊢
                  have hcal := ih prog { s1 with locals := env } (lexLtClock hs1) extra
                  simp only at hcal
                  cases he : evaluate prog { s1 with locals := env } with
                  | mk rc st1 =>
                    rw [he] at hcal
                    have hst1 : st1.clock < s.clock :=
                      Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1
                    by_cases hrc : rc = some .timeOut
                    · subst hrc
                      simp only
                      rw [← hbig]
                      refine hcal.trans ?_
                      split
                      all_goals (try (rename_i heq; rw [heq]))
                      all_goals (try split)
                      all_goals (try (cases handler))
                      all_goals (try simp only)
                      all_goals (first
                        | exact List.prefix_refl _
                        | (rw [cutRes_ffi]
                           refine List.IsPrefix.trans ?_ (evaluate_io_events_mono_snd _ _)
                           exact List.prefix_refl _))
                    · have ec := evaluate_add_clock_eq prog { s1 with locals := env } rc st1 extra he hrc
                      simp only at ec
                      rw [ec] at hbig
                      rw [← hbig]
                      rcases rc with _ | (vs | exn | l | l | _ | o | _)
                      all_goals (simp only)
                      all_goals (try exact List.prefix_refl _)
                      all_goals (try exact absurd rfl hrc)
                      · by_cases hlen : vs.length ≠ ns.length
                        · rw [if_pos hlen, if_pos hlen]; exact List.prefix_refl _
                        · rw [if_neg hlen, if_neg hlen]
                          cases handler with
                          | none => exact List.prefix_refl _
                          | some hd =>
                            obtain ⟨_, _, r, lo⟩ := hd
                            simp only; rw [cutRes_ffi, cutRes_ffi]
                            exact ih r (setVars ns vs { st1 with locals := s1.locals })
                              (lexLtClock (by simp only [setVars]; omega)) extra
                      · cases handler with
                        | none => exact List.prefix_refl _
                        | some hd =>
                          obtain ⟨n, hp, _, lo⟩ := hd
                          simp only; rw [cutRes_ffi, cutRes_ffi]
                          exact ih hp (setVar n exn { st1 with locals := s1.locals })
                            (lexLtClock (by simp only [setVar]; omega)) extra
      all_goals (apply viaStart; rw [evaluate] at hto ⊢)
      all_goals (revert hto; repeat' split)
      all_goals (intro hto; try simp at hto)
      all_goals (try rfl)
      all_goals (try exact absurd hto (shMemOp_not_timeout _ _ _ _))
  exact key _ p s rfl extra

/-- Exact HOL `evaluate_add_clock_io_events_mono` (`loopPropsScript.sml:1217-1220`):
    `∀exps s extra. (SND(evaluate(exps,s))).ffi.io_events ≼
      (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_add_clock_io_events_mono"
  (words_as_type_indexed_bitvec)]
theorem evaluate_add_clock_io_events_mono (exps : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F) (extra : Nat) :
    (evaluate exps s).2.ffi.ioEvents <+:
      (evaluate exps { s with clock := s.clock + extra }).2.ffi.ioEvents :=
  evaluate_add_clock_io_events_mono_snd exps s extra

end LoopSemStateFiniteExact
end Flapjack
