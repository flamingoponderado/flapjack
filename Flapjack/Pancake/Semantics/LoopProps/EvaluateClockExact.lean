import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# loopProps clock lemmas over the exact loopSem evaluator

Counterparts of `cakeml/pancake/semantics/loopPropsScript.sml`'s
`eval_upd_clock_eq` (line 946) and `evaluate_add_clock_eq` (line 985) over
`LoopSemStateFiniteExact.eval` / `LoopSemStateFiniteExact.evaluate`
(bead `flapjack-pxgp.9`).
-/

namespace Flapjack
namespace LoopSemStateFiniteExact

variable {width : Nat} [NeZero width] {F : Type}

namespace LoopPropsClockFiniteSupport

/-- Local same-module witness for the canonical finite-support
`LoopSemStateFiniteExact` carrier used by the `fmap_as_finite_support := [globals]`
qualified ports in this module (re-exports the checked witness of
`Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopPropsClockFiniteSupport

/-- Exact HOL `eval_upd_clock_eq` (`loopPropsScript.sml:946-957`):
    `!t e ck. eval (t with clock := ck) e = eval t e`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "eval_upd_clock_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem eval_upd_clock_eq (t : LoopSemStateFiniteExact width F) :
    ∀ (e : HolLoopExp width) (ck : Nat), eval { t with clock := ck } e = eval t e
  | .const _, _ => by simp only [eval]
  | .var _, _ => by simp only [eval]
  | .lookup _, _ => by simp only [eval]
  | .load a, ck => by
      simp only [eval, eval_upd_clock_eq t a ck]; split <;> rfl
  | .op o args, ck => by
      simp only [eval]
      have hm : ∀ e ∈ args, eval { t with clock := ck } e = eval t e :=
        fun e _ => eval_upd_clock_eq t e ck
      simp only [List.attach_map_val (f := eval { t with clock := ck }),
        List.attach_map_val (f := eval t), List.map_congr_left hm]
  | .shift sh a b, ck => by
      simp only [eval, eval_upd_clock_eq t a ck, eval_upd_clock_eq t b ck]
  | .baseAddr, _ => by simp only [eval]
  | .topAddr, _ => by simp only [eval]

theorem getVars_upd_clock (t : LoopSemStateFiniteExact width F) (ck : Nat) :
    ∀ ns : List Nat, getVars ns { t with clock := ck } = getVars ns t
  | [] => rfl
  | n :: ns => by simp only [getVars, getVars_upd_clock t ck ns]

theorem getVarImm_upd_clock (t : LoopSemStateFiniteExact width F) (ck : Nat)
    (ri : RegImm (BitVec width)) : getVarImm ri { t with clock := ck } = getVarImm ri t := by
  cases ri <;> rfl

theorem loopArith_upd_clock (t : LoopSemStateFiniteExact width F) (ck : Nat) (op : LoopArith) :
    loopArith { t with clock := ck } op = (loopArith t op).map ({ · with clock := ck }) := by
  cases op <;> simp only [loopArith] <;> split <;> (try split) <;> rfl

theorem memStore_upd_clock (t : LoopSemStateFiniteExact width F) (ck : Nat) (a : BitVec width)
    (v : WordLocW width) :
    memStore a v { t with clock := ck } = (memStore a v t).map ({ · with clock := ck }) := by
  unfold memStore; split <;> rfl

theorem shMemOp_upd_clock (op : WordMemOp) (v : Nat) (a : BitVec width)
    (t : LoopSemStateFiniteExact width F) (ck : Nat) :
    shMemOp op v a { t with clock := ck } =
      ((shMemOp op v a t).1, { (shMemOp op v a t).2 with clock := ck }) := by
  cases op <;> simp only [shMemOp, shMemLoad, shMemStore] <;>
    (repeat' split) <;> first | rfl | (simp_all; done)

theorem cutState_upd_clock (live : NumSet) (t : LoopSemStateFiniteExact width F) (c : Nat) :
    cutState live { t with clock := c } = (cutState live t).map ({ · with clock := c }) := by
  unfold cutState; split <;> rfl

theorem cutRes_add_clock (live : NumSet) (r : Option (LoopResultExact width))
    (t st : LoopSemStateFiniteExact width F) (r' : Option (LoopResultExact width)) (ck : Nat)
    (h : cutRes live (r, t) = (r', st)) (hne : r' ≠ some .timeOut) :
    cutRes live (r, { t with clock := t.clock + ck }) = (r', { st with clock := st.clock + ck }) := by
  cases r with
  | some v => simp only [cutRes, Prod.mk.injEq] at h ⊢; obtain ⟨rfl, rfl⟩ := h; simp
  | none =>
    simp only [cutRes] at h ⊢
    rw [cutState_upd_clock]
    cases hc : cutState live t with
    | none => rw [hc] at h; simp only [Option.map, Prod.mk.injEq] at h ⊢; obtain ⟨rfl, rfl⟩ := h; simp
    | some s1 =>
      rw [hc] at h; simp only [Option.map] at h ⊢
      have hs1 := cutState_clock hc
      by_cases hz : s1.clock = 0
      · simp only [hz, if_true, Prod.mk.injEq] at h; exact absurd h.1.symm hne
      · simp only [hz, if_false, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        have hz' : t.clock + ck ≠ 0 := by omega
        simp only [hz', if_false, decClock, Prod.mk.injEq, true_and]
        cases s1; simp only [LoopSemStateFiniteExact.mk.injEq, true_and, and_true] at hs1 hz ⊢; omega

/-- Exact HOL `evaluate_add_clock_eq` (`loopPropsScript.sml:985-...`):
    `!p t res st ck. evaluate (p,t) = (res,st) /\ res <> SOME TimeOut ==>
      evaluate (p,t with clock := t.clock + ck) = (res,st with clock := st.clock + ck)`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "evaluate_add_clock_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_add_clock_eq (p : HolLoopProg width) (t : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (st : LoopSemStateFiniteExact width F) (ck : Nat)
    (h : evaluate p t = (res, st)) (hne : res ≠ some .timeOut) :
    evaluate p { t with clock := t.clock + ck } = (res, { st with clock := st.clock + ck }) := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (t : LoopSemStateFiniteExact width F),
      (t.clock, sizeOf p) = x → ∀ res st ck, evaluate p t = (res, st) → res ≠ some .timeOut →
      evaluate p { t with clock := t.clock + ck } = (res, { st with clock := st.clock + ck }) := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p t hx
      have ih : ∀ (p' : HolLoopProg width) (t' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (t'.clock, sizeOf p') (t.clock, sizeOf p) →
          ∀ res st ck, evaluate p' t' = (res, st) → res ≠ some .timeOut →
          evaluate p' { t' with clock := t'.clock + ck } = (res, { st with clock := st.clock + ck }) :=
        fun p' t' hlt => ih0 _ (hx ▸ hlt) p' t' rfl
      clear ih0 hx
      intro res st ck h hne
      cases p
      case seq c1 c2 =>
        rw [evaluate] at h; rw [evaluate]
        have lex1 : Prod.Lex (· < ·) (· < ·) (t.clock, sizeOf c1) (t.clock, sizeOf (c1.seq c2)) :=
          lexLt (Nat.le_refl _) (by simp +arith)
        split at h
        · split
          · rename_i s1 heq1 s1' heq2
            rw [fix_clock_evaluate] at heq1 heq2
            have e1 := ih c1 t lex1 none s1 ck heq1 (by simp)
            rw [e1] at heq2; simp only [Prod.mk.injEq, true_and] at heq2; subst heq2
            exact ih c2 s1 (lexLt (evaluate_clock _ _ _ _ heq1) (by simp +arith)) res st ck h hne
          · rename_i s1 heq1 r2 s2 hr2 heq2
            rw [fix_clock_evaluate] at heq1 heq2
            have e1 := ih c1 t lex1 none s1 ck heq1 (by simp)
            rw [e1] at heq2; simp only [Prod.mk.injEq] at heq2
            exact absurd heq2.1.symm hr2
        · rename_i r1 s1 hr1 heq1
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          rw [fix_clock_evaluate] at heq1
          have e1 := ih c1 t lex1 _ _ ck heq1 hne
          split
          · rename_i s1' heq2
            rw [fix_clock_evaluate, e1] at heq2; simp only [Prod.mk.injEq] at heq2
            exact absurd heq2.1 hr1
          · rename_i r2 s2 hr2 heq2
            rw [fix_clock_evaluate, e1] at heq2; simp only [Prod.mk.injEq] at heq2
            obtain ⟨rfl, rfl⟩ := heq2; rfl
      case ite cmp r1 ri c1 c2 live =>
        rw [evaluate] at h; rw [evaluate]
        simp only [getVarImm_upd_clock]
        have step : ∀ c, Prod.Lex (· < ·) (· < ·) (t.clock, sizeOf c)
              (t.clock, sizeOf (HolLoopProg.ite cmp r1 ri c1 c2 live)) →
            cutRes live (evaluate c t) = (res, st) →
            cutRes live (evaluate c { t with clock := t.clock + ck }) =
              (res, { st with clock := st.clock + ck }) := by
          intro c hlex hcut
          cases he : evaluate c t with
          | mk rr ss =>
            rw [he] at hcut
            have hrr : rr ≠ some .timeOut := by
              intro hbad; subst hbad; simp only [cutRes, Prod.mk.injEq] at hcut
              exact hne hcut.1.symm
            rw [ih c t hlex rr ss ck he hrr]
            exact cutRes_add_clock live rr ss st res ck hcut hne
        revert h; split
        · intro h
          split
          · rename_i hb; simp only [hb, if_true] at h
            exact step c1 (lexLt (Nat.le_refl _) (by simp +arith)) h
          · rename_i hb; simp only [hb] at h
            exact step c2 (lexLt (Nat.le_refl _) (by simp +arith)) h
        · intro h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
      case mark q =>
        rw [evaluate] at h; rw [evaluate]
        exact ih q t (lexLt (Nat.le_refl _) (by simp +arith)) res st ck h hne
      case loop li body lo =>
        rw [evaluate] at h; rw [evaluate]
        split at h
        · rename_i s1 hc
          have hs1 := cutRes_none_clock hc
          have hc' := cutRes_add_clock li none t s1 none ck hc (by simp)
          split
          · rename_i s1' hc2
            rw [hc'] at hc2; simp only [Prod.mk.injEq, true_and] at hc2; subst hc2
            split at h
            · rename_i s2 hb
              rw [fix_clock_evaluate] at hb
              have eb := ih body s1 (lexLtClock hs1) _ _ ck hb (by simp)
              have hs2 := evaluate_clock _ _ _ _ hb
              split
              · rename_i s2' hb2
                rw [fix_clock_evaluate, eb] at hb2; simp only [Prod.mk.injEq, true_and] at hb2
                subst hb2
                exact ih _ s2 (lexLtClock (by omega)) res st ck h hne
              · rename_i s2' hb2; rw [fix_clock_evaluate, eb] at hb2; simp at hb2
              · rename_i s2' hb2; rw [fix_clock_evaluate, eb] at hb2; simp at hb2
              · rename_i r' s2' m1 m2 m3 hb2; rw [fix_clock_evaluate, eb] at hb2
                simp only [Prod.mk.injEq] at hb2; exact absurd hb2.1.symm m1
            · rename_i s2 hb
              rw [fix_clock_evaluate] at hb
              have eb := ih body s1 (lexLtClock hs1) _ _ ck hb (by simp)
              have hs2 := evaluate_clock _ _ _ _ hb
              split
              · rename_i s2' hb2; rw [fix_clock_evaluate, eb] at hb2; simp at hb2
              · rename_i s2' hb2
                rw [fix_clock_evaluate, eb] at hb2; simp only [Prod.mk.injEq, true_and] at hb2
                subst hb2
                exact ih _ s2 (lexLtClock (by omega)) res st ck h hne
              · rename_i s2' hb2; rw [fix_clock_evaluate, eb] at hb2; simp at hb2
              · rename_i r' s2' m1 m2 m3 hb2; rw [fix_clock_evaluate, eb] at hb2
                simp only [Prod.mk.injEq] at hb2; exact absurd hb2.1.symm m2
            · rename_i s2 hb
              rw [fix_clock_evaluate] at hb
              have eb := ih body s1 (lexLtClock hs1) _ _ ck hb (by simp)
              split
              · rename_i s2' hb2; rw [fix_clock_evaluate, eb] at hb2; simp at hb2
              · rename_i s2' hb2; rw [fix_clock_evaluate, eb] at hb2; simp at hb2
              · rename_i s2' hb2
                rw [fix_clock_evaluate, eb] at hb2; simp only [Prod.mk.injEq, true_and] at hb2
                subst hb2
                exact cutRes_add_clock lo none s2 st res ck h hne
              · rename_i r' s2' m1 m2 m3 hb2; rw [fix_clock_evaluate, eb] at hb2
                simp only [Prod.mk.injEq] at hb2; exact absurd hb2.1.symm m3
            · rename_i r0 s2 n1 n2 n3 hb
              rw [fix_clock_evaluate] at hb
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              have hr0 : r0 ≠ some .timeOut := by
                intro hbad; subst hbad; exact hne rfl
              have eb := ih body s1 (lexLtClock hs1) _ _ ck hb hr0
              split
              · rename_i s2' hb2; rw [fix_clock_evaluate, eb] at hb2
                simp only [Prod.mk.injEq] at hb2; exact absurd hb2.1 n1
              · rename_i s2' hb2; rw [fix_clock_evaluate, eb] at hb2
                simp only [Prod.mk.injEq] at hb2; exact absurd hb2.1 n2
              · rename_i s2' hb2; rw [fix_clock_evaluate, eb] at hb2
                simp only [Prod.mk.injEq] at hb2; exact absurd hb2.1 n3
              · rename_i r' s2' m1 m2 m3 hb2; rw [fix_clock_evaluate, eb] at hb2
                simp only [Prod.mk.injEq] at hb2; obtain ⟨rfl, rfl⟩ := hb2; rfl
          · rename_i hnot; exact (hnot _ hc').elim
        · rename_i hnot
          have hsh := cutRes_add_clock li none t st res ck h hne
          split
          · rename_i s1' hc2
            rw [hsh] at hc2; simp only [Prod.mk.injEq] at hc2
            obtain ⟨rfl, -⟩ := hc2; exact (hnot st h).elim
          · exact hsh
      case call ret dest args handler =>
        rw [evaluate] at h; rw [evaluate]
        simp only [getVars_upd_clock]
        cases hg : getVars args t with
        | none => simp only [hg] at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
        | some argvals =>
          simp only [hg] at h ⊢
          cases hfc : findCode dest argvals t.code with
          | none => simp only [hfc] at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
          | some ep =>
            obtain ⟨env, prog⟩ := ep
            simp only [hfc] at h ⊢
            cases ret with
            | none =>
              simp only at h ⊢
              by_cases hh : handler.isSome = true
              · simp only [hh, if_true] at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
              · simp only [hh, if_false, Bool.false_eq_true] at h ⊢
                by_cases hz : t.clock = 0
                · simp only [hz, dite_true, Prod.mk.injEq] at h; exact absurd h.1.symm hne
                · have hz' : t.clock + ck ≠ 0 := by omega
                  simp only [hz, hz', dite_false] at h ⊢
                  have hst : ({ decClock { t with clock := t.clock + ck } with locals := env } :
                      LoopSemStateFiniteExact width F) =
                      { ({ decClock t with locals := env } : LoopSemStateFiniteExact width F) with
                        clock := ({ decClock t with locals := env } :
                          LoopSemStateFiniteExact width F).clock + ck } := by
                    cases t; simp only [decClock, LoopSemStateFiniteExact.mk.injEq, true_and,
                      and_true] at hz ⊢; omega
                  rw [hst]
                  cases he : evaluate prog { decClock t with locals := env } with
                  | mk r s' =>
                    rw [he] at h
                    have hr : r ≠ some .timeOut := by
                      rintro rfl; simp only [Prod.mk.injEq] at h; exact hne h.1.symm
                    rw [ih prog _ (lexLtClock (by simp only [decClock]; omega)) r s' ck he hr]
                    rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;>
                      simp only [Prod.mk.injEq] at h ⊢ <;> obtain ⟨rfl, rfl⟩ := h <;> simp
            | some nl =>
              obtain ⟨ns, live⟩ := nl
              simp only at h ⊢
              by_cases hnd : ¬ ns.Nodup
              · simp only [hnd] at h ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
              simp only [hnd, if_false] at h ⊢
              split at h
              · rename_i s1 hc
                have hs1 := cutRes_none_clock hc
                have hc' := cutRes_add_clock live none t s1 none ck hc (by simp)
                split
                · rename_i s1' hc2
                  rw [hc'] at hc2; simp only [Prod.mk.injEq, true_and] at hc2; subst hc2
                  rw [fix_clock_evaluate] at h
                  rw [fix_clock_evaluate]
                  cases he : evaluate prog { s1 with locals := env } with
                  | mk r1 st1 =>
                    rw [he] at h
                    have hr1 : r1 ≠ some .timeOut := by
                      rintro rfl; simp only [Prod.mk.injEq] at h; exact hne h.1.symm
                    have hst1 := evaluate_clock _ _ _ _ he
                    have hst1' : st1.clock < t.clock := Nat.lt_of_le_of_lt hst1 hs1
                    have ef := ih prog { s1 with locals := env } (lexLtClock hs1) r1 st1 ck he hr1
                    simp only at ef
                    rw [ef]
                    rcases r1 with _ | (vs | exn | l | l | _ | o | _)
                    all_goals (simp only at h ⊢)
                    all_goals (try (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))
                    all_goals (try (exact absurd rfl hr1))
                    · by_cases hlen : vs.length ≠ ns.length
                      · rw [if_pos hlen] at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
                      · rw [if_neg hlen] at h ⊢
                        cases handler with
                        | none => simp only at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
                        | some hd =>
                          obtain ⟨_, _, r, liveOut⟩ := hd
                          simp only at h ⊢
                          cases he2 : evaluate r (setVars ns vs { st1 with locals := s1.locals }) with
                          | mk rr ss =>
                            rw [he2] at h
                            have hrr : rr ≠ some .timeOut := by
                              rintro rfl; simp only [cutRes, Prod.mk.injEq] at h; exact hne h.1.symm
                            have e2 := ih r (setVars ns vs { st1 with locals := s1.locals })
                              (lexLtClock (by simp only [setVars]; omega)) rr ss ck he2 hrr
                            simp only [setVars] at e2 ⊢
                            rw [e2]
                            exact cutRes_add_clock liveOut rr ss st res ck h hne
                    · cases handler with
                      | none => simp only at h ⊢; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
                      | some hd =>
                        obtain ⟨n, hp, _, liveOut⟩ := hd
                        simp only at h ⊢
                        cases he2 : evaluate hp (setVar n exn { st1 with locals := s1.locals }) with
                        | mk rr ss =>
                          rw [he2] at h
                          have hrr : rr ≠ some .timeOut := by
                            rintro rfl; simp only [cutRes, Prod.mk.injEq] at h; exact hne h.1.symm
                          have e2 := ih hp (setVar n exn { st1 with locals := s1.locals })
                            (lexLtClock (by simp only [setVar]; omega)) rr ss ck he2 hrr
                          simp only [setVar] at e2 ⊢
                          rw [e2]
                          exact cutRes_add_clock liveOut rr ss st res ck h hne
                · rename_i hnot; exact (hnot _ hc').elim
              · rename_i hnot
                have hsh := cutRes_add_clock live none t st res ck h hne
                split
                · rename_i s1' hc2
                  rw [hsh] at hc2; simp only [Prod.mk.injEq] at hc2
                  obtain ⟨rfl, -⟩ := hc2; exact (hnot st h).elim
                · exact hsh
      case ffi idx p1 l1 p2 l2 cutset =>
        rw [evaluate] at h; rw [evaluate]
        simp only [cutState_upd_clock]
        rcases hl1 : sptLookup l1 t.locals with _ | (w1 | ⟨_, _⟩) <;>
        rcases hp1 : sptLookup p1 t.locals with _ | (w2 | ⟨_, _⟩) <;>
        rcases hl2 : sptLookup l2 t.locals with _ | (w3 | ⟨_, _⟩) <;>
        rcases hp2 : sptLookup p2 t.locals with _ | (w4 | ⟨_, _⟩) <;>
        rcases hcs : cutState cutset t with _ | s' <;>
        simp only [hl1, hp1, hl2, hp2, hcs, Option.map_some, Option.map_none] at h ⊢
        all_goals (try (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl))
        have hsc := cutState_clock hcs
        rcases hr1 : readBytearrayWordHOL w2 w1.toNat
            (memLoadByteAuxExact s'.memory s'.mdomain s'.be) with _ | bytes <;>
        rcases hr2 : readBytearrayWordHOL w4 w3.toNat
            (memLoadByteAuxExact s'.memory s'.mdomain s'.be) with _ | bytes2 <;>
        simp only [hr1, hr2] at h ⊢
        all_goals (try (obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rw [hsc]; done))
        rcases hf : callFFIHOL s'.ffi (.extCall idx) bytes bytes2 with ⟨nf, nb⟩ | o <;>
        simp only [hf] at h ⊢ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        all_goals (simp only [callEnv, hsc])
      case tick =>
        rw [evaluate] at h; rw [evaluate]
        by_cases hz : t.clock = 0
        · simp only [hz, if_true, Prod.mk.injEq] at h; exact absurd h.1.symm hne
        · simp only [hz, if_false, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          have hz' : t.clock + ck ≠ 0 := by omega
          simp only [hz', if_false, decClock, Prod.mk.injEq, true_and]
          cases t; simp only [LoopSemStateFiniteExact.mk.injEq, true_and, and_true] at hz ⊢; omega
      all_goals (rw [evaluate] at h; rw [evaluate])
      all_goals (try simp only [eval_upd_clock_eq, getVars_upd_clock,
        loopArith_upd_clock, memStore_upd_clock, shMemOp_upd_clock] at h ⊢)
      all_goals (revert h; repeat' split)
      all_goals (try simp only [Option.map_some, Option.map_none])
      all_goals (repeat' split)
      all_goals (intro h)
      all_goals (try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl))
      all_goals (try (simp only [Prod.mk.injEq] at h; done))
      all_goals (try (clear ih; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp_all; done))
      all_goals (try (have hc := congrArg (fun x => x.2.clock) h
                      simp only [shMemOp_clock] at hc; rw [h]; simp only [hc]; done))
      all_goals (try (have := memStore_clock ‹_›; clear ih
                      simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp_all; done))
      all_goals (try (have := loopArith_clock ‹_›; clear ih
                      simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp_all; done))
  exact key _ p t rfl res st ck h hne

end LoopSemStateFiniteExact
end Flapjack
