import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkLemmas
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact

/-!
# loopProps `comp_syntax_ok` evaluator lemmas

Counterparts of `cakeml/pancake/semantics/loopPropsScript.sml`'s
`comp_syn_ok_upd_local_clock` (851) and `comp_syn_ok_lookup_locals_eq` (907)
over the exact evaluator (bead `flapjack-pxgp.17`).
-/

namespace Flapjack
namespace LoopSemStateFiniteExact

variable {width : Nat} [NeZero width] {F : Type}

/-- `t` agrees with `s` on every field except `locals` and `clock`. -/
def FrameLC (s t : LoopSemStateFiniteExact width F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem FrameLC.refl (s : LoopSemStateFiniteExact width F) : FrameLC s s := by
  cases s; rfl

theorem FrameLC.trans {s t u : LoopSemStateFiniteExact width F}
    (h1 : FrameLC s t) (h2 : FrameLC t u) : FrameLC s u := by
  cases s; cases t; cases u
  simp only [FrameLC, LoopSemStateFiniteExact.mk.injEq] at h1 h2 ⊢
  simp_all

theorem frameLC_of_fields {s t : LoopSemStateFiniteExact width F}
    (h : t.globals = s.globals ∧ t.memory = s.memory ∧ t.mdomain = s.mdomain ∧
      t.shMdomain = s.shMdomain ∧ t.code = s.code ∧ t.be = s.be ∧ t.ffi = s.ffi ∧
      t.baseAddr = s.baseAddr ∧ t.topAddr = s.topAddr) : FrameLC s t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  cases s; cases t; simp_all [FrameLC]

theorem frameLC_setVar (v : Nat) (w : WordLocW width) (s : LoopSemStateFiniteExact width F) :
    FrameLC s (setVar v w s) := by cases s; rfl

theorem frameLC_decClock (s : LoopSemStateFiniteExact width F) : FrameLC s (decClock s) := by
  cases s; rfl

theorem frameLC_cutState {live : NumSet} {s cut : LoopSemStateFiniteExact width F}
    (h : cutState live s = some cut) : FrameLC s cut := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10⟩ := cutState_some_frame h
  exact frameLC_of_fields ⟨h1, h2, h3, h4, h6, h7, h8, h9, h10⟩

theorem frameLC_cutRes (live : NumSet) (r : Option (LoopResultExact width))
    (s : LoopSemStateFiniteExact width F) : FrameLC s (cutRes live (r, s)).2 := by
  unfold cutRes
  cases r with
  | some _ => exact FrameLC.refl s
  | none =>
    simp only
    cases hc : cutState live s with
    | none => exact FrameLC.refl s
    | some cut =>
      simp only
      have hf := frameLC_cutState hc
      split
      · exact hf.trans (by cases cut; rfl)
      · exact hf.trans (frameLC_decClock cut)

theorem frameLC_loopArith {op : LoopArith} {s st : LoopSemStateFiniteExact width F}
    (h : loopArith s op = some st) : FrameLC s st := by
  cases op <;> simp only [loopArith] at h <;> split at h <;> (try split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first
      | exact frameLC_setVar _ _ _
      | exact (frameLC_setVar _ _ _).trans (frameLC_setVar _ _ _)

theorem frameLC_cutRes_pair (live : NumSet) (e : Option (LoopResultExact width) × LoopSemStateFiniteExact width F) :
    FrameLC e.2 (cutRes live e).2 := by
  obtain ⟨r, t⟩ := e; exact frameLC_cutRes live r t

theorem compSyntaxOk_evaluate_frame (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (l : NumSet) (hc : compSyntaxOkHOL l p = true) : FrameLC s (evaluate p s).2 := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock, sizeOf p) = x → ∀ l, compSyntaxOkHOL l p = true → FrameLC s (evaluate p s).2 := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx l hc
      have ih : ∀ (p' : HolLoopProg width) (s' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (s'.clock, sizeOf p') (s.clock, sizeOf p) →
          ∀ l', compSyntaxOkHOL l' p' = true → FrameLC s' (evaluate p' s').2 :=
        fun p' s' hlt => ih0 _ (hx ▸ hlt) p' s' rfl
      clear ih0 hx
      cases p
      case seq c1 c2 =>
        rw [compSyntaxOkHOL, Bool.and_eq_true] at hc
        rw [evaluate_seq]
        have h1 := ih c1 s (lexLt (Nat.le_refl _) (by simp +arith)) l hc.1
        cases he : evaluate c1 s with
        | mk r s1 =>
          rw [he] at h1; simp only at h1
          cases r with
          | none =>
            simp only
            exact h1.trans (ih c2 s1 (lexLt (evaluate_clock _ _ _ _ he) (by simp +arith)) _ hc.2)
          | some v => exact h1
      case ite cmp r1 ri c1 c2 live =>
        rw [compSyntaxOkHOL, Bool.and_eq_true, Bool.and_eq_true] at hc
        rw [evaluate]
        split
        · split
          · exact (ih c1 s (lexLt (Nat.le_refl _) (by simp +arith)) l hc.1.1).trans
              (frameLC_cutRes_pair _ _)
          · exact (ih c2 s (lexLt (Nat.le_refl _) (by simp +arith)) l hc.1.2).trans
              (frameLC_cutRes_pair _ _)
        · exact FrameLC.refl s
      case loop li body lo =>
        have hc' := hc
        rw [compSyntaxOkHOL, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          decide_eq_true_eq] at hc'
        obtain ⟨⟨rfl, rfl⟩, hb⟩ := hc'
        rw [evaluate]
        split
        · rename_i s1 hcr
          have hf1 : FrameLC s s1 := by
            have := frameLC_cutRes l none s; rw [hcr] at this; exact this
          have hs1 := cutRes_none_clock hcr
          rw [fix_clock_evaluate]
          have hbf := ih body s1 (lexLtClock hs1) l hb
          cases hbe : evaluate body s1 with
          | mk rb s2 =>
            rw [hbe] at hbf; simp only at hbf
            have hs2 : s2.clock < s.clock := Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ hbe) hs1
            rcases rb with _ | (vs | e | k | k | _ | o | _)
            · exact hf1.trans (hbf.trans (ih _ s2 (lexLtClock hs2) l hc))
            · exact hf1.trans hbf
            · exact hf1.trans hbf
            · cases k with
              | zero => exact hf1.trans (hbf.trans (frameLC_cutRes l none s2))
              | succ k => exact hf1.trans hbf
            · cases k with
              | zero => exact hf1.trans (hbf.trans (ih _ s2 (lexLtClock hs2) l hc))
              | succ k => exact hf1.trans hbf
            · exact hf1.trans hbf
            · exact hf1.trans hbf
            · exact hf1.trans hbf
        · exact frameLC_cutRes l none s
      all_goals (try (simp [compSyntaxOkHOL] at hc; done))
      all_goals (rw [evaluate]; repeat' split)
      all_goals (first
        | exact FrameLC.refl s
        | exact frameLC_setVar _ _ _
        | exact frameLC_loopArith ‹_›)
  exact key _ p s rfl l hc

theorem cutRes_lookup_nt {live : NumSet} {r r' : Option (LoopResultExact width)}
    {s s' : LoopSemStateFiniteExact width F} {n : Nat}
    (h : cutRes live (r, s) = (r', s')) (hne : r' ≠ some .timeOut) (hn : sptMem n live) :
    sptLookup n s'.locals = sptLookup n s.locals := by
  unfold cutRes at h
  cases r with
  | some x => simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
  | none =>
    simp only at h
    cases hc : cutState live s with
    | none => rw [hc] at h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
    | some cut =>
      rw [hc] at h; simp only at h
      split at h
      · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hne
      · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
        simp only [decClock]; exact cutState_lookup hc hn

theorem compSyntaxOk_lookup_locals (n : Nat) :
    ∀ (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (t : LoopSemStateFiniteExact width F) (l : NumSet),
      evaluate p s = (res, t) → res ≠ some .timeOut → compSyntaxOkHOL l p = true →
      sptMem n l → n ∉ holLoopAssignedVars p →
      sptLookup n t.locals = sptLookup n s.locals := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock, sizeOf p) = x → ∀ res t l, evaluate p s = (res, t) → res ≠ some .timeOut →
      compSyntaxOkHOL l p = true → sptMem n l → n ∉ holLoopAssignedVars p →
      sptLookup n t.locals = sptLookup n s.locals := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx
      have ih : ∀ (p' : HolLoopProg width) (s' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (s'.clock, sizeOf p') (s.clock, sizeOf p) →
          ∀ res t l, evaluate p' s' = (res, t) → res ≠ some .timeOut →
          compSyntaxOkHOL l p' = true → sptMem n l → n ∉ holLoopAssignedVars p' →
          sptLookup n t.locals = sptLookup n s'.locals :=
        fun p' s' hlt => ih0 _ (hx ▸ hlt) p' s' rfl
      clear ih0 hx
      intro res t l h hne hc hn hna
      cases p
      case seq c1 c2 =>
        rw [compSyntaxOkHOL, Bool.and_eq_true] at hc
        simp only [holLoopAssignedVars, List.mem_append, not_or] at hna
        rw [evaluate_seq] at h
        cases he : evaluate c1 s with
        | mk r1 s1 =>
          rw [he] at h
          cases r1 with
          | none =>
            simp only at h
            have e1 := ih c1 s (lexLt (Nat.le_refl _) (by simp +arith)) _ _ l he (by simp) hc.1 hn hna.1
            rw [← e1]
            exact ih c2 s1 (lexLt (evaluate_clock _ _ _ _ he) (by simp +arith)) _ _ _ h hne hc.2
              (comp_syn_cut_sets_mem_domain c1 l n ⟨hc.1, hn⟩) hna.2
          | some v =>
            simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact ih c1 s (lexLt (Nat.le_refl _) (by simp +arith)) _ _ l he hne hc.1 hn hna.1
      case ite cmp r1 ri c1 c2 live =>
        rw [compSyntaxOkHOL, Bool.and_eq_true, Bool.and_eq_true, holPropBool_eq_true] at hc
        obtain ⟨⟨hc1, hc2⟩, names, hlive⟩ := hc
        simp only [holLoopAssignedVars, List.mem_append, not_or] at hna
        have hnl : sptMem n live := by rw [hlive]; exact sptMem_sptListInsert_of _ _ _ hn
        rw [evaluate] at h
        have step : ∀ c, Prod.Lex (· < ·) (· < ·) (s.clock, sizeOf c)
              (s.clock, sizeOf (HolLoopProg.ite cmp r1 ri c1 c2 live)) →
            compSyntaxOkHOL l c = true → n ∉ holLoopAssignedVars c →
            cutRes live (evaluate c s) = (res, t) → sptLookup n t.locals = sptLookup n s.locals := by
          intro c hlex hcc hnac hcut
          cases he : evaluate c s with
          | mk rc sc =>
            rw [he] at hcut
            have hrc : rc ≠ some .timeOut := by
              rintro rfl; unfold cutRes at hcut; simp only [Prod.mk.injEq] at hcut
              exact hne hcut.1.symm
            rw [cutRes_lookup_nt hcut hne hnl]
            exact ih c s hlex _ _ l he hrc hcc hn hnac
        split at h
        · split at h
          · exact step c1 (lexLt (Nat.le_refl _) (by simp +arith)) hc1 hna.1 h
          · exact step c2 (lexLt (Nat.le_refl _) (by simp +arith)) hc2 hna.2 h
        · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
      case loop li body lo =>
        have hc' := hc
        rw [compSyntaxOkHOL, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          decide_eq_true_eq] at hc'
        obtain ⟨⟨rfl, rfl⟩, hb⟩ := hc'
        simp only [holLoopAssignedVars] at hna
        rw [evaluate] at h
        split at h
        · rename_i s1 hcr
          have e1 := cutRes_lookup_nt hcr (by simp) hn
          have hs1 := cutRes_none_clock hcr
          rw [fix_clock_evaluate] at h
          rw [← e1]
          cases hbe : evaluate body s1 with
          | mk rb s2 =>
            rw [hbe] at h
            have hs2 : s2.clock < s.clock := Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ hbe) hs1
            have ihb := fun hrb => ih body s1 (lexLtClock hs1) _ _ l hbe hrb hb hn hna
            rcases rb with _ | (vs | e | k | k | _ | o | _)
            · simp only at h
              rw [← ihb (by simp)]
              exact ih _ s2 (lexLtClock hs2) _ _ l h hne hc hn hna
            · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ihb (by simp)
            · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ihb (by simp)
            · cases k with
              | zero =>
                simp only at h
                rw [cutRes_lookup_nt h hne hn]; exact ihb (by simp)
              | succ k => simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ihb (by simp)
            · cases k with
              | zero =>
                simp only at h
                rw [← ihb (by simp)]
                exact ih _ s2 (lexLtClock hs2) _ _ l h hne hc hn hna
              | succ k => simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ihb (by simp)
            · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [exitLoop] at hne
            · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ihb (by simp)
            · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ihb (by simp)
        · exact cutRes_lookup_nt h hne hn
      all_goals (try (simp [compSyntaxOkHOL] at hc; done))
      all_goals (rw [evaluate] at h; revert h; repeat' split)
      all_goals intro h
      all_goals (try (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h))
      all_goals (try rfl)
      all_goals (try (simp only [holLoopAssignedVars, List.mem_singleton] at hna
                      exact sptLookup_setVar_ne hna _ _))
      all_goals (try (exact loopArith_lookup ‹loopArith _ _ = some _› hna))
  exact fun p s => key _ p s rfl

namespace LoopPropsCompSyntaxEvalFiniteSupport

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

end LoopPropsCompSyntaxEvalFiniteSupport

/-- Exact HOL `comp_syn_ok_upd_local_clock` (`loopPropsScript.sml:851-855`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_upd_local_clock"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem comp_syn_ok_upd_local_clock :
    ∀ (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (t : LoopSemStateFiniteExact width F) (l : NumSet),
      evaluate p s = (res, t) ∧ compSyntaxOkHOL l p = true →
      t = { s with locals := t.locals, clock := t.clock } := by
  intro p s res t l ⟨h, hc⟩
  have := compSyntaxOk_evaluate_frame p s l hc
  rw [h] at this; exact this

/-- Exact HOL `comp_syn_ok_lookup_locals_eq` (`loopPropsScript.sml:907-912`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syn_ok_lookup_locals_eq"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem comp_syn_ok_lookup_locals_eq :
    ∀ (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (t : LoopSemStateFiniteExact width F) (l : NumSet)
      (n : Nat),
      evaluate p s = (res, t) ∧ res ≠ some .timeOut ∧ compSyntaxOkHOL l p = true ∧
        sptMem n l ∧ n ∉ holLoopAssignedVars p →
      sptLookup n t.locals = sptLookup n s.locals :=
  fun p s res t l n ⟨h, hne, hc, hn, hna⟩ => compSyntaxOk_lookup_locals n p s res t l h hne hc hn hna

end LoopSemStateFiniteExact
end Flapjack
