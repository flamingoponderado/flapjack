import Flapjack.Pancake.Proofs.CrepInline.UnreachElim
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd

/-!
# crep_inline: `unreach_elim` evaluation lemmas

Exact counterparts of `cakeml/pancake/proofs/crep_inlineProofScript.sml:1569-1662`
(`unreach_elim_not_none_evaluate`, `unreach_elim_correct`), bead
`flapjack-pxn.18.5.5.46.3`, over the tagged exact `unreachElimHOLExact`
(`unreach_elim_def`) and the exact Crep evaluator `evalCrepSemHOLProgExact`
(`evaluate_def`) on the reviewed `CrepSemHOLState` carrier.
-/

namespace Flapjack

namespace CrepInlineUnreachElimEvaluate

/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- Exact HOL `unreach_elim_not_none_evaluate`
    (`crep_inlineProofScript.sml:1569-1573`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_not_none_evaluate"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem unreachElimNotNoneEvaluate {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (p1 : CrepProgHOL width) (e : CrepEarlyExitHOL),
      unreachElimHOLExact p = (p1, some e) ∧ evalCrepSemHOLProgExact s p = (r, s') →
      ∃ e, r = some e := by
  intro p
  fun_induction unreachElimHOLExact p <;> intro s r s' p1 e ⟨hu, hev⟩
  -- Return / Raise / Break / Continue: the evaluator always reports a result.
  · rw [evalCrepSemHOLProgExact_return] at hev
    split at hev <;> (simp only [Prod.mk.injEq] at hev; exact ⟨_, hev.1.symm⟩)
  · rw [evalCrepSemHOLProgExact_raise] at hev
    exact ⟨_, (Prod.mk.inj hev).1.symm⟩
  · rw [evalCrepSemHOLProgExact_break] at hev
    exact ⟨_, (Prod.mk.inj hev).1.symm⟩
  · rw [evalCrepSemHOLProgExact_continue] at hev
    exact ⟨_, (Prod.mk.inj hev).1.symm⟩
  -- Seq whose first component reports an exit.
  · rename_i first second first' firstExit hfirst hsome ih
    obtain ⟨_, rfl⟩ := Prod.mk.inj hu
    rw [evalCrepSemHOLProgExact_seq_holShape] at hev
    rcases h1 : evalCrepSemHOLProgExact s first with ⟨res, s1⟩
    obtain ⟨e1, rfl⟩ := ih s res s1 first' e ⟨hfirst, h1⟩
    rw [h1] at hev
    simp only [reduceCtorEq, if_false, Prod.mk.injEq] at hev
    exact ⟨e1, hev.1.symm⟩
  -- Seq whose first component reports no exit.
  · rename_i first second first' firstExit hfirst hnone second' secondExit hsecond ih1 ih2
    obtain ⟨_, rfl⟩ := Prod.mk.inj hu
    rw [evalCrepSemHOLProgExact_seq_holShape] at hev
    rcases h1 : evalCrepSemHOLProgExact s first with ⟨res, s1⟩
    rw [h1] at hev
    dsimp only at hev
    by_cases hres : res = none
    · rw [if_pos hres] at hev
      exact ih2 s1 r s' second' e ⟨hsecond, hev⟩
    · rw [if_neg hres] at hev
      have hr : res = r := (Prod.mk.inj hev).1
      exact Option.ne_none_iff_exists'.mp (hr ▸ hres)
  -- Dec.
  · rename_i name value body body' bodyExit hbody ih
    obtain ⟨_, rfl⟩ := Prod.mk.inj hu
    rw [evalCrepSemHOLProgExact_dec_holShape] at hev
    split at hev
    · rename_i v _
      rcases h1 : evalCrepSemHOLProgExact
          { s with locals := s.locals.updateEq (name, v) } body with ⟨res, st⟩
      rw [h1] at hev
      obtain ⟨rfl, _⟩ := Prod.mk.inj hev
      exact ih _ res st body' e ⟨hbody, h1⟩
    · exact ⟨_, (Prod.mk.inj hev).1.symm⟩
  -- If: a merged exit requires an exit from both branches.
  · rename_i condition thenBranch elseBranch then' thenExit hthen else' elseExit helse ihThen ihElse
    obtain ⟨_, hmerge⟩ := Prod.mk.inj hu
    have hboth : ∃ a b, thenExit = some a ∧ elseExit = some b := by
      rcases thenExit with _ | a <;> rcases elseExit with _ | b <;>
        (try cases a) <;> (try cases b) <;> simp_all [crepMergeExitHOL]
    obtain ⟨a, b, rfl, rfl⟩ := hboth
    rw [evalCrepSemHOLProgExact_ite_holShape] at hev
    split at hev
    · rename_i w _
      by_cases hw : w ≠ 0
      · rw [if_pos hw] at hev
        exact ihThen s r s' then' a ⟨hthen, hev⟩
      · rw [if_neg hw] at hev
        exact ihElse s r s' else' b ⟨helse, hev⟩
    · exact ⟨_, (Prod.mk.inj hev).1.symm⟩
  -- While: unreach_elim reports no exit.
  · simp at hu
  -- Tail Call: every evaluation outcome is a result.
  · rw [evalCrepSemHOLProgExact_call_holShape] at hev
    repeat' split at hev
    all_goals first
      | exact ⟨_, (Prod.mk.inj hev).1.symm⟩
      | (simp only [Prod.mk.injEq] at hev; exact ⟨_, hev.1.symm⟩)
      | skip
    all_goals first
      | (simp_all; done)
      | (have hr := (Prod.mk.inj hev).1
         subst hr
         exact Option.ne_none_iff_exists'.mp (by assumption))
  -- Returning calls and every other constructor: no exit.
  · simp at hu
  · simp at hu
  · simp at hu

/-- Size of a strict subprogram is below its `Seq`/`Dec`/`If`/`While` parent;
    local support for the lexicographic induction. -/
private theorem lexSmaller {width : Nat} [NeZero width] {σ : Type}
    {s t : CrepSemHOLState width σ} {p q : CrepProgHOL width}
    (hclock : t.clock ≤ s.clock) (hsize : sizeOf p < sizeOf q) :
    Prod.Lex Nat.lt Nat.lt (t.clock, sizeOf p) (s.clock, sizeOf q) := by
  rw [Prod.lex_def]
  by_cases hlt : t.clock < s.clock
  · exact Or.inl hlt
  · exact Or.inr ⟨by omega, hsize⟩

private theorem lexClock {width : Nat} [NeZero width] {σ : Type}
    {s t : CrepSemHOLState width σ} {p q : CrepProgHOL width}
    (hclock : t.clock < s.clock) :
    Prod.Lex Nat.lt Nat.lt (t.clock, sizeOf p) (s.clock, sizeOf q) := by
  rw [Prod.lex_def]
  exact Or.inl hclock

/-- Evaluation does not increase the clock, read off an evaluation equation. -/
private theorem clockLeOfEval {width : Nat} [NeZero width] {σ : Type}
    {s t : CrepSemHOLState width σ} {p : CrepProgHOL width}
    {r : Option (CrepResultHOLExact width)}
    (h : evalCrepSemHOLProgExact s p = (r, t)) : t.clock ≤ s.clock := by
  have := evalCrepSemHOLProgExact_clock_le s p
  rw [h] at this
  exact this

/-- Exact HOL `unreach_elim_correct` (`crep_inlineProofScript.sml:1608-1613`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem unreachElimCorrect {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (p1 : CrepProgHOL width) (s1 : Option CrepEarlyExitHOL),
      evalCrepSemHOLProgExact s p = (r, s') ∧ r ≠ some .error ∧
        unreachElimHOLExact p = (p1, s1) →
      evalCrepSemHOLProgExact s p1 = (r, s') := by
  intro p s
  refine evalCrepSemHOLProgExact_inductLex (motive := fun p s =>
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (p1 : CrepProgHOL width) (s1 : Option CrepEarlyExitHOL),
      evalCrepSemHOLProgExact s p = (r, s') ∧ r ≠ some .error ∧
        unreachElimHOLExact p = (p1, s1) →
      evalCrepSemHOLProgExact s p1 = (r, s')) ?_ p s
  intro p s ih r s' p1 x ⟨hev, hne, hu⟩
  cases p with
  | seq a b =>
      rcases ha : unreachElimHOLExact a with ⟨a', ea⟩
      rw [unreachElimHOLExact, ha] at hu
      rw [evalCrepSemHOLProgExact_seq_holShape] at hev
      rcases h1 : evalCrepSemHOLProgExact s a with ⟨res, t⟩
      rw [h1] at hev
      dsimp only at hev
      have hresErr : res ≠ some .error := by
        intro hres
        rw [if_neg (by simp [hres])] at hev
        exact hne ((Prod.mk.inj hev).1 ▸ hres)
      have ha' := ih a s (lexSmaller (Nat.le_refl _) (by first | omega | (simp; omega) | simp)) res t a' ea ⟨h1, hresErr, ha⟩
      by_cases hsome : ea.isSome
      · simp only [hsome, if_true, Prod.mk.injEq] at hu
        obtain ⟨rfl, _⟩ := hu
        obtain ⟨e, rfl⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨e1, rfl⟩ := unreachElimNotNoneEvaluate a s res t a' e ⟨ha, h1⟩
        simp only [reduceCtorEq, if_false] at hev
        rw [ha', hev]
      · simp only [hsome, Bool.false_eq_true, if_false] at hu
        rcases hb : unreachElimHOLExact b with ⟨b', eb⟩
        rw [hb] at hu
        obtain ⟨rfl, _⟩ := Prod.mk.inj hu
        rw [evalCrepSemHOLProgExact_seq_holShape, ha']
        try dsimp only
        by_cases hres : res = none
        · rw [if_pos hres] at hev ⊢
          have ht := evalCrepSemHOLProgExact_clock_le s a
          rw [h1] at ht
          exact ih b t (lexSmaller ht (by first | omega | (simp; omega) | simp)) r s' b' eb ⟨hev, hne, hb⟩
        · rw [if_neg hres] at hev ⊢
          exact hev
  | dec name value body =>
      rcases hbody : unreachElimHOLExact body with ⟨body', eb⟩
      rw [unreachElimHOLExact, hbody] at hu
      obtain ⟨rfl, _⟩ := Prod.mk.inj hu
      rw [evalCrepSemHOLProgExact_dec_holShape] at hev ⊢
      split at hev
      · rename_i v hv
        try rw [hv]
        try dsimp only
        rcases h1 : evalCrepSemHOLProgExact
            { s with locals := s.locals.updateEq (name, v) } body with ⟨res, st⟩
        rw [h1] at hev
        have hres : res = r := (Prod.mk.inj hev).1
        subst hres
        have := ih body { s with locals := s.locals.updateEq (name, v) }
          (lexSmaller (Nat.le_refl _) (by first | omega | (simp; omega) | simp)) res st body' eb ⟨h1, hne, hbody⟩
        rw [this]
        exact hev
      · exact absurd (Prod.mk.inj hev).1.symm hne
  | ite condition thenBranch elseBranch =>
      rcases hthen : unreachElimHOLExact thenBranch with ⟨then', et⟩
      rcases helse : unreachElimHOLExact elseBranch with ⟨else', ee⟩
      rw [unreachElimHOLExact, hthen, helse] at hu
      obtain ⟨rfl, _⟩ := Prod.mk.inj hu
      rw [evalCrepSemHOLProgExact_ite_holShape] at hev ⊢
      split at hev
      · rename_i w hw
        try rw [hw]
        try dsimp only
        by_cases hwz : w ≠ 0
        · rw [if_pos hwz] at hev ⊢
          exact ih thenBranch s (lexSmaller (Nat.le_refl _) (by first | omega | (simp; omega) | simp)) r s' then' et
            ⟨hev, hne, hthen⟩
        · rw [if_neg hwz] at hev ⊢
          exact ih elseBranch s (lexSmaller (Nat.le_refl _) (by first | omega | (simp; omega) | simp)) r s' else' ee
            ⟨hev, hne, helse⟩
      · exact absurd (Prod.mk.inj hev).1.symm hne
  | «while» condition body =>
      rcases hbody : unreachElimHOLExact body with ⟨body', eb⟩
      rw [unreachElimHOLExact, hbody] at hu
      obtain ⟨rfl, _⟩ := Prod.mk.inj hu
      have hloop := ih (.while condition body)
      rw [evalCrepSemHOLProgExact_while_holShape] at hev ⊢
      split at hev
      · rename_i w hw
        try rw [hw]
        try dsimp only
        by_cases hwz : w ≠ 0
        · rw [if_pos hwz] at hev ⊢
          by_cases hclock : s.clock = 0
          · rw [if_pos hclock] at hev ⊢
            exact hev
          · rw [if_neg hclock] at hev ⊢
            rcases h1 : evalCrepSemHOLProgExact (decClockCrepSemHOL s) body with ⟨res, t⟩
            rw [h1] at hev
            dsimp only at hev
            have hdec : (decClockCrepSemHOL s).clock < s.clock := by
              simp [decClockCrepSemHOL]; omega
            have ht : t.clock < s.clock := by
              have := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) body
              rw [h1] at this
              simp only at this
              omega
            have hresErr : res ≠ some .error := by
              intro hres
              subst hres
              exact hne (Prod.mk.inj hev).1.symm
            rw [ih body (decClockCrepSemHOL s) (lexClock hdec) res t body' eb
              ⟨h1, hresErr, hbody⟩]
            try dsimp only
            have hrec : ∀ r' s'',
                evalCrepSemHOLProgExact t (.while condition body) = (r', s'') →
                r' ≠ some .error →
                evalCrepSemHOLProgExact t (.while condition body') = (r', s'') :=
              fun r' s'' h hne' => hloop t (lexClock ht) r' s'' _ none
                ⟨h, hne', by rw [unreachElimHOLExact, hbody]⟩
            split at hev
            · exact hrec r s' hev hne
            · exact hrec r s' hev hne
            · exact hev
            · exact hev
        · rw [if_neg hwz] at hev ⊢
          exact hev
      · exact hev
  | call returnInfo function arguments =>
      rcases returnInfo with _ | ⟨names, _ | ⟨handler, hbody⟩⟩
      · simp only [unreachElimHOLExact, Prod.mk.injEq] at hu
        obtain ⟨rfl, _⟩ := hu
        exact hev
      · simp only [unreachElimHOLExact, Prod.mk.injEq] at hu
        obtain ⟨rfl, _⟩ := hu
        exact hev
      · rcases hh : unreachElimHOLExact hbody with ⟨hbody', eh⟩
        rw [unreachElimHOLExact, hh] at hu
        obtain ⟨rfl, _⟩ := Prod.mk.inj hu
        rw [evalCrepSemHOLProgExact_call_holShape] at hev ⊢
        simp only [crepReturnInfoNodupError] at hev ⊢
        repeat' split at hev
        all_goals first
          | (simp_all; done)
          | (rename_i hnodup hclock _ _ st hcallee heid
             subst heid
             rw [if_neg hnodup, if_neg hclock, if_pos rfl]
             have hle := clockLeOfEval hcallee
             simp only [decClockCrepSemHOL] at hle
             exact ih hbody _ (lexClock (by simp only; omega)) r s' hbody' eh
               ⟨hev, hne, hh⟩)
  | _ =>
      simp only [unreachElimHOLExact, Prod.mk.injEq] at hu
      obtain ⟨rfl, _⟩ := hu
      exact hev

end CrepInlineUnreachElimEvaluate

end Flapjack
