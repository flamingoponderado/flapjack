import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Structural

/-!
# crep_inline `evaluate_state_locals_rel_strong`: the `While` case

Counterpart of `cakeml/pancake/proofs/crep_inlineProofScript.sml:289-327`
(bead `flapjack-pxn.18.5.5.43.5.6`).  The induction hypotheses are exactly the
three guarded `evaluate_ind` While premises at the motive `strongLocalsGoal`,
bundled as for the accepted `WhileDomainIH`.
-/

namespace Flapjack.CrepInlineExact

namespace StrongWhileSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end StrongWhileSupport

/-- The three guarded recursion premises of HOL `evaluate_ind`'s While case,
specialized to `strongLocalsGoal`.  Infrastructure; not a HOL theorem port. -/
structure StrongLocalsWhileIH {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (s : CrepSemHOLState width σ) : Prop where
  continueCase : ∀ v2 w res s1 v1 v8,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
    res = some v1 → v1 = .continue v8 → v8 = 0 → strongLocalsGoal (.while e c) s1
  normalCase : ∀ v2 w res s1,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
    res = none → strongLocalsGoal (.while e c) s1
  bodyCase : ∀ v2 w,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    strongLocalsGoal c (decClockCrepSemHOL s)

/-- Local support: the `While` case of the motive. -/
theorem whileStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : StrongLocalsWhileIH e c s) :
    strongLocalsGoal (.while e c) s := by
  intro r s' t hev hne hloc hrel
  have hclock : s.clock = t.clock := hrel.2.2.2.2.2.1
  rw [evalCrepSemHOLProgExact_while_holShape] at hev ⊢
  cases hcond : evalCrepSemHOLExp s e with
  | none => rw [hcond] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some cv =>
      rw [hcond] at hev
      rw [evalStateLocalsRelExact s e cv t ⟨hcond, hrel, hloc⟩]
      rcases cv with ⟨w⟩
      dsimp only at hev ⊢
      have hclass : crepExactEvalExpClassical s e = some (.word w) := by
        simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hcond
      by_cases hw : w ≠ 0
      · rw [if_pos hw] at hev ⊢
        by_cases hc : s.clock = 0
        · rw [if_pos hc] at hev
          rw [if_pos (hclock ▸ hc)]
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel
          exact ⟨_, rfl, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, trivial⟩
        · rw [if_neg hc] at hev
          rw [if_neg (hclock ▸ hc)]
          rcases hb : evalCrepSemHOLProgExact (decClockCrepSemHOL s) c with ⟨r0, s1⟩
          rw [hb] at hev
          dsimp only at hev
          have hne0 : r0 ≠ some .error := by
            rintro rfl
            simp only [exitLoopCrepResult] at hev
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            exact hne rfl
          obtain ⟨hlocd, hreld⟩ := crepInlineLocalsRel_decClockExact s t ⟨hloc, hrel⟩
          obtain ⟨t1, hevt1, hrel1, hpost1⟩ :=
            ih.bodyCase (.word w) w hclass rfl hw hc r0 s1 (decClockCrepSemHOL t) hb hne0 hlocd hreld
          rw [hevt1]
          dsimp only
          -- the body's `locals_ext_rel` from the undecremented states
          have hext : ∀ (h : crepInlineLocalsExtRelExact (decClockCrepSemHOL s) s1
              (decClockCrepSemHOL t) t1), crepInlineLocalsExtRelExact s s1 t t1 := fun h => h
          unfold strongLocalsPost at hpost1
          rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
          · obtain ⟨hl1, hx1⟩ := hpost1
            obtain ⟨t', hev', hrel', hpost'⟩ :=
              ih.normalCase (.word w) w none s1 hclass rfl hw hc hb.symm rfl r s' t1 hev hne hl1 hrel1
            refine ⟨t', hev', hrel', ?_⟩
            unfold strongLocalsPost at hpost' ⊢
            rcases r with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
            · exact ⟨hpost'.1, (hext hx1).trans hpost'.2⟩
            · exact hpost'
            · exact trivial
            · exact ⟨hpost'.1, (hext hx1).trans hpost'.2⟩
            · exact ⟨hpost'.1, (hext hx1).trans hpost'.2⟩
            · exact trivial
            · exact trivial
            · exact trivial
          · exact absurd rfl hne0
          · simp only [exitLoopCrepResult] at hev ⊢
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            exact ⟨_, rfl, hrel1, trivial⟩
          · obtain ⟨hl1, hx1⟩ := hpost1
            cases n with
            | zero =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                exact ⟨_, rfl, hrel1, hl1, hext hx1⟩
            | succ n =>
                simp only [exitLoopCrepResult] at hev ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                exact ⟨_, rfl, hrel1, hl1, hext hx1⟩
          · obtain ⟨hl1, hx1⟩ := hpost1
            cases n with
            | zero =>
                obtain ⟨t', hev', hrel', hpost'⟩ :=
                  ih.continueCase (.word w) w _ s1 _ 0 hclass rfl hw hc hb.symm rfl rfl rfl
                    r s' t1 hev hne hl1 hrel1
                refine ⟨t', hev', hrel', ?_⟩
                unfold strongLocalsPost at hpost' ⊢
                rcases r with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
                · exact ⟨hpost'.1, (hext hx1).trans hpost'.2⟩
                · exact hpost'
                · exact trivial
                · exact ⟨hpost'.1, (hext hx1).trans hpost'.2⟩
                · exact ⟨hpost'.1, (hext hx1).trans hpost'.2⟩
                · exact trivial
                · exact trivial
                · exact trivial
            | succ n =>
                simp only [exitLoopCrepResult] at hev ⊢
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                exact ⟨_, rfl, hrel1, hl1, hext hx1⟩
          · simp only [exitLoopCrepResult] at hev ⊢
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            exact ⟨_, rfl, hrel1, trivial⟩
          · simp only [exitLoopCrepResult] at hev ⊢
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            exact ⟨_, rfl, hrel1, trivial⟩
          · simp only [exitLoopCrepResult] at hev ⊢
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            exact ⟨_, rfl, hrel1, trivial⟩
      · rw [if_neg hw] at hev ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
        exact ⟨_, rfl, hrel, hloc, rfl⟩

/-- `While` case of HOL `evaluate_state_locals_rel_strong` (`:289-327`), with
    exactly the guarded `evaluate_ind` While premises. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongWhileExact {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : StrongLocalsWhileIH e c s)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.while e c) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.while e c) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  whileStrongGoal e c s ih r s' t heval herror hlocals hstate

end Flapjack.CrepInlineExact
