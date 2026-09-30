import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.While
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Call

/-!
# crep_inline: assembled `evaluate_state_locals_rel_strong`

Assembly of HOL `evaluate_state_locals_rel_strong`
(`cakeml/pancake/proofs/crep_inlineProofScript.sml:273-564`) from its tagged
constructor cases (bead `flapjack-pxn.18.5.5.43.5.8`), and the corollary
`evaluate_state_locals_rel` (`:567-585`).  The `evaluate_ind` motive is
established for every program and state by the lexicographic (clock, size)
induction `evalCrepSemHOLProgExact_inductLex`, which supplies every tagged
case's literal `evaluate_ind` premises (including the Call callee premise at
the decremented clock).  No public induction hypothesis remains.
-/

namespace Flapjack.CrepInlineExact

namespace StrongAssemblySupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end StrongAssemblySupport

/-- Local support: the `evaluate_ind` motive of `evaluate_state_locals_rel_strong`
    for every program and state, by the lexicographic (clock, size)
    induction `evalCrepSemHOLProgExact_inductLex`.  Each tagged case is applied
    with exactly its `evaluate_ind` premises; every premise's program/state pair
    is lexicographically smaller. -/
private theorem strongMotive {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), strongLocalsGoal p s := by
  refine evalCrepSemHOLProgExact_inductLex (motive := strongLocalsGoal) ?_
  intro p s ih
  have lower : ∀ (p' : CrepProgHOL width) (s' : CrepSemHOLState width σ),
      s'.clock < s.clock → strongLocalsGoal p' s' :=
    fun p' s' hc => ih p' s' (Prod.Lex.left _ _ hc)
  have same : ∀ (p' : CrepProgHOL width) (s' : CrepSemHOLState width σ),
      s'.clock = s.clock → sizeOf p' < sizeOf p → strongLocalsGoal p' s' :=
    fun p' s' hc hs => ih p' s' (by rw [hc]; exact Prod.Lex.right _ hs)
  have dec_lt : s.clock ≠ 0 → (decClockCrepSemHOL s).clock < s.clock := by
    intro h; simp only [decClockCrepSemHOL_clock']; omega
  cases p with
  | skip => exact fun r s' t h he hl hr => evaluateStateLocalsRelStrongSkipExact s s' t r h he hl hr
  | tick => exact fun r s' t h he hl hr => evaluateStateLocalsRelStrongTickExact s s' t r h he hl hr
  | «break» n => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongBreakExact n s s' t r h he hl hr
  | «continue» n => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongContinueExact n s s' t r h he hl hr
  | assign n e => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongAssignExact n e s r s' t h he hl hr
  | store a b => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongStoreExact a b s r s' t h he hl hr
  | store32 a b => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongStore32Exact a b s r s' t h he hl hr
  | storeByte a b => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongStoreByteExact a b s r s' t h he hl hr
  | storeGlob a b => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongStoreGlobExact a b s r s' t h he hl hr
  | raise e => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongRaiseExact e s r s' t h he hl hr
  | «return» es => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongReturnExact es s r s' t h he hl hr
  | primitive ns op args => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongPrimitiveExact ns op args s r s' t h he hl hr
  | extCall f a b c d => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongExtCallExact f a b c d s r s' t h he hl hr
  | shMem op n a => exact fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongShMemExact op n a s r s' t h he hl hr
  | dec v e body =>
      have hsz : sizeOf body < sizeOf (CrepProgHOL.dec v e body) := by
        simp only [CrepProgHOL.dec.sizeOf_spec]; omega
      exact fun r s' t h he hl hr =>
        evaluateStateLocalsRelStrongDecExact v e body s (fun _ _ => same _ _ rfl hsz)
          r s' t h he hl hr
  | seq a b =>
      refine fun r s' t h he hl hr => evaluateStateLocalsRelStrongSeqExact a b s
        (fun res s1 hs1 _ => ?_) (same _ _ rfl (by simp only [CrepProgHOL.seq.sizeOf_spec]; omega))
        r s' t h he hl hr
      have hle := evalCrepSemHOLProgExact_clock_le s a
      rw [← hs1] at hle
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact lower _ _ hlt
      · exact same _ _ heq (by simp only [CrepProgHOL.seq.sizeOf_spec]; omega)
  | ite c a b =>
      refine fun r s' t h he hl hr => evaluateStateLocalsRelStrongIfExact c a b s
        (fun _ w _ _ => ?_) r s' t h he hl hr
      by_cases hw : w ≠ 0
      · rw [if_pos hw]; exact same _ _ rfl (by simp only [CrepProgHOL.ite.sizeOf_spec]; omega)
      · rw [if_neg hw]; exact same _ _ rfl (by simp only [CrepProgHOL.ite.sizeOf_spec]; omega)
  | «while» e c =>
      have hlt : ∀ res s1, s.clock ≠ 0 →
          (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c → s1.clock < s.clock := by
        intro res s1 hck heq
        have hle := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) c
        rw [← heq] at hle
        exact Nat.lt_of_le_of_lt hle (dec_lt hck)
      exact fun r s' t h he hl hr => evaluateStateLocalsRelStrongWhileExact e c s
        { continueCase := fun _ _ res s1 _ _ _ _ _ hck heq _ _ _ =>
            lower _ s1 (hlt res s1 hck heq)
          normalCase := fun _ _ res s1 _ _ _ hck heq _ => lower _ s1 (hlt res s1 hck heq)
          bodyCase := fun _ _ _ _ _ hck => lower _ _ (dec_lt hck) } r s' t h he hl hr
  | call info f args =>
      exact fun r s' t h he hl hr => evaluateStateLocalsRelStrongCallExact info f args s
        (fun _ _ newlocals _ _ _ hck => lower _ { decClockCrepSemHOL s with locals := newlocals }
          (dec_lt hck))
        (fun _ prog newlocals _ _ _ st _ _ _ hck hb _ => by
          have hle := evalCrepSemHOLProgExact_clock_le
            { decClockCrepSemHOL s with locals := newlocals } prog
          rw [hb] at hle
          exact lower _ { st with locals := s.locals } (Nat.lt_of_le_of_lt hle (dec_lt hck)))
        r s' t h he hl hr

/-- Exact HOL `evaluate_state_locals_rel_strong` (`crep_inlineProofScript.sml:273-564`),
    assembled from the tagged constructor cases with every `evaluate_ind`
    premise discharged internally. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongExact {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact s p = (r, s') ∧ r ≠ some .error ∧
        crepInlineLocalsRelExact s t ∧ crepInlineStateRelExact s t →
      ∃ t', evalCrepSemHOLProgExact t p = (r, t') ∧ crepInlineStateRelExact s' t' ∧
        (match (generalizing := false) r with
         | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
         | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
         | some (.continue _) =>
             crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
         | some .error => False
         | _ => True) :=
  fun p s r s' t ⟨h, he, hl, hr⟩ => strongMotive p s r s' t h he hl hr

/-- Exact HOL `evaluate_state_locals_rel` (`crep_inlineProofScript.sml:567-585`),
    curried as in HOL; the weaker conclusion drops `locals_ext_rel`. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelExact {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
      (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact s p = (r, s') →
      r ≠ some .error →
      crepInlineLocalsRelExact s t ∧ crepInlineStateRelExact s t →
      ∃ t', evalCrepSemHOLProgExact t p = (r, t') ∧ crepInlineStateRelExact s' t' ∧
        (match (generalizing := false) r with
         | none => crepInlineLocalsRelExact s' t'
         | some (.break _) => crepInlineLocalsRelExact s' t'
         | some (.continue _) => crepInlineLocalsRelExact s' t'
         | some .error => False
         | _ => True) := by
  intro p s r s' t h he ⟨hl, hr⟩
  obtain ⟨t', ht, hrel, hpost⟩ := evaluateStateLocalsRelStrongExact p s r s' t ⟨h, he, hl, hr⟩
  refine ⟨t', ht, hrel, ?_⟩
  rcases r with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
  · exact hpost.1
  · exact hpost
  · exact trivial
  · exact hpost.1
  · exact hpost.1
  · exact trivial
  · exact trivial
  · exact trivial

end Flapjack.CrepInlineExact
