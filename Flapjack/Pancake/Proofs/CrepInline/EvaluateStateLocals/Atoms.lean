import Flapjack.Pancake.Proofs.CrepInline

namespace Flapjack.CrepInlineExact

namespace StrongAtomsSupport
/-- Flapjack-specific canonical state roundtrip re-export. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end StrongAtomsSupport

/-- Skip case of HOL evaluate_state_locals_rel_strong. Original evaluation,
non-Error, locals and state relation premises; target evaluation is proved. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongSkipExact {width : Nat} [NeZero width] {σ : Type}
    (s s' t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (heval : evalCrepSemHOLProgExact s .skip = (r,s'))
    (_herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t .skip = (r,t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) := by
  rw [evalCrepSemHOLProgExact_skip] at heval
  obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
  simp only at hr ht
  subst r
  subst s'
  exact ⟨t, evalCrepSemHOLProgExact_skip t, hstate, hlocals, rfl⟩

/-- Break case of HOL evaluate_state_locals_rel_strong. Original evaluation,
non-Error, locals and state relation premises; target evaluation is proved. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongBreakExact {width : Nat} [NeZero width] {σ : Type}
    (label : Nat) (s s' t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (heval : evalCrepSemHOLProgExact s (.break label) = (r,s'))
    (_herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.break label) = (r,t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) := by
  rw [evalCrepSemHOLProgExact_break] at heval
  obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
  simp only at hr ht
  subst r
  subst s'
  exact ⟨t, evalCrepSemHOLProgExact_break t label, hstate, hlocals, rfl⟩


/-- Continue case of HOL evaluate_state_locals_rel_strong. Original evaluation,
non-Error, locals and state relation premises; target evaluation is proved. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongContinueExact {width : Nat} [NeZero width] {σ : Type}
    (label : Nat) (s s' t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (heval : evalCrepSemHOLProgExact s (.continue label) = (r,s'))
    (_herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.continue label) = (r,t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) := by
  rw [evalCrepSemHOLProgExact_continue] at heval
  obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
  simp only at hr ht
  subst r
  subst s'
  exact ⟨t, evalCrepSemHOLProgExact_continue t label, hstate, hlocals, rfl⟩


/-- Tick case of HOL evaluate_state_locals_rel_strong. Original evaluation,
non-Error, locals and state relation premises; target evaluation is proved. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongTickExact {width : Nat} [NeZero width] {σ : Type}
    (s s' t : CrepSemHOLState width σ) (r : Option (CrepResultHOLExact width))
    (heval : evalCrepSemHOLProgExact s .tick = (r,s'))
    (_herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t .tick = (r,t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) := by
  have hclock : s.clock = t.clock := hstate.2.2.2.2.2.1
  rw [evalCrepSemHOLProgExact_tick] at heval
  by_cases hc : s.clock = 0
  · rw [if_pos hc] at heval
    obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
    simp only at hr ht
    subst r
    subst s'
    refine ⟨t.emptyLocals, ?_, ?_, True.intro⟩
    · rw [evalCrepSemHOLProgExact_tick, if_pos (hclock ▸ hc)]
    · simpa only [crepInlineStateRelExact, CrepSemHOLState.emptyLocals] using hstate
  · rw [if_neg hc] at heval
    obtain ⟨hr,ht⟩ := Prod.ext_iff.mp heval
    simp only at hr ht
    subst r
    subst s'
    refine ⟨decClockCrepSemHOL t, ?_, ?_, ?_, rfl⟩
    · rw [evalCrepSemHOLProgExact_tick, if_neg (hclock ▸ hc)]
    · simpa only [crepInlineStateRelExact, decClockCrepSemHOL] using
        (show crepInlineStateRelExact (decClockCrepSemHOL s) (decClockCrepSemHOL t) from
          crepInlineLocalsRel_decClockExact s t ⟨hlocals,hstate⟩ |>.2)
    · exact hlocals

end Flapjack.CrepInlineExact
