import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.While
import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Call

/-!
# crep_inline: assembled `evaluate_state_locals_rel_strong`

Assembly of HOL `evaluate_state_locals_rel_strong`
(`cakeml/pancake/proofs/crep_inlineProofScript.sml:273-564`) from its tagged
constructor cases (bead `flapjack-pxn.18.5.5.43.5.8`), and the corollary
`evaluate_state_locals_rel` (`:567-585`).  The `evaluate_ind` motive is
established for every state by structural recursion on the program (a call's
handler being a structural subterm), with an inner clock induction supplying
exactly the guarded While premises, the principle of the accepted
`evaluate_locals_same_fdom` assembly.  No public induction hypothesis remains.
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

/-- Local support: the While motive for every state, by clock induction. -/
private theorem whileStrongMotive {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (ihc : ∀ u : CrepSemHOLState width σ, strongLocalsGoal c u) :
    ∀ s : CrepSemHOLState width σ, strongLocalsGoal (.while e c) s := by
  have step : ∀ s : CrepSemHOLState width σ,
      (∀ s1 : CrepSemHOLState width σ, s1.clock < s.clock → strongLocalsGoal (.while e c) s1) →
      strongLocalsGoal (.while e c) s := by
    intro s ih
    have hlt : ∀ res s1, s.clock ≠ 0 →
        (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c → s1.clock < s.clock := by
      intro res s1 hck heq
      have hle := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) c
      rw [← heq] at hle
      simp only [decClockCrepSemHOL_clock'] at hle
      omega
    intro r s' t h he hl hr
    exact evaluateStateLocalsRelStrongWhileExact e c s
      { continueCase := fun _ _ res s1 _ _ _ _ _ hck heq _ _ _ => ih s1 (hlt res s1 hck heq)
        normalCase := fun _ _ res s1 _ _ _ hck heq _ => ih s1 (hlt res s1 hck heq)
        bodyCase := fun _ _ _ _ _ _ => ihc _ } r s' t h he hl hr
  have main : ∀ (n : Nat) (s : CrepSemHOLState width σ), s.clock ≤ n →
      strongLocalsGoal (.while e c) s := by
    intro n
    induction n with
    | zero => intro s hs; exact step s (fun s1 h1 => absurd h1 (by omega))
    | succ k ih => intro s hs; exact step s (fun s1 h1 => ih s1 (by omega))
  exact fun s => main s.clock s (Nat.le_refl _)

/-- Local support: the `evaluate_ind` motive of `evaluate_state_locals_rel_strong`
    for every program and state. -/
private theorem strongMotive {width : Nat} [NeZero width] {σ : Type} :
    ∀ (p : CrepProgHOL width) (s : CrepSemHOLState width σ), strongLocalsGoal p s
  | .skip, s => fun r s' t h he hl hr => evaluateStateLocalsRelStrongSkipExact s s' t r h he hl hr
  | .tick, s => fun r s' t h he hl hr => evaluateStateLocalsRelStrongTickExact s s' t r h he hl hr
  | .break n, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongBreakExact n s s' t r h he hl hr
  | .continue n, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongContinueExact n s s' t r h he hl hr
  | .assign n e, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongAssignExact n e s r s' t h he hl hr
  | .store a b, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongStoreExact a b s r s' t h he hl hr
  | .store32 a b, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongStore32Exact a b s r s' t h he hl hr
  | .storeByte a b, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongStoreByteExact a b s r s' t h he hl hr
  | .storeGlob a b, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongStoreGlobExact a b s r s' t h he hl hr
  | .raise e, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongRaiseExact e s r s' t h he hl hr
  | .return es, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongReturnExact es s r s' t h he hl hr
  | .primitive ns op args, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongPrimitiveExact ns op args s r s' t h he hl hr
  | .extCall f a b c d, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongExtCallExact f a b c d s r s' t h he hl hr
  | .shMem op n a, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongShMemExact op n a s r s' t h he hl hr
  | .dec v e body, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongDecExact v e body s (fun _ _ => strongMotive body _)
        r s' t h he hl hr
  | .seq a b, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongSeqExact a b s (fun _ s1 _ _ => strongMotive b s1)
        (strongMotive a s) r s' t h he hl hr
  | .ite c a b, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongIfExact c a b s (fun _ w _ _ => by
        by_cases hw : w ≠ 0
        · rw [if_pos hw]; exact strongMotive a s
        · rw [if_neg hw]; exact strongMotive b s) r s' t h he hl hr
  | .while e c, s => whileStrongMotive e c (fun u => strongMotive c u) s
  | .call none f args, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongCallExact none f args s
        (fun _ _ _ _ _ _ _ _ _ _ _ _ hinfo => by cases hinfo) r s' t h he hl hr
  | .call (some (names, none)) f args, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongCallExact _ f args s
        (fun _ _ _ _ _ _ _ _ _ _ _ _ hinfo => by simp at hinfo) r s' t h he hl hr
  | .call (some (names, some (eid, handler))) f args, s => fun r s' t h he hl hr =>
      evaluateStateLocalsRelStrongCallExact _ f args s
        (fun _ _ _ _ _ handler' st _ _ _ _ _ hinfo => by
          simp only [Option.some.injEq, Prod.mk.injEq] at hinfo
          obtain ⟨_, _, rfl⟩ := hinfo
          exact strongMotive handler _) r s' t h he hl hr
termination_by p => sizeOf p

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
