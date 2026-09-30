import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.Atoms
import Flapjack.Pancake.Proofs.CrepInline.ExpressionRelations
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Assembly

/-!
# crep_inline `evaluate_state_locals_rel_strong`: Dec, Seq and If cases

Counterpart of `cakeml/pancake/proofs/crep_inlineProofScript.sml:328-397`
(bead `flapjack-pxn.18.5.5.43.5.4`).  The motive `strongLocalsGoal` is HOL's
`evaluate_ind` motive for `evaluate_state_locals_rel_strong` at `(p, s)`; each
tagged case states HOL's goal for its constructor (curried as in the accepted
leaf cases) and takes exactly the guarded `evaluate_ind` premises of that
constructor at this motive.
-/

namespace Flapjack.CrepInlineExact

namespace StrongStructuralSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end StrongStructuralSupport

/-- HOL's result-indexed conclusion of `evaluate_state_locals_rel_strong`.
    Untagged: part of the theorem statement. -/
def strongLocalsPost {width : Nat} [NeZero width] {σ : Type}
    (r : Option (CrepResultHOLExact width)) (s s' t t' : CrepSemHOLState width σ) : Prop :=
  match (generalizing := false) r with
  | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
  | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
  | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
  | some .error => False
  | _ => True

/-- The `evaluate_ind` motive of HOL `evaluate_state_locals_rel_strong` at
    `(p, s)`.  Untagged Flapjack spelling of the motive. -/
def strongLocalsGoal {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ) : Prop :=
  ∀ (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ),
    evalCrepSemHOLProgExact s p = (r, s') → r ≠ some .error →
    crepInlineLocalsRelExact s t → crepInlineStateRelExact s t →
    ∃ t', evalCrepSemHOLProgExact t p = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      strongLocalsPost r s s' t t'

/-- Local support: `locals_rel` is preserved by updating both maps at the
    same key with the same value. -/
private theorem localsRel_updateEq {width : Nat} [NeZero width] {σ : Type}
    {s t : CrepSemHOLState width σ} (h : crepInlineLocalsRelExact s t) (v : Nat)
    (w : HolWordLab width) :
    crepInlineLocalsRelExact { s with locals := s.locals.updateEq (v, w) }
      { t with locals := t.locals.updateEq (v, w) } := by
  intro k x hk
  simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hk ⊢
  by_cases hkv : k = v
  · simp_all
  · simp only [hkv, if_false] at hk ⊢; exact h k x hk

/-- Local support: the `locals_ext_rel` step of the `Dec` case, pointwise. -/
private theorem decExtRel {width : Nat} [NeZero width] {σ : Type}
    (v : Nat) (val : HolWordLab width) (s t st t2 : CrepSemHOLState width σ)
    (hdom : crepHolFdom (s.locals.updateEq (v, val)).lookup = crepHolFdom st.locals.lookup)
    (hx2 : crepHolFdiff t2.locals.lookup (crepHolFdom st.locals.lookup) =
      crepHolFdiff (t.locals.updateEq (v, val)).lookup
        (crepHolFdom (s.locals.updateEq (v, val)).lookup) ∨
      crepHolFdiff (t.locals.updateEq (v, val)).lookup
        (crepHolFdom (s.locals.updateEq (v, val)).lookup) =
      crepHolFdiff t2.locals.lookup (crepHolFdom st.locals.lookup)) :
    crepHolFdiff t.locals.lookup (crepHolFdom s.locals.lookup) =
      crepHolFdiff (t2.locals.resVarEq (v, t.locals.lookup v)).lookup
        (crepHolFdom (st.locals.resVarEq (v, s.locals.lookup v)).lookup) := by
  have hx : crepHolFdiff (t.locals.updateEq (v, val)).lookup
      (crepHolFdom (s.locals.updateEq (v, val)).lookup) =
      crepHolFdiff t2.locals.lookup (crepHolFdom st.locals.lookup) := by
    rcases hx2 with h | h
    · exact h.symm
    · exact h
  have hres : ∀ (m : HolFiniteMapExact Nat (HolWordLab width)) (o : Option (HolWordLab width))
      (k : Nat), (m.resVarEq (v, o)).lookup k = if k = v then o else m.lookup k := by
    intro m o k
    cases o <;> simp [HolFiniteMapExact.lookup_resVarEq_none,
      HolFiniteMapExact.lookup_resVarEq_some, FDOMSUB_HOL, FUPDATE_HOL]
  funext k
  have hdk := congrFun hdom k
  have hxk := congrFun hx k
  simp only [crepHolFdiff, crepHolFdom, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hdk hxk ⊢
  simp only [hres]
  by_cases hkv : k = v
  · subst hkv
    simp only [if_true]
    rfl
  · simp only [hkv, if_false] at hdk hxk ⊢
    exact hxk

/-- Local support: the `Dec` case of the motive from its guarded premise. -/
private theorem decStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (v : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ value, crepExactEvalExpClassical s e = some value →
      strongLocalsGoal body (CrepSemHOLState.setVar v value s)) :
    strongLocalsGoal (.dec v e body) s := by
  intro r s' t hev hne hloc hrel
  rw [evalCrepSemHOLProgExact_dec_holShape] at hev
  cases hval : evalCrepSemHOLExp s e with
  | none => rw [hval] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some val =>
      rw [hval] at hev
      dsimp only at hev
      rcases hbody : evalCrepSemHOLProgExact
          { s with locals := s.locals.updateEq (v, val) } body with ⟨r0, st⟩
      rw [hbody] at hev
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      have htval : evalCrepSemHOLExp t e = some val :=
        evalStateLocalsRelExact s e val t ⟨hval, hrel, hloc⟩
      have hcl : crepExactEvalExpClassical s e = some val := by
        simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hval
      have hrelu : crepInlineStateRelExact { s with locals := s.locals.updateEq (v, val) }
          { t with locals := t.locals.updateEq (v, val) } := by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      obtain ⟨t2, hevt, hrel2, hpost2⟩ :=
        ih val hcl r0 st { t with locals := t.locals.updateEq (v, val) } hbody hne
          (localsRel_updateEq hloc v val) hrelu
      refine ⟨{ t2 with locals := t2.locals.resVarEq (v, t.locals.lookup v) }, ?_, ?_, ?_⟩
      · rw [evalCrepSemHOLProgExact_dec_holShape, htval]
        dsimp only
        rw [hevt]
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel2
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      · -- locals facts for the three continuing results
        have key : strongLocalsPost r0 { s with locals := s.locals.updateEq (v, val) } st
            { t with locals := t.locals.updateEq (v, val) } t2 →
            (r0 = none ∨ (∃ n, r0 = some (.break n)) ∨ (∃ n, r0 = some (.continue n))) →
            crepInlineLocalsRelExact
                { st with locals := st.locals.resVarEq (v, s.locals.lookup v) }
                { t2 with locals := t2.locals.resVarEq (v, t.locals.lookup v) } ∧
              crepInlineLocalsExtRelExact s
                { st with locals := st.locals.resVarEq (v, s.locals.lookup v) } t
                { t2 with locals := t2.locals.resVarEq (v, t.locals.lookup v) } := by
          intro hp hr
          have hpl : crepInlineLocalsRelExact st t2 ∧
              crepInlineLocalsExtRelExact { s with locals := s.locals.updateEq (v, val) } st
                { t with locals := t.locals.updateEq (v, val) } t2 := by
            rcases hr with rfl | ⟨n, rfl⟩ | ⟨n, rfl⟩ <;> exact hp
          obtain ⟨hl2, hx2⟩ := hpl
          have hdom := evaluateLocalsSameFdom'Exact body
            { s with locals := s.locals.updateEq (v, val) } r0 st ⟨hbody, hr⟩
          constructor
          · intro k x hk
            cases hsv : s.locals.lookup v with
            | some y =>
                have hty : t.locals.lookup v = some y := hloc v y hsv
                rw [hsv, HolFiniteMapExact.lookup_resVarEq_some] at hk
                rw [hty, HolFiniteMapExact.lookup_resVarEq_some]
                simp only [FUPDATE_HOL] at hk ⊢
                by_cases hkv : k = v
                · simp_all
                · simp only [hkv, if_false] at hk ⊢; exact hl2 k x hk
            | none =>
                rw [hsv, HolFiniteMapExact.lookup_resVarEq_none] at hk
                simp only [FDOMSUB_HOL] at hk
                by_cases hkv : k = v
                · simp [hkv] at hk
                · simp only [hkv, if_false] at hk
                  cases htv : t.locals.lookup v with
                  | none =>
                      rw [HolFiniteMapExact.lookup_resVarEq_none]
                      simp only [FDOMSUB_HOL, hkv, if_false]; exact hl2 k x hk
                  | some y =>
                      rw [HolFiniteMapExact.lookup_resVarEq_some]
                      simp only [FUPDATE_HOL, hkv, if_false]; exact hl2 k x hk
          · unfold crepInlineLocalsExtRelExact at hx2 ⊢
            exact decExtRel v val s t st t2 hdom (Or.inr hx2)
        unfold strongLocalsPost at hpost2 ⊢
        rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
        · exact key hpost2 (Or.inl rfl)
        · exact hpost2
        · exact trivial
        · exact key hpost2 (Or.inr (Or.inl ⟨n, rfl⟩))
        · exact key hpost2 (Or.inr (Or.inr ⟨n, rfl⟩))
        · exact trivial
        · exact trivial
        · exact trivial

/-- Local support: the `Seq` case of the motive from its guarded premises. -/
private theorem seqStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih2 : ∀ res s1, (res, s1) = evalCrepSemHOLProgExact s c1 → res = none →
      strongLocalsGoal c2 s1)
    (ih1 : strongLocalsGoal c1 s) :
    strongLocalsGoal (.seq c1 c2) s := by
  intro r s' t hev hne hloc hrel
  rw [evalCrepSemHOLProgExact_seq_fixClockFree] at hev
  rw [evalCrepSemHOLProgExact_seq_fixClockFree]
  rcases hstep : evalCrepSemHOLProgExact s c1 with ⟨r0, s1⟩
  rw [hstep] at hev
  cases r0 with
  | none =>
      obtain ⟨t1, hev1, hrel1, hpost1⟩ := ih1 none s1 t hstep (by simp) hloc hrel
      obtain ⟨hl1, hx1⟩ := hpost1
      rw [hev1]
      obtain ⟨t', hev2, hrel2, hpost2⟩ := ih2 none s1 hstep.symm rfl r s' t1 hev hne hl1 hrel1
      refine ⟨t', hev2, hrel2, ?_⟩
      unfold strongLocalsPost at hpost2 ⊢
      rcases r with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
      · exact ⟨hpost2.1, hx1.trans hpost2.2⟩
      · exact hpost2
      · exact trivial
      · exact ⟨hpost2.1, hx1.trans hpost2.2⟩
      · exact ⟨hpost2.1, hx1.trans hpost2.2⟩
      · exact trivial
      · exact trivial
      · exact trivial
  | some x =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      obtain ⟨t1, hev1, hrel1, hpost1⟩ := ih1 (some x) s1 t hstep hne hloc hrel
      rw [hev1]
      exact ⟨t1, rfl, hrel1, hpost1⟩

/-- Local support: the `If` case of the motive from its guarded premise. -/
private theorem iteStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (c : CrepExpHOL width) (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ v1 w, crepExactEvalExpClassical s c = some v1 → v1 = .word w →
      strongLocalsGoal (if w ≠ 0 then c1 else c2) s) :
    strongLocalsGoal (.ite c c1 c2) s := by
  intro r s' t hev hne hloc hrel
  rw [evalCrepSemHOLProgExact_ite] at hev
  rw [evalCrepSemHOLProgExact_ite]
  simp only [crepExactEvalExp_eq_eval] at hev ⊢
  cases hcond : evalCrepSemHOLExp s c with
  | none => rw [hcond] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some cv =>
      cases cv with
      | word w =>
          rw [hcond] at hev
          have htc := evalStateLocalsRelExact s c (.word w) t ⟨hcond, hrel, hloc⟩
          rw [htc]
          have hcl : crepExactEvalExpClassical s c = some (.word w) := by
            simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hcond
          have hsel := ih (.word w) w hcl rfl
          dsimp only at hev ⊢
          by_cases hw : w ≠ 0
          · rw [if_pos hw] at hev hsel ⊢
            exact hsel r s' t hev hne hloc hrel
          · rw [if_neg hw] at hev hsel ⊢
            exact hsel r s' t hev hne hloc hrel

/-- `Dec` case of HOL `evaluate_state_locals_rel_strong` (`:328-380`), with
    HOL `evaluate_ind`'s guarded body premise. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongDecExact {width : Nat} [NeZero width] {σ : Type}
    (v : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ value, crepExactEvalExpClassical s e = some value →
      strongLocalsGoal body (CrepSemHOLState.setVar v value s))
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.dec v e body) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.dec v e body) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  decStrongGoal v e body s ih r s' t heval herror hlocals hstate

/-- `Seq` case (`:381-390`), with HOL `evaluate_ind`'s two Seq premises. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongSeqExact {width : Nat} [NeZero width] {σ : Type}
    (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih2 : ∀ res s1, (res, s1) = evalCrepSemHOLProgExact s c1 → res = none →
      strongLocalsGoal c2 s1)
    (ih1 : strongLocalsGoal c1 s)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.seq c1 c2) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.seq c1 c2) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  seqStrongGoal c1 c2 s ih2 ih1 r s' t heval herror hlocals hstate

/-- `If` case (`:391-397`), with HOL `evaluate_ind`'s guarded selected-branch
    premise. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongIfExact {width : Nat} [NeZero width] {σ : Type}
    (c : CrepExpHOL width) (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ v1 w, crepExactEvalExpClassical s c = some v1 → v1 = .word w →
      strongLocalsGoal (if w ≠ 0 then c1 else c2) s)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.ite c c1 c2) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.ite c c1 c2) = (r, t') ∧ crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  iteStrongGoal c c1 c2 s ih r s' t heval herror hlocals hstate

end Flapjack.CrepInlineExact
