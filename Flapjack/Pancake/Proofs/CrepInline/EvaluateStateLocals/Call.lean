import Flapjack.Pancake.Proofs.CrepInline.EvaluateStateLocals.MoreAtoms

/-!
# crep_inline `evaluate_state_locals_rel_strong`: the `Call` case

`Resume evaluate_state_locals_rel_strong[Call]`
(`cakeml/pancake/proofs/crep_inlineProofScript.sml:511-562`, bead
`flapjack-pxn.18.5.5.43.5.7`).  The only induction
hypothesis is HOL `evaluate_ind`'s guarded Call handler premise (handler at
`st with locals := s.locals`) at the motive `strongLocalsGoal`, spelled with the
same evaluator guards as the accepted `evaluate_locals_same_fdom` Call case.
SPECIALISED, STRONGER case: HOL's proof also uses the callee premise
`P (prog, dec_clock s with locals := newlocals)`, but here `state_rel s t`
makes the callee's start state `dec_clock t with locals := newlocals` equal to
the source one, so both callee runs coincide and that premise is not needed.
-/

namespace Flapjack.CrepInlineExact

namespace StrongCallSupport
/-- Canonical carrier roundtrip re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
      (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
      CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end StrongCallSupport

/-- HOL `evaluate_ind`'s guarded Call handler premise at `strongLocalsGoal`. -/
def StrongLocalsCallHandlerIH {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width)) : Prop :=
  ∀ values prog newlocals rts eid handler st,
    args.mapM (evalCrepSemHOLExp s) = some values →
    lookupCodeFiniteHOL s.code fname values values.length = some (prog, newlocals) →
    ¬ crepReturnInfoNodupError info → s.clock ≠ 0 →
    evalCrepSemHOLProgExact { decClockCrepSemHOL s with locals := newlocals } prog =
      (some (.exception eid), st) →
    info = some (rts, some (eid, handler)) →
    strongLocalsGoal handler { st with locals := s.locals }

/-- Local support: the Call return write-back keeps `locals_rel` and
    `locals_ext_rel` when the destinations are existing locals. -/
private theorem callReturnPost {width : Nat} [NeZero width] {σ : Type}
    (s t st t2 : CrepSemHOLState width σ) (rts : List Nat) (retvs vals : List (HolWordLab width))
    (hm : rts.mapM s.locals.lookup = some vals) (hloc : crepInlineLocalsRelExact s t) :
    crepInlineLocalsRelExact { st with locals := s.locals.updateListEq (rts.zip retvs) }
        { t2 with locals := t.locals.updateListEq (rts.zip retvs) } ∧
      crepInlineLocalsExtRelExact s { st with locals := s.locals.updateListEq (rts.zip retvs) } t
        { t2 with locals := t.locals.updateListEq (rts.zip retvs) } := by
  have hkeys : ∀ e ∈ rts.zip retvs, (s.locals.lookup e.1).isSome = true := fun e he =>
    lookupMapMSomeIsSome s.locals.lookup rts vals hm e.1 (List.of_mem_zip he).1
  refine ⟨fun k v hk => submap_updateList _ _ _ hloc k v hk, ?_⟩
  unfold crepInlineLocalsExtRelExact
  funext j
  simp only [crepHolFdiff, crepHolFdom, HolFiniteMapExact.lookup_updateListEq]
  simp only [dom_updateList _ _ hkeys j]
  by_cases hj : (s.locals.lookup j).isSome = true
  · simp [hj]
  · have hjn : j ∉ (rts.zip retvs).map Prod.fst := by
      intro hm'
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm'
      exact hj (hkeys e he)
    simp only [hj, Bool.false_eq_true, if_false]
    exact (FLOOKUP_FUPDATE_LIST_HOL_not_mem _ _ j hjn).symm

/-- Local support: the `Call` case of the motive. -/
theorem callStrongGoal {width : Nat} [NeZero width] {σ : Type}
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ) (ih : StrongLocalsCallHandlerIH s info fname args) :
    strongLocalsGoal (.call info fname args) s := by
  intro r s' t hev hne hloc hrel
  obtain ⟨tl, rfl⟩ := target_eq hrel
  rw [evalCrepSemHOLProgExact_call_holShape] at hev ⊢
  cases hargs : args.mapM (evalCrepSemHOLExp s) with
  | none => simp only [hargs] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some vals =>
      rw [evalOptmmapStateLocalsRelExact s args vals _ ⟨hargs, hrel, hloc⟩]
      simp only [hargs] at hev
      dsimp only at hev ⊢
      cases hcode : lookupCodeFiniteHOL s.code fname vals vals.length with
      | none => simp only [hcode] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
      | some pn =>
          obtain ⟨prog, newlocals⟩ := pn
          simp only [hcode] at hev ⊢
          by_cases hn : crepReturnInfoNodupError info
          · simp only [hn, if_true] at hev
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
          · simp only [hn, if_false] at hev ⊢
            by_cases hc : s.clock = 0
            · rw [if_pos hc] at hev ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩
            · rw [if_neg hc] at hev ⊢
              have hsame : ({ decClockCrepSemHOL ({ s with locals := tl } : CrepSemHOLState width σ)
                  with locals := newlocals } : CrepSemHOLState width σ) =
                  { decClockCrepSemHOL s with locals := newlocals } := rfl
              rw [hsame]
              rcases hb : evalCrepSemHOLProgExact { decClockCrepSemHOL s with locals := newlocals } prog
                with ⟨r0, st⟩
              simp only [hb] at hev ⊢
              have emp : ∀ (x : Option (CrepResultHOLExact width)),
                  (match x with
                   | some .timeOut => True | some (.return _) => True
                   | some (.exception _) => True | some (.finalFfi _) => True
                   | _ => False) →
                  (x, CrepSemHOLState.emptyLocals st) = (r, s') →
                  ∃ t', (x, CrepSemHOLState.emptyLocals st) = (r, t') ∧
                    crepInlineStateRelExact s' t' ∧
                    strongLocalsPost r s s' { s with locals := tl } t' := by
                intro x hx h
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
                unfold strongLocalsPost
                rcases x with _ | ⟨_ | _ | n | n | vs | ex | ev⟩ <;> first | trivial | exact hx.elim
              rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
              all_goals try simp only at hev ⊢
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
              · exact emp _ trivial hev
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
              · -- Return
                rcases info with _ | ⟨rts, hdl⟩
                · exact emp _ trivial hev
                · dsimp only at hev ⊢
                  by_cases hl : vs.length ≠ rts.length
                  · rw [if_pos hl] at hev
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
                  · rw [if_neg hl] at hev ⊢
                    cases hm : rts.mapM s.locals.lookup with
                    | none =>
                        simp only [hm] at hev
                        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
                    | some old =>
                        have htm : rts.mapM tl.lookup = some old := mapM_lookup_submap hloc rts old hm
                        simp only [hm] at hev
                        simp only [htm]
                        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                        exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
                          callReturnPost s { s with locals := tl } st st rts vs old hm hloc⟩
              · -- Exception
                rcases info with _ | ⟨rts, _ | ⟨eid, h⟩⟩
                · exact emp _ trivial hev
                · exact emp _ trivial hev
                · dsimp only at hev ⊢
                  by_cases he : ex = eid
                  · subst he
                    simp only [if_true] at hev ⊢
                    exact ih vals prog newlocals rts ex h st hargs hcode hn hc hb rfl r s'
                      { st with locals := tl } hev hne hloc
                      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                  · simp only [he, if_false] at hev ⊢
                    exact emp _ trivial hev
              · exact emp _ trivial hev

/-- `Call` case of HOL `evaluate_state_locals_rel_strong` (Resume at `:511-562`)
    for every call shape.  SPECIALISED, STRONGER case: only HOL `evaluate_ind`'s
    guarded handler premise is assumed; the callee premise is unnecessary because
    `state_rel` makes both callee start states equal (see the module note). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "evaluate_state_locals_rel_strong"
  (fmap_as_finite_support_relation :=
    [CrepSemHOLState.locals, CrepSemHOLState.globals, CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem evaluateStateLocalsRelStrongCallExact {width : Nat} [NeZero width] {σ : Type}
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ) (ih : StrongLocalsCallHandlerIH s info fname args)
    (r : Option (CrepResultHOLExact width)) (s' t : CrepSemHOLState width σ)
    (heval : evalCrepSemHOLProgExact s (.call info fname args) = (r, s'))
    (herror : r ≠ some .error)
    (hlocals : crepInlineLocalsRelExact s t) (hstate : crepInlineStateRelExact s t) :
    ∃ t', evalCrepSemHOLProgExact t (.call info fname args) = (r, t') ∧
      crepInlineStateRelExact s' t' ∧
      (match (generalizing := false) r with
       | none => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.break _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some (.continue _) => crepInlineLocalsRelExact s' t' ∧ crepInlineLocalsExtRelExact s s' t t'
       | some .error => False
       | _ => True) :=
  callStrongGoal info fname args s ih r s' t heval herror hlocals hstate

end Flapjack.CrepInlineExact
