import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Cases
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Call

/-!
# crep_inline `transform_eoc_correct`: the `Call` case

`Resume transform_eoc_correct[Call]` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2024-2038`,
bead `flapjack-pxn.18.5.5.47.2.3`).  `transform_eoc` rewrites a tail call
`Call NONE` to `Call (SOME (rts, NONE))`, leaves `Call (SOME (_, NONE))`
unchanged and transforms the handler of `Call (SOME (_, SOME (eid, p)))`.  The
tagged case takes both of HOL `evaluate_ind`'s guarded Call premises (callee and
handler), specialized to `transformEocGoal` (bead `flapjack-pxn.18.5.5.47.5`);
the proof, the untagged `callEocGoal`, uses only the handler premise.
-/

namespace Flapjack

namespace CrepInlineTransformEoc

open HolFiniteMapExact
open CrepInlineExact

namespace CallWitness
/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end CallWitness

/-- Local support: distinct keys updated by `ZIP` read back their values
    (HOL `opt_mmap_some_eq_zip_flookup` on the finite-support carrier). -/
theorem mapM_updateListEq_zip {β : Type} (m : HolFiniteMapExact Nat β) :
    ∀ (xs : List Nat) (ys : List β), xs.Nodup → xs.length = ys.length →
      xs.mapM (m.updateListEq (xs.zip ys)).lookup = some ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: xs, y :: ys, hnd, hlen => by
      have hnd' := List.nodup_cons.1 hnd
      have hl : (m.updateListEq ((x, y) :: xs.zip ys)).lookup =
          ((m.updateEq (x, y)).updateListEq (xs.zip ys)).lookup := rfl
      have hx : x ∉ (xs.zip ys).map Prod.fst := by
        intro hm
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        exact hnd'.1 (List.of_mem_zip he).1
      have hrest := mapM_updateListEq_zip (m.updateEq (x, y)) xs ys hnd'.2 (by simpa using hlen)
      simp only [List.zip_cons_cons, List.mapM_cons, hl]
      rw [hrest]
      have hxl : ((m.updateEq (x, y)).updateListEq (xs.zip ys)).lookup x = some y := by
        rw [lookup_updateListEq]
        exact (FLOOKUP_FUPDATE_LIST_HOL_not_mem _ _ x hx).trans (by simp [FLOOKUP, updateEq, FUPDATE_HOL])
      rw [hxl]
      rfl

/-- Local support: the tail call `Call NONE`. -/
private theorem tailGoal {width : Nat} [NeZero width] {σ : Type}
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ) :
    transformEocGoal (.call none fname args) s := by
  intro r s' res rts ⟨hev, _, _, hlen, _, ⟨z, hz⟩, hnd, hne⟩
  simp only [transformEocHOLExact]
  rw [evalCrepSemHOLProgExact_call_holShape] at hev ⊢
  have hnd' : ¬ crepReturnInfoNodupError (some (rts, (none : Option (BitVec width × CrepProgHOL width)))) := by
    simp [crepReturnInfoNodupError, hnd]
  have hnd0 : ¬ crepReturnInfoNodupError (none : Option (List Nat × Option (BitVec width × CrepProgHOL width))) := by
    simp [crepReturnInfoNodupError]
  cases hargs : args.mapM (evalCrepSemHOLExp s) with
  | none => simp only [hargs] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some vals =>
      simp only [hargs] at hev ⊢
      cases hcode : lookupCodeFiniteHOL s.code fname vals vals.length with
      | none => simp only [hcode] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
      | some pn =>
          obtain ⟨prog, newlocals⟩ := pn
          simp only [hcode, if_neg hnd', if_neg hnd0] at hev ⊢
          by_cases hc : s.clock = 0
          · simp only [hc, if_true] at hev ⊢
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            exact ⟨_, _, rfl, stateRel_refl _, rfl⟩
          · simp only [hc, if_false] at hev ⊢
            rcases hb : evalCrepSemHOLProgExact { decClockCrepSemHOL s with locals := newlocals } prog
              with ⟨r0, st⟩
            simp only [hb] at hev ⊢
            rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩ <;> simp only at hev ⊢
            all_goals first
              | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne)
              | skip
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              have hl := hlen vs rfl
              simp only [show ¬ (vs.length ≠ rts.length) from fun h => h hl.symm, if_false, hz]
              exact ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl,
                mapM_updateListEq_zip s.locals rts vs hnd hl⟩
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- HOL `evaluate_ind`'s guarded Call callee premise, specialized to
    `transformEocGoal`: arguments evaluate, the code lookup succeeds, the return
    names are distinct and the clock is nonzero. -/
def TransformEocCallCalleeIH {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ)
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width)) : Prop :=
  ∀ values prog newlocals,
    args.mapM (evalCrepSemHOLExp s) = some values →
    lookupCodeFiniteHOL s.code fname values values.length = some (prog, newlocals) →
    ¬ crepReturnInfoNodupError info → s.clock ≠ 0 →
    transformEocGoal prog { decClockCrepSemHOL s with locals := newlocals }

/-- HOL `evaluate_ind`'s guarded Call handler premise, specialized to
    `transformEocGoal` (as `ihHandler` of the accepted locals-domain Call case). -/
def TransformEocCallHandlerIH {width : Nat} [NeZero width] {σ : Type}
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
    transformEocGoal handler { st with locals := s.locals }

/-- Local support: the handler call `Call (SOME (names, SOME (eid, h)))`. -/
private theorem handlerGoal {width : Nat} [NeZero width] {σ : Type}
    (names : List Nat) (eid : BitVec width) (h : CrepProgHOL width)
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (ih : TransformEocCallHandlerIH s (some (names, some (eid, h))) fname args) :
    transformEocGoal (.call (some (names, some (eid, h))) fname args) s := by
  intro r s' res rts ⟨hev, hue, hnb, hlen, hfresh, hz, hnd, hne⟩
  rcases huh : unreachElimHOLExact h with ⟨h', xh⟩
  simp only [unreachElimHOLExact, huh, Prod.mk.injEq, CrepProgHOL.call.injEq,
    Option.some.injEq] at hue
  obtain ⟨⟨⟨_, _, rfl⟩, _, _⟩, _⟩ := hue
  simp only [notBranchRetHOLExact, Bool.not_eq_true'] at hnb
  have hnbh := CrepInlineUnreachElim.notHasReturnImpNotBranchRet h' (by simp [hnb])
  have hfh : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact h' := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  simp only [transformEocHOLExact]
  rw [evalCrepSemHOLProgExact_call_holShape] at hev ⊢
  cases hargs : args.mapM (evalCrepSemHOLExp s) with
  | none => simp only [hargs] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some vals =>
      simp only [hargs] at hev ⊢
      cases hcode : lookupCodeFiniteHOL s.code fname vals vals.length with
      | none => simp only [hcode] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
      | some pn =>
          obtain ⟨prog, newlocals⟩ := pn
          simp only [hcode] at hev ⊢
          by_cases hn : crepReturnInfoNodupError
              (some (names, some (eid, h')) : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
          · have hn' : crepReturnInfoNodupError
                (some (names, some (eid, transformEocHOLExact rts h')) :
                  Option (List Nat × Option (BitVec width × CrepProgHOL width))) := by
              simpa [crepReturnInfoNodupError] using hn
            simp only [hn, if_true] at hev
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            exact absurd rfl hne
          · have hn' : ¬ crepReturnInfoNodupError
                (some (names, some (eid, transformEocHOLExact rts h')) :
                  Option (List Nat × Option (BitVec width × CrepProgHOL width))) := by
              simpa [crepReturnInfoNodupError] using hn
            simp only [hn, hn', if_false] at hev ⊢
            by_cases hc : s.clock = 0
            · simp only [hc, if_true] at hev ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, stateRel_refl _, rfl⟩
            · simp only [hc, if_false] at hev ⊢
              rcases hb : evalCrepSemHOLProgExact { decClockCrepSemHOL s with locals := newlocals } prog
                with ⟨r0, st⟩
              simp only [hb] at hev ⊢
              rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩ <;> simp only at hev ⊢
              all_goals first
                | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne)
                | skip
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                exact ⟨_, _, rfl, stateRel_refl _, rfl⟩
              · by_cases hl : vs.length ≠ names.length
                · rw [if_pos hl] at hev
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
                · rw [if_neg hl] at hev ⊢
                  cases hm : names.mapM s.locals.lookup with
                  | none =>
                      simp only [hm] at hev
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
                  | some _ =>
                      simp only [hm] at hev ⊢
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                      exact ⟨_, _, rfl, stateRel_refl _, rfl, rfl⟩
              · by_cases he : ex = eid
                · subst he
                  simp only [if_true] at hev ⊢
                  exact ih vals prog newlocals names ex h' st hargs hcode hn hc hb rfl r s' xh rts
                    ⟨hev, huh, hnbh, hlen, hfh, hz, hnd, hne⟩
                · simp only [he, if_false] at hev ⊢
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                  exact ⟨_, _, rfl, stateRel_refl _, rfl⟩
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                exact ⟨_, _, rfl, stateRel_refl _, rfl⟩

/-- Local support (untagged): the `Call` case of HOL `transform_eoc_correct`
    for every call shape from the guarded handler premise alone.  This is not
    HOL's case shape (the callee premise is omitted, being unused); the tagged
    `transformEocCorrect_Call` restores it. -/
theorem callEocGoal {width : Nat} [NeZero width] {σ : Type}
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (ih : TransformEocCallHandlerIH s info fname args) :
    transformEocGoal (.call info fname args) s := by
  rcases info with _ | ⟨names, _ | ⟨eid, h⟩⟩
  · exact tailGoal fname args s
  · exact leafGoal _ s (fun _ => by simp [transformEocHOLExact]) (by simp [hasReturnHOLExact])
  · exact handlerGoal names eid h fname args s ih

/-- `Call` case of HOL `transform_eoc_correct` (Resume at `:2024-2038`), for
    every call shape, with exactly HOL `evaluate_ind`'s two guarded Call
    premises: the callee premise `_ihCallee` (unused by the proof, as in HOL)
    and the handler premise `ih`, with tuple/result aliases normalized.  The
    assembled theorem discharges both internally. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_eoc_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformEocCorrect_Call {width : Nat} [NeZero width] {σ : Type}
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (_ihCallee : TransformEocCallCalleeIH s info fname args)
    (ih : TransformEocCallHandlerIH s info fname args) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (res : Option CrepEarlyExitHOL) (rts : List Nat),
      evalCrepSemHOLProgExact s (.call info fname args) = (r, s') ∧
        unreachElimHOLExact (.call info fname args) = ((.call info fname args), res) ∧
        notBranchRetHOLExact (.call info fname args) = true ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.call info fname args)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformEocHOLExact rts (.call info fname args)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  callEocGoal info fname args s ih

end CrepInlineTransformEoc

end Flapjack
