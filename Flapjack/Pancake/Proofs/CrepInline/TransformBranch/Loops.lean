import Flapjack.Pancake.Proofs.CrepInline.TransformBranch.Cases
import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Call

/-!
# crep_inline `transform_branch_correct`: `While` and `Call` cases

`Resume transform_branch_correct[While]` and `[Call]`
(`cakeml/pancake/proofs/crep_inlineProofScript.sml:2124-2184`, bead
`flapjack-pxn.18.5.5.47.3`).  The induction hypotheses are the guarded
`evaluate_ind` premises at the motive `transformBranchGoal`, bundled as for
`transform_eoc_correct`.
-/

namespace Flapjack

namespace CrepInlineTransformBranch

open HolFiniteMapExact
open CrepInlineExact
open CrepInlineTransformEoc (stateRel_refl eq_of_stateRel_localsStrongRel
  mapM_some_of_fdom_eq)

namespace LoopsWitness
/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end LoopsWitness

/-- The three guarded recursion premises of HOL `evaluate_ind`'s While case,
specialized to `transformBranchGoal`.  Infrastructure; not a HOL theorem port. -/
structure TransformBranchWhileIH {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (s : CrepSemHOLState width σ) : Prop where
  continueCase : ∀ v2 w res s1 v1 v8,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
    res = some v1 → v1 = .continue v8 → v8 = 0 → transformBranchGoal (.while e c) s1
  normalCase : ∀ v2 w res s1,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
    res = none → transformBranchGoal (.while e c) s1
  bodyCase : ∀ v2 w,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    transformBranchGoal c (decClockCrepSemHOL s)

/-- Local support: the `While` case of the motive. -/
theorem whileGoal {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : TransformBranchWhileIH e c s) :
    transformBranchGoal (.while e c) s := by
  intro r s' ld rts ⟨hev, hlen, hfresh, ⟨z, hz⟩, hnd, hne⟩
  have hfc : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  simp only [transformBranchHOLExact]
  rw [evalCrepSemHOLProgExact_while_holShape] at hev ⊢
  split at hev
  · rename_i w hexp
    have hclass : crepExactEvalExpClassical s e = some (.word w) := by
      simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hexp
    by_cases hw : w ≠ 0
    · rw [if_pos hw] at hev ⊢
      by_cases hc : s.clock = 0
      · rw [if_pos hc] at hev ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
        exact ⟨_, _, rfl, stateRel_refl _, rfl⟩
      · rw [if_neg hc] at hev ⊢
        rcases hb : evalCrepSemHOLProgExact (decClockCrepSemHOL s) c with ⟨r0, s1⟩
        rw [hb] at hev
        dsimp only at hev
        have hne0 : r0 ≠ some .error := by
          rintro rfl
          simp only [exitLoopCrepResult] at hev
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact hne rfl
        have hlen0 : ∀ retvs, r0 = some (.return retvs) → rts.length = retvs.length := by
          rintro retvs rfl
          simp only [exitLoopCrepResult] at hev
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact hlen retvs rfl
        obtain ⟨ra, sa, heva, hrela, hposta⟩ :=
          ih.bodyCase (.word w) w hclass rfl hw hc r0 s1 (ld + 1) rts
            ⟨hb, hlen0, hfc, ⟨z, hz⟩, hnd, hne0⟩
        rw [heva]
        dsimp only
        have hdom : ∀ n, (r0 = none ∨ r0 = some (.continue n)) →
            ∃ z1, rts.mapM s1.locals.lookup = some z1 := by
          intro n hr
          have hd := evaluateLocalsSameFdom'Exact c (decClockCrepSemHOL s) r0 s1
            ⟨hb, by rcases hr with rfl | rfl <;> simp⟩
          exact mapM_some_of_fdom_eq hd rts z hz
        unfold transformBranchPost at hposta
        rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
        · obtain ⟨rfl, hl⟩ := hposta
          have hsa := eq_of_stateRel_localsStrongRel hrela hl
          subst hsa
          have hloop := ih.normalCase (.word w) w none s1 hclass rfl hw hc hb.symm rfl r s' ld rts
            ⟨hev, hlen, hfresh, hdom 0 (Or.inl rfl), hnd, hne⟩
          simpa only [transformBranchHOLExact] using hloop
        · exact absurd rfl hne0
        · subst hposta
          simp only [exitLoopCrepResult] at hev ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact ⟨_, _, rfl, hrela, rfl⟩
        · obtain ⟨rfl, hl⟩ := hposta
          cases n with
          | zero =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, hrela, rfl, hl⟩
          | succ n =>
              simp only [exitLoopCrepResult] at hev ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, hrela, rfl, hl⟩
        · obtain ⟨rfl, hl⟩ := hposta
          cases n with
          | zero =>
              have hsa := eq_of_stateRel_localsStrongRel hrela hl
              subst hsa
              have hloop := ih.continueCase (.word w) w _ s1 _ 0 hclass rfl hw hc hb.symm rfl rfl
                rfl r s' ld rts ⟨hev, hlen, hfresh, hdom 0 (Or.inr rfl), hnd, hne⟩
              simpa only [transformBranchHOLExact] using hloop
          | succ n =>
              simp only [exitLoopCrepResult] at hev ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, hrela, rfl, hl⟩
        · obtain ⟨rfl, hl⟩ := hposta
          simp only [exitLoopCrepResult] at hev ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact ⟨_, _, rfl, hrela, rfl, hl⟩
        · subst hposta
          simp only [exitLoopCrepResult] at hev ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact ⟨_, _, rfl, hrela, rfl⟩
        · subst hposta
          simp only [exitLoopCrepResult] at hev ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact ⟨_, _, rfl, hrela, rfl⟩
    · rw [if_neg hw] at hev ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      exact ⟨_, _, rfl, stateRel_refl _, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact absurd rfl hne

/-- HOL `evaluate_ind`'s guarded Call handler premise, specialized to
    `transformBranchGoal`. -/
def TransformBranchCallHandlerIH {width : Nat} [NeZero width] {σ : Type}
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
    transformBranchGoal handler { st with locals := s.locals }

/-- Local support: the tail call `Call NONE`, rewritten to
    `Seq (Call (SOME (rts, NONE))) (Break ld)`. -/
private theorem tailGoal {width : Nat} [NeZero width] {σ : Type}
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ) :
    transformBranchGoal (.call none fname args) s := by
  intro r s' ld rts ⟨hev, hlen, _, ⟨z, hz⟩, hnd, hne⟩
  simp only [transformBranchHOLExact]
  rw [evalCrepSemHOLProgExact_seq_fixClockFree]
  rw [evalCrepSemHOLProgExact_call_holShape] at hev ⊢
  have hnd' : ¬ crepReturnInfoNodupError
      (some (rts, (none : Option (BitVec width × CrepProgHOL width)))) := by
    simp [crepReturnInfoNodupError, hnd]
  have hnd0 : ¬ crepReturnInfoNodupError
      (none : Option (List Nat × Option (BitVec width × CrepProgHOL width))) := by
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
              rw [evalCrepSemHOLProgExact_break]
              exact ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl,
                CrepInlineTransformEoc.mapM_updateListEq_zip s.locals rts vs hnd hl⟩
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Local support: the handler call `Call (SOME (names, SOME (eid, h)))`. -/
private theorem handlerGoal {width : Nat} [NeZero width] {σ : Type}
    (names : List Nat) (eid : BitVec width) (h : CrepProgHOL width)
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (ih : TransformBranchCallHandlerIH s (some (names, some (eid, h))) fname args) :
    transformBranchGoal (.call (some (names, some (eid, h))) fname args) s := by
  intro r s' ld rts ⟨hev, hlen, hfresh, hz, hnd, hne⟩
  have hfh : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact h := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  simp only [transformBranchHOLExact]
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
              (some (names, some (eid, h)) : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
          · simp only [hn, if_true] at hev
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            exact absurd rfl hne
          · have hn' : ¬ crepReturnInfoNodupError
                (some (names, some (eid, transformBranchHOLExact ld rts h)) :
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
                  exact ih vals prog newlocals names ex h st hargs hcode hn hc hb rfl r s' ld rts
                    ⟨hev, hlen, hfh, hz, hnd, hne⟩
                · simp only [he, if_false] at hev ⊢
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                  exact ⟨_, _, rfl, stateRel_refl _, rfl⟩
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                exact ⟨_, _, rfl, stateRel_refl _, rfl⟩

/-- Flapjack-specific stronger handler-only Call calculation for every call
shape. It omits the unused callee induction hypothesis and is deliberately
untagged; the exact wrapper below retains both original hypotheses. -/
theorem callGoal {width : Nat} [NeZero width] {σ : Type}
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (ih : TransformBranchCallHandlerIH s info fname args) :
    transformBranchGoal (.call info fname args) s := by
  rcases info with _ | ⟨names, _ | ⟨eid, h⟩⟩
  · exact tailGoal fname args s
  · exact leafGoal _ s (fun _ _ => by simp [transformBranchHOLExact]) (by simp [hasReturnHOLExact])
  · exact handlerGoal names eid h fname args s ih

/-- `While` case (Resume at `:2124-2165`), with exactly the guarded
    `evaluate_ind` While premises. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_branch_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformBranchCorrect_While {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : TransformBranchWhileIH e c s) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (ld : Nat) (rts : List Nat),
      evalCrepSemHOLProgExact s (.while e c) = (r, s') ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.while e c)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformBranchHOLExact ld rts (.while e c)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = some (.break ld) ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  whileGoal e c s ih

/-- Exact `Call` induction case of `transform_branch_correct`.
Both original guarded callee and matching-handler hypotheses are retained.
The callee hypothesis is unused: the unchanged callee run starts from the same
state, and caller locals are restored. The existing untagged `callGoal`
calculation needs only the handler hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_branch_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformBranchCorrect_Call {width : Nat} [NeZero width] {σ : Type}
    (info : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : Flapjack.Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ)
    (_ihCallee : ∀ values prog newlocals,
      args.mapM (evalCrepSemHOLExp s) = some values →
      lookupCodeFiniteHOL s.code fname values values.length = some (prog, newlocals) →
      ¬ crepReturnInfoNodupError info → s.clock ≠ 0 →
      transformBranchGoal prog {decClockCrepSemHOL s with locals := newlocals})
    (ih : TransformBranchCallHandlerIH s info fname args) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (ld : Nat) (rts : List Nat),
      evalCrepSemHOLProgExact s (.call info fname args) = (r, s') ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.call info fname args)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformBranchHOLExact ld rts (.call info fname args)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = some (.break ld) ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  callGoal info fname args s ih

end CrepInlineTransformBranch

end Flapjack
