import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Cases

/-!
# crep_inline `transform_branch_correct`: motive and non-suspended cases

Counterpart of `cakeml/pancake/proofs/crep_inlineProofScript.sml:2042-2122`
(bead `flapjack-pxn.18.5.5.47.3`).  As for `transform_eoc_correct`, HOL proves
the theorem by `recInduct evaluate_ind`, suspending `While` and `Call`; the
tagged cases below take exactly the guarded `evaluate_ind` premises for their
constructor at the motive `transformBranchGoal`.  HOL's statement binds a
variable `res` that occurs only as the (shadowing) catch-all pattern of the
final `case`; the outer binder is vacuous and is omitted.
-/

namespace Flapjack

namespace CrepInlineTransformBranch

open HolFiniteMapExact
open CrepInlineExact
open CrepInlineTransformEoc (stateRel_refl eq_of_stateRel_localsStrongRel
  mapM_some_of_fdom_eq panMap2_eq_zipWith)

/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- HOL's result-indexed conclusion of `transform_branch_correct` (its final
    `case r of ...`).  Untagged: part of the theorem statement. -/
def transformBranchPost {width : Nat} [NeZero width] {σ : Type} (ld : Nat) (rts : List Nat)
    (r r1 : Option (CrepResultHOLExact width)) (s' s1' : CrepSemHOLState width σ) : Prop :=
  match r with
  | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
  | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
  | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
  | some (.return retvs) => r1 = some (.break ld) ∧ rts.mapM s1'.locals.lookup = some retvs
  | some .error => False
  | _ => r1 = r

/-- The `evaluate_ind` motive of HOL `transform_branch_correct` at `(p, s)`.
    Untagged Flapjack spelling of the motive. -/
def transformBranchGoal {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ) : Prop :=
  ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (ld : Nat) (rts : List Nat),
    evalCrepSemHOLProgExact s p = (r, s') ∧
      (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
      (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact p) ∧
      (∃ z, rts.mapM s.locals.lookup = some z) ∧
      rts.Nodup ∧
      r ≠ some .error →
    ∃ r1 s1', evalCrepSemHOLProgExact s (transformBranchHOLExact ld rts p) = (r1, s1') ∧
      crepInlineStateRelExact s' s1' ∧ transformBranchPost ld rts r r1 s' s1'

/-- Local support: programs `transform_branch` leaves unchanged and that
    contain no `Return`. -/
theorem leafGoal {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (htr : ∀ ld rts, transformBranchHOLExact ld rts p = p) (hnr : hasReturnHOLExact p = false) :
    transformBranchGoal p s := by
  intro r s' ld rts ⟨hev, _, _, _, _, hne⟩
  refine ⟨r, s', by rw [htr]; exact hev, stateRel_refl s', ?_⟩
  obtain ⟨r0, s0, hev0, hm⟩ := CrepInlineNoReturn.notHasReturnNotEvaluateReturn p s hnr
  rw [hev] at hev0
  obtain ⟨hr, _⟩ := Prod.mk.inj hev0
  subst hr
  unfold transformBranchPost
  rcases r with _ | ⟨_ | _ | n | n | vs | e | ev⟩ <;>
    simp [crepInlineLocalsStrongRelExact] at hm hne ⊢

/-- Local support: the `Return` case. -/
private theorem returnGoal {width : Nat} [NeZero width] {σ : Type}
    (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ) :
    transformBranchGoal (.return es) s := by
  intro r s' ld rts ⟨hev, hlen, hfresh, ⟨z, hz⟩, hnd, hne⟩
  rw [evalCrepSemHOLProgExact_return] at hev
  cases hws : es.mapM (evalCrepSemHOLExp s) with
  | none => rw [hws] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some ws =>
      rw [hws] at hev
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      have hfr : ∀ x, x ∈ rts → x ∉ (es.map crepExpVarsHOL).flatten := by
        intro x hx hm
        apply hfresh x hx
        simpa [crepVarProgHOLExact, List.flatMap] using hm
      obtain ⟨s1, hev1, hrel, _, hlook⟩ :=
        CrepInlineNestedSeqAssign.evaluateNestedSeqAssign rts s es ws z
          ⟨hws, hfr, hz, hlen ws rfl, hnd⟩
      refine ⟨some (.break ld), s1, ?_, ?_, ⟨rfl, hlook⟩⟩
      · simp only [transformBranchHOLExact]
        rw [evalCrepSemHOLProgExact_seq_fixClockFree, ← panMap2_eq_zipWith, hev1]
        exact evalCrepSemHOLProgExact_break s1 ld
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- Local support: the `Dec` case from its guarded body premise. -/
private theorem decGoal {width : Nat} [NeZero width] {σ : Type}
    (v : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ value, crepExactEvalExpClassical s e = some value →
      transformBranchGoal body (CrepSemHOLState.setVar v value s)) :
    transformBranchGoal (.dec v e body) s := by
  intro r s' ld rts ⟨hev, hlen, hfresh, ⟨z, hz⟩, hnd, hne⟩
  rw [evalCrepSemHOLProgExact_dec_holShape] at hev
  cases hval : evalCrepSemHOLExp s e with
  | none => rw [hval] at hev; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev; exact absurd rfl hne
  | some val =>
      rw [hval] at hev
      dsimp only at hev
      let su : CrepSemHOLState width σ := { s with locals := s.locals.updateEq (v, val) }
      rcases hbody : evalCrepSemHOLProgExact su body with ⟨r0, st⟩
      simp only [su] at hbody
      rw [hbody] at hev
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      have hv : v ∉ rts := fun hm => hfresh v hm (by simp [crepVarProgHOLExact])
      have hfresh' : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact body := fun x hx hm =>
        hfresh x hx (by simp [crepVarProgHOLExact, hm])
      obtain ⟨z', hz'⟩ := CrepInlineNestedSeqAssign.optMmapSomeImpFupdateExistSome rts s.locals z
        (v, val) hz
      have hcl : crepExactEvalExpClassical s e = some val := by
        simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hval
      obtain ⟨r1, s1, hev1, hrel1, hpost1⟩ := ih val hcl r0 st ld rts
        ⟨hbody, hlen, hfresh', ⟨z', hz'⟩, hnd, hne⟩
      refine ⟨r1, { s1 with locals := s1.locals.resVarEq (v, s.locals.lookup v) }, ?_, ?_, ?_⟩
      · simp only [transformBranchHOLExact]
        rw [evalCrepSemHOLProgExact_dec_holShape, hval]
        dsimp only
        simp only [CrepSemHOLState.setVar] at hev1
        rw [hev1]
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel1
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      · unfold transformBranchPost at hpost1 ⊢
        rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
        · exact ⟨hpost1.1, by simp only [crepInlineLocalsStrongRelExact] at hpost1 ⊢; rw [hpost1.2]⟩
        · exact hpost1
        · exact hpost1
        · exact ⟨hpost1.1, by simp only [crepInlineLocalsStrongRelExact] at hpost1 ⊢; rw [hpost1.2]⟩
        · exact ⟨hpost1.1, by simp only [crepInlineLocalsStrongRelExact] at hpost1 ⊢; rw [hpost1.2]⟩
        · refine ⟨hpost1.1, ?_⟩
          rw [← hpost1.2]
          refine OPT_MMAP_ALL_EQ _ _ rts (fun x hx => ?_)
          have hxv : x ≠ v := fun heq => hv (heq ▸ hx)
          cases s.locals.lookup v <;> simp [FDOMSUB_HOL, FUPDATE_HOL, hxv]
        · exact hpost1
        · exact hpost1

/-- Local support: the `If` case from its guarded selected-branch premise. -/
private theorem iteGoal {width : Nat} [NeZero width] {σ : Type}
    (c : CrepExpHOL width) (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ v1 w, crepExactEvalExpClassical s c = some v1 → v1 = .word w →
      transformBranchGoal (if w ≠ 0 then c1 else c2) s) :
    transformBranchGoal (.ite c c1 c2) s := by
  intro r s' ld rts ⟨hev, hlen, hfresh, hz, hnd, hne⟩
  have hf1 : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c1 := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  have hf2 : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c2 := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  rw [evalCrepSemHOLProgExact_ite] at hev
  simp only [transformBranchHOLExact]
  rw [evalCrepSemHOLProgExact_ite]
  split at hev
  · rename_i w hcond
    have hcl : crepExactEvalExpClassical s c = some (.word w) := by
      simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hcond
    have hsel := ih (.word w) w hcl rfl
    by_cases hw : w ≠ 0
    · rw [if_pos hw] at hev hsel ⊢
      exact hsel r s' ld rts ⟨hev, hlen, hf1, hz, hnd, hne⟩
    · rw [if_neg hw] at hev hsel ⊢
      exact hsel r s' ld rts ⟨hev, hlen, hf2, hz, hnd, hne⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact absurd rfl hne

/-- Local support: the `Seq` case from its guarded premises. -/
private theorem seqGoal {width : Nat} [NeZero width] {σ : Type}
    (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih2 : ∀ res s1, (res, s1) = evalCrepSemHOLProgExact s c1 → res = none →
      transformBranchGoal c2 s1)
    (ih1 : transformBranchGoal c1 s) :
    transformBranchGoal (.seq c1 c2) s := by
  intro r s' ld rts ⟨hev, hlen, hfresh, ⟨z, hz⟩, hnd, hne⟩
  have hf1 : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c1 := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  have hf2 : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c2 := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  rw [evalCrepSemHOLProgExact_seq_fixClockFree] at hev
  simp only [transformBranchHOLExact]
  rw [evalCrepSemHOLProgExact_seq_fixClockFree]
  rcases hstep : evalCrepSemHOLProgExact s c1 with ⟨r0, s1⟩
  rw [hstep] at hev
  cases r0 with
  | none =>
      obtain ⟨ra, sa, heva, hrela, hposta⟩ := ih1 none s1 ld rts
        ⟨hstep, fun _ h => absurd h (by simp), hf1, ⟨z, hz⟩, hnd, by simp⟩
      unfold transformBranchPost at hposta
      obtain ⟨rfl, hl⟩ := hposta
      have hsa := eq_of_stateRel_localsStrongRel hrela hl
      subst hsa
      rw [heva]
      have hdom := evaluateLocalsSameFdom'Exact c1 s none s1 ⟨hstep, Or.inl rfl⟩
      obtain ⟨z1, hz1⟩ := mapM_some_of_fdom_eq hdom rts z hz
      exact ih2 none s1 hstep.symm rfl r s' ld rts ⟨hev, hlen, hf2, ⟨z1, hz1⟩, hnd, hne⟩
  | some x =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
      obtain ⟨ra, sa, heva, hrela, hposta⟩ := ih1 (some x) s1 ld rts
        ⟨hstep, hlen, hf1, ⟨z, hz⟩, hnd, hne⟩
      rw [heva]
      unfold transformBranchPost at hposta ⊢
      rcases x with _ | _ | n | n | vs | ex | ev
      · exact absurd rfl hne
      · subst hposta; exact ⟨_, _, rfl, hrela, rfl⟩
      · obtain ⟨rfl, hl⟩ := hposta; exact ⟨_, _, rfl, hrela, rfl, hl⟩
      · obtain ⟨rfl, hl⟩ := hposta; exact ⟨_, _, rfl, hrela, rfl, hl⟩
      · obtain ⟨rfl, hl⟩ := hposta; exact ⟨_, _, rfl, hrela, rfl, hl⟩
      · subst hposta; exact ⟨_, _, rfl, hrela, rfl⟩
      · subst hposta; exact ⟨_, _, rfl, hrela, rfl⟩

/-! ## Tagged cases (HOL goal for each constructor; guarded `evaluate_ind` premises only) -/

/-- Programs left unchanged by `transform_branch` (the final `rw` of HOL's
    proof); no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_branch_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformBranchCorrect_Leaf {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (hp : p = .skip ∨ (∃ n e, p = .assign n e) ∨ (∃ ns op args, p = .primitive ns op args) ∨
      (∃ a b, p = .store a b) ∨ (∃ a b, p = .store32 a b) ∨ (∃ a b, p = .storeByte a b) ∨
      (∃ a b, p = .storeGlob a b) ∨ (∃ n, p = .break n) ∨ (∃ n, p = .continue n) ∨
      (∃ e, p = .raise e) ∨ p = .tick ∨
      (∃ f a b c d, p = .extCall f a b c d) ∨ (∃ op n a, p = .shMem op n a)) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (ld : Nat) (rts : List Nat),
      evalCrepSemHOLProgExact s (p) = (r, s') ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (p)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformBranchHOLExact ld rts (p)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = some (.break ld) ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r := by
  have hleaf : (∀ ld rts, transformBranchHOLExact ld rts p = p) ∧ hasReturnHOLExact p = false := by
    rcases hp with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ |
      ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl | ⟨_, _, _, _, _, rfl⟩ |
      ⟨_, _, _, rfl⟩ <;>
      exact ⟨fun _ _ => by simp [transformBranchHOLExact], by simp [hasReturnHOLExact]⟩
  exact leafGoal p s hleaf.1 hleaf.2

/-- `Return` case; no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_branch_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformBranchCorrect_Return {width : Nat} [NeZero width] {σ : Type}
    (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (ld : Nat) (rts : List Nat),
      evalCrepSemHOLProgExact s (.return es) = (r, s') ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.return es)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformBranchHOLExact ld rts (.return es)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = some (.break ld) ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  returnGoal es s

/-- `Dec` case, with HOL `evaluate_ind`'s guarded body premise. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_branch_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformBranchCorrect_Dec {width : Nat} [NeZero width] {σ : Type}
    (v : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ value, crepExactEvalExpClassical s e = some value →
      transformBranchGoal body (CrepSemHOLState.setVar v value s)) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (ld : Nat) (rts : List Nat),
      evalCrepSemHOLProgExact s (.dec v e body) = (r, s') ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.dec v e body)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformBranchHOLExact ld rts (.dec v e body)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = some (.break ld) ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  decGoal v e body s ih

/-- `If` case, with HOL `evaluate_ind`'s guarded selected-branch premise. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_branch_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformBranchCorrect_If {width : Nat} [NeZero width] {σ : Type}
    (c : CrepExpHOL width) (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ v1 w, crepExactEvalExpClassical s c = some v1 → v1 = .word w →
      transformBranchGoal (if w ≠ 0 then c1 else c2) s) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (ld : Nat) (rts : List Nat),
      evalCrepSemHOLProgExact s (.ite c c1 c2) = (r, s') ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.ite c c1 c2)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformBranchHOLExact ld rts (.ite c c1 c2)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = some (.break ld) ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  iteGoal c c1 c2 s ih

/-- `Seq` case, with HOL `evaluate_ind`'s two Seq premises. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_branch_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformBranchCorrect_Seq {width : Nat} [NeZero width] {σ : Type}
    (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih2 : ∀ res s1, (res, s1) = evalCrepSemHOLProgExact s c1 → res = none →
      transformBranchGoal c2 s1)
    (ih1 : transformBranchGoal c1 s) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (ld : Nat) (rts : List Nat),
      evalCrepSemHOLProgExact s (.seq c1 c2) = (r, s') ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.seq c1 c2)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformBranchHOLExact ld rts (.seq c1 c2)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = some (.break ld) ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  seqGoal c1 c2 s ih2 ih1

end CrepInlineTransformBranch

end Flapjack
