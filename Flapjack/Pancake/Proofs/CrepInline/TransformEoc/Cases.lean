import Flapjack.Pancake.Proofs.CrepInline.NestedSeqAssign
import Flapjack.Pancake.Proofs.CrepInline.EvaluateLocals.Assembly
import Flapjack.Pancake.Proofs.CrepInline.NotBranchReturn
import Flapjack.Pancake.Proofs.CrepInline.UnreachElimProgSize
import Flapjack.Pancake.CrepInline.Pass

/-!
# crep_inline `transform_eoc_correct`: motive and non-suspended cases

Counterpart of `cakeml/pancake/proofs/crep_inlineProofScript.sml:1893-1977`
(bead `flapjack-pxn.18.5.5.47.2.1`).  HOL proves `transform_eoc_correct` by
`recInduct evaluate_ind`, suspending `While` and `Call`; this module gives the
motive and the remaining cases: the programs `transform_eoc` leaves unchanged,
`Return`, `Dec`, `If` and `Seq`.  Each tagged case states HOL's goal for its
constructor; the only extra hypotheses are HOL `evaluate_ind`'s guarded
premises for that constructor, at the motive `transformEocGoal`.
Renderings are those of `NestedSeqAssign`; `unreach_elim`, `not_branch_ret`,
`var_prog`, `transform_eoc` and `locals_strong_rel` are the tagged
`unreachElimHOLExact`, `notBranchRetHOLExact`, `crepVarProgHOLExact`,
`transformEocHOLExact` and `crepInlineLocalsStrongRelExact`.
-/

namespace Flapjack

namespace CrepInlineTransformEoc

open HolFiniteMapExact
open CrepInlineExact

/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

/-- HOL's result-indexed conclusion of `transform_eoc_correct` (the final
    `case r of ...`).  Untagged: part of the theorem statement, not a HOL
    declaration. -/
def transformEocPost {width : Nat} [NeZero width] {σ : Type} (rts : List Nat)
    (r r1 : Option (CrepResultHOLExact width)) (s' s1' : CrepSemHOLState width σ) : Prop :=
  match r with
  | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
  | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
  | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
  | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
  | some .error => False
  | _ => r1 = r

/-- The `evaluate_ind` motive of HOL `transform_eoc_correct` at `(p, s)`:
    `∀r s' res rts. <HOL hypotheses> ⇒ ∃r1 s1'. <HOL conclusion>`.  Untagged
    Flapjack spelling of the motive, used for the sub-program induction
    hypotheses of the case theorems. -/
def transformEocGoal {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ) : Prop :=
  ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (res : Option CrepEarlyExitHOL) (rts : List Nat),
    evalCrepSemHOLProgExact s p = (r, s') ∧
      unreachElimHOLExact p = (p, res) ∧
      notBranchRetHOLExact p = true ∧
      (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
      (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact p) ∧
      (∃ z, rts.mapM s.locals.lookup = some z) ∧
      rts.Nodup ∧
      r ≠ some .error →
    ∃ r1 s1', evalCrepSemHOLProgExact s (transformEocHOLExact rts p) = (r1, s1') ∧
      crepInlineStateRelExact s' s1' ∧ transformEocPost rts r r1 s' s1'

/-- Local support: `state_rel` is reflexive. -/
theorem stateRel_refl {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) : crepInlineStateRelExact s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Local support: `state_rel` with equal locals is state equality
    (HOL `state_component_equality`). -/
theorem eq_of_stateRel_localsStrongRel {width : Nat} [NeZero width] {σ : Type}
    {s t : CrepSemHOLState width σ} (h : crepInlineStateRelExact s t)
    (hl : crepInlineLocalsStrongRelExact s t) : s = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  cases s; cases t
  simp only [crepInlineLocalsStrongRelExact] at hl
  simp_all

/-- Local support: `MAP2` as `List.zipWith`. -/
private theorem panMap2_eq_zipWith {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β), panMap2 f xs ys = List.zipWith f xs ys
  | [], _ => by simp [panMap2]
  | _ :: _, [] => by simp [panMap2]
  | x :: xs, y :: ys => by simp [panMap2, panMap2_eq_zipWith f xs ys]

/-- Local support: equal `FDOM`s transfer a successful `OPT_MMAP FLOOKUP`
    (HOL `fdoms_eq_opt_mmap_flookup_some` on the finite-support carrier). -/
theorem mapM_some_of_fdom_eq {β : Type} {f g : Nat → Option β}
    (h : crepHolFdom f = crepHolFdom g) :
    ∀ (vs : List Nat) (vals : List β), vs.mapM f = some vals → ∃ z, vs.mapM g = some z
  | [], _, _ => ⟨[], rfl⟩
  | v :: vs, vals, hv => by
      simp only [List.mapM_cons] at hv
      cases hf : f v with
      | none => simp [hf] at hv
      | some y =>
          cases hr : vs.mapM f with
          | none => simp [hf, hr] at hv
          | some ys =>
              have hd := congrFun h v
              simp only [crepHolFdom, hf, Option.isSome_some] at hd
              cases hg : g v with
              | none => simp [hg] at hd
              | some z =>
                  obtain ⟨zs, hzs⟩ := mapM_some_of_fdom_eq h vs ys hr
                  exact ⟨z :: zs, by simp [List.mapM_cons, hg, hzs]⟩

/-- Local support: programs that `transform_eoc` leaves unchanged and that
    contain no `Return`. -/
theorem leafGoal {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (htr : ∀ rts, transformEocHOLExact rts p = p) (hnr : hasReturnHOLExact p = false) :
    transformEocGoal p s := by
  intro r s' res rts ⟨hev, _, _, _, _, _, _, hne⟩
  refine ⟨r, s', by rw [htr]; exact hev, stateRel_refl s', ?_⟩
  obtain ⟨r0, s0, hev0, hm⟩ := CrepInlineNoReturn.notHasReturnNotEvaluateReturn p s hnr
  rw [hev] at hev0
  obtain ⟨hr, _⟩ := Prod.mk.inj hev0
  subst hr
  unfold transformEocPost
  rcases r with _ | ⟨_ | _ | n | n | vs | e | ev⟩ <;>
    simp [crepInlineLocalsStrongRelExact] at hm hne ⊢

/-- Local support: the `Return` case. -/
private theorem returnGoal {width : Nat} [NeZero width] {σ : Type}
    (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ) :
    transformEocGoal (.return es) s := by
  intro r s' res rts ⟨hev, _, _, hlen, hfresh, ⟨z, hz⟩, hnd, hne⟩
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
      refine ⟨none, s1, ?_, ?_, ⟨rfl, hlook⟩⟩
      · simp only [transformEocHOLExact]
        rw [← panMap2_eq_zipWith]
        exact hev1
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- Local support: the `Dec` case, from the motive for the body. -/
private theorem decGoal {width : Nat} [NeZero width] {σ : Type}
    (v : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ value, crepExactEvalExpClassical s e = some value →
      transformEocGoal body (CrepSemHOLState.setVar v value s)) :
    transformEocGoal (.dec v e body) s := by
  intro r s' res rts ⟨hev, hue, hnb, hlen, hfresh, ⟨z, hz⟩, hnd, hne⟩
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
      rcases hub : unreachElimHOLExact body with ⟨b', x'⟩
      have hue' : unreachElimHOLExact body = (body, res) := by
        simp only [unreachElimHOLExact, hub, Prod.mk.injEq, CrepProgHOL.dec.injEq] at hue
        rw [hub, hue.1.2.2, hue.2]
      have hv : v ∉ rts := fun hm => hfresh v hm (by simp [crepVarProgHOLExact])
      have hfresh' : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact body := fun x hx hm =>
        hfresh x hx (by simp [crepVarProgHOLExact, hm])
      obtain ⟨z', hz'⟩ := CrepInlineNestedSeqAssign.optMmapSomeImpFupdateExistSome rts s.locals z
        (v, val) hz
      have hcl : crepExactEvalExpClassical s e = some val := by
        simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hval
      obtain ⟨r1, s1, hev1, hrel1, hpost1⟩ := ih val hcl r0 st res rts
        ⟨hbody, hue', by simpa [notBranchRetHOLExact] using hnb, hlen, hfresh', ⟨z', hz'⟩,
          hnd, hne⟩
      refine ⟨r1, { s1 with locals := s1.locals.resVarEq (v, s.locals.lookup v) }, ?_, ?_, ?_⟩
      · simp only [transformEocHOLExact]
        rw [evalCrepSemHOLProgExact_dec_holShape, hval]
        dsimp only
        simp only [su] at hev1
        rw [hev1]
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hrel1
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      · unfold transformEocPost at hpost1 ⊢
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

/-- Local support: the `If` case, from the motive for both branches. -/
private theorem iteGoal {width : Nat} [NeZero width] {σ : Type}
    (c : CrepExpHOL width) (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ v1 w, crepExactEvalExpClassical s c = some v1 → v1 = .word w →
      transformEocGoal (if w ≠ 0 then c1 else c2) s) :
    transformEocGoal (.ite c c1 c2) s := by
  intro r s' res rts ⟨hev, hue, hnb, hlen, hfresh, hz, hnd, hne⟩
  rcases hu1 : unreachElimHOLExact c1 with ⟨c1', x1⟩
  rcases hu2 : unreachElimHOLExact c2 with ⟨c2', x2⟩
  simp only [unreachElimHOLExact, hu1, hu2, Prod.mk.injEq, CrepProgHOL.ite.injEq] at hue
  obtain ⟨⟨_, rfl, rfl⟩, _⟩ := hue
  simp only [notBranchRetHOLExact, Bool.and_eq_true, Bool.not_eq_true'] at hnb
  have hnb1 := CrepInlineUnreachElim.notHasReturnImpNotBranchRet c1' (by simp [hnb.1])
  have hnb2 := CrepInlineUnreachElim.notHasReturnImpNotBranchRet c2' (by simp [hnb.2])
  have hf1 : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c1' := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  have hf2 : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c2' := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  rw [evalCrepSemHOLProgExact_ite] at hev
  simp only [transformEocHOLExact]
  rw [evalCrepSemHOLProgExact_ite]
  split at hev
  · rename_i w hcond
    have hcl : crepExactEvalExpClassical s c = some (.word w) := by
      simpa only [crepExactEvalExpClassical_eq, crepExactEvalExp_eq_eval] using hcond
    have hsel := ih (.word w) w hcl rfl
    by_cases hw : w ≠ 0
    · rw [if_pos hw] at hev hsel ⊢
      exact hsel r s' x1 rts ⟨hev, hu1, hnb1, hlen, hf1, hz, hnd, hne⟩
    · rw [if_neg hw] at hev hsel ⊢
      exact hsel r s' x2 rts ⟨hev, hu2, hnb2, hlen, hf2, hz, hnd, hne⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact absurd rfl hne

/-- Local support: the `Seq` case, from the motive for both components. -/
private theorem seqGoal {width : Nat} [NeZero width] {σ : Type}
    (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih2 : ∀ res s1, (res, s1) = evalCrepSemHOLProgExact s c1 → res = none →
      transformEocGoal c2 s1)
    (ih1 : transformEocGoal c1 s) :
    transformEocGoal (.seq c1 c2) s := by
  intro r s' res rts ⟨hev, hue, hnb, hlen, hfresh, ⟨z, hz⟩, hnd, hne⟩
  rcases hu1 : unreachElimHOLExact c1 with ⟨c1', x1⟩
  simp only [unreachElimHOLExact, hu1] at hue
  by_cases hx1 : x1.isSome
  · simp only [hx1, if_true, Prod.mk.injEq] at hue
    have hsz := CrepInlineUnreachElimProgSize.unreachElimProgSize c1 c1' x1 (fun n : Nat => n) hu1
    rw [hue.1] at hsz
    simp only [CrepLangGeneratedSize.crepProgSizeHOL] at hsz
    omega
  · simp only [hx1, if_false, Bool.false_eq_true] at hue
    rcases hu2 : unreachElimHOLExact c2 with ⟨c2', x2⟩
    simp only [hu2, Prod.mk.injEq, CrepProgHOL.seq.injEq] at hue
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hue
    have hx1n : x1 = none := by cases x1 <;> simp_all
    subst hx1n
    simp only [notBranchRetHOLExact, Bool.and_eq_true] at hnb
    have hf1 : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c1' := fun x hx hm =>
      hfresh x hx (by simp [crepVarProgHOLExact, hm])
    have hf2 : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c2' := fun x hx hm =>
      hfresh x hx (by simp [crepVarProgHOLExact, hm])
    rw [evalCrepSemHOLProgExact_seq_fixClockFree] at hev
    simp only [transformEocHOLExact]
    rw [evalCrepSemHOLProgExact_seq_fixClockFree]
    rcases hstep : evalCrepSemHOLProgExact s c1' with ⟨r0, s1⟩
    rw [hstep] at hev
    have hnoret : ∀ vs, r0 ≠ some (.return vs) :=
      CrepInlineNotBranchReturn.notBranchRetEvaluateReturnUnreachElim c1' s r0 s1
        ⟨hu1, hnb.1, hstep⟩
    cases r0 with
    | none =>
        obtain ⟨ra, sa, heva, hrela, hposta⟩ := ih1 none s1 none rts
          ⟨hstep, hu1, hnb.1, fun _ h => absurd h (by simp), hf1, ⟨z, hz⟩, hnd, by simp⟩
        unfold transformEocPost at hposta
        obtain ⟨rfl, hl⟩ := hposta
        have hsa := eq_of_stateRel_localsStrongRel hrela hl
        subst hsa
        rw [heva]
        have hdom := evaluateLocalsSameFdom'Exact c1' s none s1 ⟨hstep, Or.inl rfl⟩
        obtain ⟨z1, hz1⟩ := mapM_some_of_fdom_eq hdom rts z hz
        exact ih2 none s1 hstep.symm rfl r s' x2 rts ⟨hev, hu2, hnb.2, hlen, hf2, ⟨z1, hz1⟩, hnd, hne⟩
    | some x =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
        obtain ⟨ra, sa, heva, hrela, hposta⟩ := ih1 (some x) s1 none rts
          ⟨hstep, hu1, hnb.1, fun vs h => absurd h (hnoret vs), hf1, ⟨z, hz⟩, hnd, hne⟩
        rw [heva]
        unfold transformEocPost at hposta ⊢
        rcases x with _ | _ | n | n | vs | ex | ev
        · exact absurd rfl hne
        · subst hposta; exact ⟨_, _, rfl, hrela, rfl⟩
        · obtain ⟨rfl, hl⟩ := hposta; exact ⟨_, _, rfl, hrela, rfl, hl⟩
        · obtain ⟨rfl, hl⟩ := hposta; exact ⟨_, _, rfl, hrela, rfl, hl⟩
        · exact absurd rfl (hnoret vs)
        · subst hposta; exact ⟨_, _, rfl, hrela, rfl⟩
        · subst hposta; exact ⟨_, _, rfl, hrela, rfl⟩

/-! ## Tagged cases (HOL goal for each constructor; IHs only for sub-programs) -/

/-- Programs left unchanged by `transform_eoc` (the final `rw` of HOL's proof:
    Skip, Assign, Primitive, Store, Store32, StoreByte, StoreGlob, Break,
    Continue, Raise, Tick, ExtCall, ShMem); no sub-program IH. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_eoc_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformEocCorrect_Leaf {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (hp : p = .skip ∨ (∃ n e, p = .assign n e) ∨ (∃ ns op args, p = .primitive ns op args) ∨
      (∃ a b, p = .store a b) ∨ (∃ a b, p = .store32 a b) ∨ (∃ a b, p = .storeByte a b) ∨
      (∃ a b, p = .storeGlob a b) ∨ (∃ n, p = .break n) ∨ (∃ n, p = .continue n) ∨
      (∃ e, p = .raise e) ∨ p = .tick ∨
      (∃ f a b c d, p = .extCall f a b c d) ∨ (∃ op n a, p = .shMem op n a)) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (res : Option CrepEarlyExitHOL) (rts : List Nat),
      evalCrepSemHOLProgExact s (p) = (r, s') ∧
        unreachElimHOLExact (p) = ((p), res) ∧
        notBranchRetHOLExact (p) = true ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (p)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformEocHOLExact rts (p)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r := by
  have hleaf : (∀ rts, transformEocHOLExact rts p = p) ∧ hasReturnHOLExact p = false := by
    rcases hp with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ |
      ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl | ⟨_, _, _, _, _, rfl⟩ |
      ⟨_, _, _, rfl⟩ <;> exact ⟨fun _ => by simp [transformEocHOLExact], by simp [hasReturnHOLExact]⟩
  exact leafGoal p s hleaf.1 hleaf.2

/-- `Return` case (HOL: `imp_res_tac evaluate_nested_seq_assign`); no IH. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_eoc_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformEocCorrect_Return {width : Nat} [NeZero width] {σ : Type}
    (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (res : Option CrepEarlyExitHOL) (rts : List Nat),
      evalCrepSemHOLProgExact s (.return es) = (r, s') ∧
        unreachElimHOLExact (.return es) = ((.return es), res) ∧
        notBranchRetHOLExact (.return es) = true ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.return es)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformEocHOLExact rts (.return es)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  returnGoal es s

/-- `Dec` case, with HOL `evaluate_ind`'s guarded body premise
    (`eval s e = SOME value ⇒ P (prog, set_var v value s)`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_eoc_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformEocCorrect_Dec {width : Nat} [NeZero width] {σ : Type}
    (v : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ value, crepExactEvalExpClassical s e = some value →
      transformEocGoal body (CrepSemHOLState.setVar v value s)) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (res : Option CrepEarlyExitHOL) (rts : List Nat),
      evalCrepSemHOLProgExact s (.dec v e body) = (r, s') ∧
        unreachElimHOLExact (.dec v e body) = ((.dec v e body), res) ∧
        notBranchRetHOLExact (.dec v e body) = true ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.dec v e body)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformEocHOLExact rts (.dec v e body)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  decGoal v e body s ih

/-- `If` case, with HOL `evaluate_ind`'s guarded premise for the selected
    branch (`eval s e = SOME v1 ∧ v1 = Word w ⇒ P (if w ≠ 0w then c1 else c2, s)`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_eoc_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformEocCorrect_If {width : Nat} [NeZero width] {σ : Type}
    (c : CrepExpHOL width) (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : ∀ v1 w, crepExactEvalExpClassical s c = some v1 → v1 = .word w →
      transformEocGoal (if w ≠ 0 then c1 else c2) s) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (res : Option CrepEarlyExitHOL) (rts : List Nat),
      evalCrepSemHOLProgExact s (.ite c c1 c2) = (r, s') ∧
        unreachElimHOLExact (.ite c c1 c2) = ((.ite c c1 c2), res) ∧
        notBranchRetHOLExact (.ite c c1 c2) = true ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.ite c c1 c2)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformEocHOLExact rts (.ite c c1 c2)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  iteGoal c c1 c2 s ih

/-- `Seq` case, with HOL `evaluate_ind`'s premises
    (`(res,s1) = evaluate (c1,s) ∧ res = NONE ⇒ P (c2,s1)` and `P (c1,s)`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_eoc_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformEocCorrect_Seq {width : Nat} [NeZero width] {σ : Type}
    (c1 c2 : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih2 : ∀ res s1, (res, s1) = evalCrepSemHOLProgExact s c1 → res = none →
      transformEocGoal c2 s1)
    (ih1 : transformEocGoal c1 s) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (res : Option CrepEarlyExitHOL) (rts : List Nat),
      evalCrepSemHOLProgExact s (.seq c1 c2) = (r, s') ∧
        unreachElimHOLExact (.seq c1 c2) = ((.seq c1 c2), res) ∧
        notBranchRetHOLExact (.seq c1 c2) = true ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.seq c1 c2)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformEocHOLExact rts (.seq c1 c2)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  seqGoal c1 c2 s ih2 ih1

end CrepInlineTransformEoc

end Flapjack
