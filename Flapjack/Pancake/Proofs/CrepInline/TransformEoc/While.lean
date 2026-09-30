import Flapjack.Pancake.Proofs.CrepInline.TransformEoc.Cases

/-!
# crep_inline `transform_eoc_correct`: the `While` case

`Resume transform_eoc_correct[While]` (`cakeml/pancake/proofs/crep_inlineProofScript.sml:1979-2022`,
bead `flapjack-pxn.18.5.5.47.2.2`).  The induction hypotheses are the three
guarded recursive premises of HOL `evaluate_ind`'s While conjunct (body at the
decremented clock; loop re-entry after `NONE` and after `Continue 0`),
specialized to the motive `transformEocGoal`, exactly as `WhileDomainIH` does
for `evaluate_locals_same_fdom`.
-/

namespace Flapjack

namespace CrepInlineTransformEoc

open HolFiniteMapExact
open CrepInlineExact

namespace WhileWitness
/-- Same-module canonical witness for the finite-map qualifier on the
`CrepSemHOLState` fields `locals`, `globals` and `code`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness
end WhileWitness

/-- The three guarded recursion premises of the exact HOL `evaluate_ind`
While case, specialized to `transformEocGoal`.  Infrastructure recording
which recursive evaluations are justified; not a HOL theorem port. -/
structure TransformEocWhileIH {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width)
    (s : CrepSemHOLState width σ) : Prop where
  continueCase : ∀ v2 w res s1 v1 v8,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
    res = some v1 → v1 = .continue v8 → v8 = 0 → transformEocGoal (.while e c) s1
  normalCase : ∀ v2 w res s1,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    (res, s1) = evalCrepSemHOLProgExact (decClockCrepSemHOL s) c →
    res = none → transformEocGoal (.while e c) s1
  bodyCase : ∀ v2 w,
    crepExactEvalExpClassical s e = some v2 → v2 = .word w → w ≠ 0 → s.clock ≠ 0 →
    transformEocGoal c (decClockCrepSemHOL s)

/-- Local support: the `While` case of the motive. -/
private theorem whileGoal {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : TransformEocWhileIH e c s) :
    transformEocGoal (.while e c) s := by
  intro r s' res rts ⟨hev, hue, hnb, hlen, hfresh, ⟨z, hz⟩, hnd, hne⟩
  rcases huc : unreachElimHOLExact c with ⟨c', xc⟩
  simp only [unreachElimHOLExact, huc, Prod.mk.injEq, CrepProgHOL.while.injEq] at hue
  obtain ⟨⟨_, rfl⟩, rfl⟩ := hue
  simp only [notBranchRetHOLExact, Bool.not_eq_true'] at hnb
  have hnbc := CrepInlineUnreachElim.notHasReturnImpNotBranchRet c' (by simp [hnb])
  have hueW : unreachElimHOLExact (.while e c') = (.while e c', none) := by
    simp [unreachElimHOLExact, huc]
  have hnbW : notBranchRetHOLExact (.while e c') = true := by
    simp [notBranchRetHOLExact, hnb]
  have hfc : ∀ x, x ∈ rts → x ∉ crepVarProgHOLExact c' := fun x hx hm =>
    hfresh x hx (by simp [crepVarProgHOLExact, hm])
  have hstate : crepInlineStateRelExact s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp only [transformEocHOLExact]
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
        exact ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      · rw [if_neg hc] at hev ⊢
        rcases hb : evalCrepSemHOLProgExact (decClockCrepSemHOL s) c' with ⟨r0, s1⟩
        rw [hb] at hev
        dsimp only at hev
        obtain ⟨r00, s00, hb0, hm0⟩ :=
          CrepInlineNoReturn.notHasReturnNotEvaluateReturn c' (decClockCrepSemHOL s)
            (by simpa using hnb)
        rw [hb] at hb0
        obtain ⟨hr0, _⟩ := Prod.mk.inj hb0
        subst hr0
        have hne0 : r0 ≠ some .error := by
          rintro rfl
          simp only [exitLoopCrepResult] at hev
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
          exact hne rfl
        obtain ⟨ra, sa, heva, hrela, hposta⟩ :=
          ih.bodyCase (.word w) w hclass rfl hw hc r0 s1 xc rts
            ⟨hb, huc, hnbc, fun vs h => by subst h; exact hm0.elim, hfc, ⟨z, hz⟩, hnd, hne0⟩
        rw [heva]
        dsimp only
        have hdom : ∀ n, (r0 = none ∨ r0 = some (.continue n)) →
            ∃ z1, rts.mapM s1.locals.lookup = some z1 := by
          intro n hr
          have hd := evaluateLocalsSameFdom'Exact c' (decClockCrepSemHOL s) r0 s1
            ⟨hb, by rcases hr with rfl | rfl <;> simp⟩
          exact mapM_some_of_fdom_eq hd rts z hz
        unfold transformEocPost at hposta
        rcases r0 with _ | ⟨_ | _ | n | n | vs | ex | ev⟩
        · obtain ⟨rfl, hl⟩ := hposta
          have hsa := eq_of_stateRel_localsStrongRel hrela hl
          subst hsa
          have hloop := ih.normalCase (.word w) w none s1 hclass rfl hw hc hb.symm rfl r s' none rts
            ⟨hev, hueW, hnbW, hlen, hfresh, hdom 0 (Or.inl rfl), hnd, hne⟩
          simpa only [transformEocHOLExact] using hloop
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
                rfl r s' none rts ⟨hev, hueW, hnbW, hlen, hfresh, hdom 0 (Or.inr rfl), hnd, hne⟩
              simpa only [transformEocHOLExact] using hloop
          | succ n =>
              simp only [exitLoopCrepResult] at hev ⊢
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
              exact ⟨_, _, rfl, hrela, rfl, hl⟩
        · exact hm0.elim
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
      exact ⟨_, _, rfl, hstate, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    exact absurd rfl hne

/-- `While` case of HOL `transform_eoc_correct` (Resume at `:1979-2022`), with
    exactly the guarded `evaluate_ind` While premises as IHs. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "transform_eoc_correct"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem transformEocCorrect_While {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (c : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (ih : TransformEocWhileIH e c s) :
    ∀ (r : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
      (res : Option CrepEarlyExitHOL) (rts : List Nat),
      evalCrepSemHOLProgExact s (.while e c) = (r, s') ∧
        unreachElimHOLExact (.while e c) = ((.while e c), res) ∧
        notBranchRetHOLExact (.while e c) = true ∧
        (∀ retvs, r = some (.return retvs) → rts.length = retvs.length) ∧
        (∀ x, x ∈ rts → x ∉ crepVarProgHOLExact (.while e c)) ∧
        (∃ z, rts.mapM s.locals.lookup = some z) ∧
        rts.Nodup ∧
        r ≠ some .error →
      ∃ r1 s1', evalCrepSemHOLProgExact s (transformEocHOLExact rts (.while e c)) = (r1, s1') ∧
        crepInlineStateRelExact s' s1' ∧
        match r with
        | none => r1 = none ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.break n) => r1 = some (.break n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.continue n) => r1 = some (.continue n) ∧ crepInlineLocalsStrongRelExact s' s1'
        | some (.return retvs) => r1 = none ∧ rts.mapM s1'.locals.lookup = some retvs
        | some .error => False
        | _ => r1 = r :=
  whileGoal e c s ih

end CrepInlineTransformEoc

end Flapjack
