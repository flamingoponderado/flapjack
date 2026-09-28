import Flapjack.Pancake.Proofs.LoopLive.CompileCorrect

/-!
# loop_live `mark_correct` / `comp_correct`

Exact ports of `cakeml/pancake/proofs/loop_liveProofScript.sml`'s `mark_correct`
(860) and `comp_correct` (931) over the exact `LoopSemStateFiniteExact.evaluate`
and the tagged `markAllHOL` (`mark_all_def`) / `compHOL` (`comp_def`)
(beads `flapjack-pxn.18.5.8.2.1`, `.2.2`).  `optimise_correct` (955) waits for
`loop_callProof`'s `compile_correct` (bead `flapjack-pxn.18.5.7`).
-/

namespace Flapjack

open LoopSemStateFiniteExact

/-- Flapjack helper (no HOL declaration): the equational form of HOL's
    `mark_correct`, proved by the lexicographic `(clock, program size)` induction
    mirroring `loopSemTheory.evaluate_ind` (HOL's `recInduct evaluate_ind` with its
    `Seq`/`If`/`Loop`/`Call` resumes). -/
private theorem markAll_evaluate_eq {width : Nat} [NeZero width] {F : Type} :
    ∀ (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      evaluate (markAllHOL prog).1 s = evaluate prog s := by
  have key : ∀ (x : Nat × Nat) (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock, sizeOf prog) = x → evaluate (markAllHOL prog).1 s = evaluate prog s := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro prog s hx
      have ih : ∀ (p' : HolLoopProg width) (t' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (t'.clock, sizeOf p') (s.clock, sizeOf prog) →
          evaluate (markAllHOL p').1 t' = evaluate p' t' :=
        fun p' t' hlt => ih0 _ (hx ▸ hlt) p' t' rfl
      clear ih0 hx
      have ihc : ∀ (p' : HolLoopProg width) (t' : LoopSemStateFiniteExact width F),
          t'.clock < s.clock → evaluate (markAllHOL p').1 t' = evaluate p' t' :=
        fun p' t' h => ih p' t' (Prod.Lex.left _ _ h)
      have ihle : ∀ (p' : HolLoopProg width) (t' : LoopSemStateFiniteExact width F),
          t'.clock ≤ s.clock → sizeOf p' < sizeOf prog →
          evaluate (markAllHOL p').1 t' = evaluate p' t' := fun p' t' h hs => by
        rcases Nat.lt_or_eq_of_le h with h | h
        · exact ihc p' t' h
        · exact ih p' t' (by rw [h]; exact Prod.Lex.right _ hs)
      have hmark : ∀ (p : HolLoopProg width) (t : LoopSemStateFiniteExact width F),
          evaluate (.mark p) t = evaluate p t := fun p t => by rw [evaluate]
      cases prog with
      | seq c1 c2 =>
        have hseq : evaluate (.seq (markAllHOL c1).1 (markAllHOL c2).1) s = evaluate (.seq c1 c2) s := by
          rw [evaluate_seq, evaluate_seq, ihle c1 s (Nat.le_refl _) (by simp <;> omega)]
          rcases h1 : evaluate c1 s with ⟨r, s1⟩
          cases r with
          | none =>
            simp only
            have hle := evaluate_clock_snd c1 s
            rw [h1] at hle
            exact ihle c2 s1 hle (by simp <;> omega)
          | some _ => rfl
        simp only [markAllHOL]
        split
        · rw [hmark]; exact hseq
        · exact hseq
      | loop liveIn body liveOut =>
        simp only [markAllHOL]
        rw [evaluate, evaluate]
        rcases hc : cutRes liveIn (none, s) with ⟨r0, s1⟩
        cases r0 with
        | some _ => rfl
        | none =>
          simp only
          have hs1 := cutRes_none_clock hc
          rw [fix_clock_evaluate, fix_clock_evaluate, ihc body s1 hs1]
          rcases hb : evaluate body s1 with ⟨rb, s2⟩
          have hs2 : s2.clock < s.clock := by
            have := evaluate_clock_snd body s1
            rw [hb] at this; simp only at this; omega
          have hL : evaluate (.loop liveIn (markAllHOL body).1 liveOut) s2 =
              evaluate (.loop liveIn body liveOut) s2 := by
            have := ihc (.loop liveIn body liveOut) s2 hs2
            simpa [markAllHOL] using this
          rcases rb with _ | r
          · exact hL
          · cases r with
            | «continue» n => cases n with
              | zero => exact hL
              | succ n => rfl
            | «break» n => cases n <;> rfl
            | _ => rfl
      | ite cmp r1 ri c1 c2 live =>
        have hite : evaluate (.ite cmp r1 ri (markAllHOL c1).1 (markAllHOL c2).1 live) s =
            evaluate (.ite cmp r1 ri c1 c2 live) s := by
          rw [evaluate, evaluate, ihle c1 s (Nat.le_refl _) (by simp <;> omega),
            ihle c2 s (Nat.le_refl _) (by simp <;> omega)]
        simp only [markAllHOL]
        split
        · rw [hmark]; exact hite
        · exact hite
      | mark body =>
        simp only [markAllHOL]
        rw [ihle body s (Nat.le_refl _) (by simp)]
        rw [evaluate]
      | call ret dest args handler =>
        cases handler with
        | none => simp only [markAllHOL]; rw [evaluate]
        | some hd =>
          obtain ⟨e, h, r, lo⟩ := hd
          have hP : evaluate (.call ret dest args (some (e, (markAllHOL h).1, (markAllHOL r).1, lo))) s =
              evaluate (.call ret dest args (some (e, h, r, lo))) s := by
            rw [evaluate, evaluate]
            cases hg : LoopSemStateFiniteExact.getVars args s with
            | none => rfl
            | some av =>
            simp only
            cases hfc : LoopSemStateFiniteExact.findCode dest av s.code with
            | none => rfl
            | some ep =>
            obtain ⟨env, pr⟩ := ep
            simp only
            cases ret with
            | none => rfl
            | some rl =>
            obtain ⟨ns, live⟩ := rl
            simp only
            by_cases hnd' : ¬ ns.Nodup
            · simp [hnd']
            have hnd : ns.Nodup := Classical.not_not.mp hnd'
            simp only [hnd, not_true_eq_false, if_false]
            rcases hc : cutRes live (none, s) with ⟨r0, s1⟩
            cases r0 with
            | some _ => rfl
            | none =>
              simp only
              have hs1 := cutRes_none_clock hc
              rw [fix_clock_evaluate]
              rcases hcal : evaluate pr { s1 with locals := env } with ⟨rc, st⟩
              have hst : st.clock < s.clock := by
                have := evaluate_clock_snd pr { s1 with locals := env }
                rw [hcal] at this; simp only at this; omega
              rcases rc with _ | rv
              · rfl
              · cases rv with
                | result retvs =>
                  simp only
                  split
                  · rfl
                  · rw [ihc r _ (by simp [LoopSemStateFiniteExact.setVars]; exact hst)]
                | exception w =>
                  simp only
                  rw [ihc h _ (by simp [LoopSemStateFiniteExact.setVar]; exact hst)]
                | _ => rfl
          simp only [markAllHOL]
          split
          · rw [hmark]; exact hP
          · exact hP
      | _ => simp [markAllHOL, evaluate]
  exact fun prog s => key _ prog s rfl

/-- Exact HOL `mark_correct` (`loop_liveProofScript.sml:860-862`):
    `∀prog s res s1. evaluate (prog,s) = (res,s1) ⇒
      evaluate (FST (mark_all prog),s) = (res,s1)`. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "mark_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem mark_correct {width : Nat} [NeZero width] {F : Type} :
    ∀ (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F),
      evaluate prog s = (res, s1) → evaluate (markAllHOL prog).1 s = (res, s1) :=
  fun prog s _ _ h => (markAll_evaluate_eq prog s).trans h

/-- Exact HOL `comp_correct` (`loop_liveProofScript.sml:931-937`):
    `evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧ (∀n. res ≠ SOME (Break n)) ∧
      (∀n. res ≠ SOME (Continue n)) ∧ res ≠ NONE ⇒ evaluate (comp prog,s) = (res,s1)`,
    its free variables `prog s res s1` universally quantified in order of
    occurrence. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "comp_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem comp_correct {width : Nat} [NeZero width] {F : Type} :
    ∀ (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F),
      evaluate prog s = (res, s1) ∧ res ≠ some .error ∧ (∀ n, res ≠ some (.break n)) ∧
        (∀ n, res ≠ some (.continue n)) ∧ res ≠ none →
      evaluate (compHOL prog) s = (res, s1) := by
  intro prog s res s1 ⟨he, hne, hnb, hnc, hnn⟩
  rcases hs : shrinkHOL [] prog .ln with ⟨p', l1'⟩
  have hsub : sptSubspt (sptInter s.locals l1') s.locals := by
    intro k hk
    cases hl : (sptLookup k l1').isSome with
    | false =>
      simp [sptMem, sptDomain, sptLookup_sptInter, hl] at hk
    | true =>
      have hk' : sptMem k s.locals := by
        simpa [sptMem, sptDomain, sptLookup_sptInter, hl] using hk
      exact ⟨hk', by rw [sptLookup_sptInter, if_pos hl]⟩
  obtain ⟨nl, hn, hp⟩ := loopLive_compile_correct prog s res s1 [] s.locals p' l1' .ln
    ⟨he, hne, hs, hsub⟩
  have hnl : nl = s1.locals := by
    rcases res with _ | r
    · exact absurd rfl hnn
    · cases r with
      | «break» n => exact absurd rfl (hnb n)
      | «continue» n => exact absurd rfl (hnc n)
      | error => exact absurd rfl hne
      | _ => exact hp
  subst hnl
  have hn' : evaluate p' s = (res, s1) := hn
  simp only [compHOL, hs]
  exact mark_correct p' s res s1 hn'

end Flapjack
