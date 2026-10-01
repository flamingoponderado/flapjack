import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Move

/-!
# `evaluate_remove_dead` Call cases

The `Call NONE` and `Call (SOME _)` cases of `word_allocProofScript.sml:3900-4472`
`evaluate_remove_dead` (Resume blocks 4268 and 4212). `remove_dead` resets the
dead-store list to `[]` at a call, so both stores coincide; the callee runs from
`call_env`, which discards the caller's locals, so source and target agree from
the call onwards and the returning call's handlers are related by their
induction hypotheses with reflexive relations.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateRemoveDeadCallWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateRemoveDeadCallWitnesses

/-- The `evaluate_remove_dead` post-condition holds between a state and itself
(Flapjack infrastructure). -/
theorem removeDeadPostRefl {width : Nat} [NeZero width] {C F : Type} (live : NumSet)
    (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet)) (res : Option (WordSemResult width))
    (rst : WordSemStateFiniteExact width C F) :
    removeDeadPost live nlive lt res rst rst.locals rst.store := by
  cases res with
  | none => exact ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _⟩
  | some r =>
    cases r <;> first
      | exact ⟨rfl, rfl⟩
      | exact ⟨rfl, by split <;> first | trivial | exact strongLocalsRelIdRefl _ _⟩

/-- HOL `evaluate_remove_dead`, `Call NONE` case (Resume 4268). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_CallNone {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    removeDeadGoal C F (.call none dest args h : WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [removeDead] at hrd
  simp only [getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hst
  rw [evaluate] at hev
  split at hev
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · rename_i xs hgv
    have hgvT : WordSemStateFiniteExact.getVars args ({ st with locals := t, store := st.store } :
        WordSemStateFiniteExact width C F) = some xs :=
      (getVarsLocalsEq { st with locals := t, store := st.store } { st with locals := t } rfl _).trans
        (strongLocalsRelIGetVars' args _ st t xs
          ⟨fun x hx => (sptDomain_numsetIns _ _ _).mpr (Or.inr hx), hl, hgv⟩)
    rw [evaluate, hgvT]
    simp only at hev ⊢
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · rename_i hbad
      rw [if_neg hbad]
      split at hev
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      · rename_i args1 prog ss hfc
        split at hev
        · split at hev
          · rename_i hc
            rw [dif_pos hc]
            simp only [Prod.mk.injEq] at hev
            obtain ⟨rfl, rfl⟩ := hev
            exact ⟨_, _, rfl, removeDeadPostRefl _ _ _ _ _⟩
          · rename_i hc
            rw [dif_neg hc]
            refine ⟨rst.locals, rst.store, ?_, removeDeadPostRefl _ _ _ _ _⟩
            exact hev
        · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr

/-- `push_env` carries the caller locals unchanged (Flapjack infrastructure). -/
theorem pushEnvNoneWithLocals {width : Nat} [NeZero width] {C F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (s : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width)) :
    pushEnv envs none { s with locals := t } = { pushEnv envs none s with locals := t } := rfl

/-- `push_env` with a handler carries the caller locals unchanged (Flapjack
infrastructure). -/
theorem pushEnvSomeWithLocals {width : Nat} [NeZero width] {C F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (hn : Nat)
    (p : WordLangProgHOL (BitVec width)) (a b : Nat)
    (s : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width)) :
    pushEnv envs (some (hn, p, a, b)) { s with locals := t } =
      { pushEnv envs (some (hn, p, a, b)) s with locals := t } := rfl

/-- `dec_clock` commutes with a locals overwrite (Flapjack infrastructure). -/
theorem decClockWithLocals {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width)) :
    decClock { s with locals := t } = { decClock s with locals := t } := rfl

/-- `call_env` discards the caller locals (Flapjack infrastructure). -/
theorem callEnvWithLocals {width : Nat} [NeZero width] {C F : Type}
    (args : List (WordLocW width)) (size : Option Nat)
    (s : WordSemStateFiniteExact width C F) (t : Spt (WordLocW width)) :
    WordSemStateFiniteExact.callEnv args size { s with locals := t } =
      WordSemStateFiniteExact.callEnv args size s := rfl

/-- `push_env` ignores the handler program (Flapjack infrastructure; HOL's
`push_env_def` case split in the CallSome case). -/
theorem pushEnvRemoveDead {width : Nat} [NeZero width] {C F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (hn : Nat)
    (hp : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
    (lt : List (NumSet × NumSet)) (a b : Nat) (s : WordSemStateFiniteExact width C F) :
    pushEnv envs (some (hn, (removeDead hp live nlive lt).1, a, b)) s =
      pushEnv envs (some (hn, hp, a, b)) s := rfl

/-- HOL `evaluate_remove_dead`, `Call (SOME _)` case (Resume 4212), with induction
hypotheses for the return handler and the exception handler program. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_remove_dead"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateRemoveDead_CallSome {width : Nat} [NeZero width] {C F : Type}
    (n : List Nat) (names : WordLangCutsetsHOL) (retH : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (ihRet : removeDeadGoal C F retH)
    (ihH : ∀ hn hp a b, h = some (hn, hp, a, b) → removeDeadGoal C F hp) :
    removeDeadGoal C F (.call (some (n, names, retH, l1, l2)) dest args h :
      WordLangProgHOL (BitVec width)) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  rw [removeDead.eq_def] at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hst
  unfold flatExpConventions at hflat
  simp only [Bool.and_eq_true] at hflat
  obtain ⟨hfRet, hfH⟩ := hflat
  rcases hrr : removeDead retH live nlive lt with ⟨retH', lr, nr⟩
  rw [evaluate] at hev
  split at hev
  · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  rename_i xs hgv
  have hgvT : WordSemStateFiniteExact.getVars args ({ st with locals := t, store := st.store } :
      WordSemStateFiniteExact width C F) = some xs :=
    (getVarsLocalsEq { st with locals := t, store := st.store } { st with locals := t } rfl _).trans
      (strongLocalsRelIGetVars' args _ st t xs
        ⟨fun x hx => by
          rw [sptDomain_sptUnion]
          exact Or.inr ((sptDomain_numsetIns _ _ _).mpr (Or.inr hx)), hl, hgv⟩)
  rw [evaluate, hgvT]
  rcases h with _ | ⟨hn, hp, a, b⟩
  all_goals simp only [decClockWithLocals, pushEnvNoneWithLocals, pushEnvSomeWithLocals,
    callEnvWithLocals]
  case none =>
    simp only at hev ⊢
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    rename_i hbad
    rw [if_neg hbad]
    have har : wordSemAddRetLoc (some (n, names, retH', l1, l2)) xs =
        wordSemAddRetLoc (some (n, names, retH, l1, l2)) xs := rfl
    rw [har]
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    rename_i args1 prog ss hfc
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    rename_i hnd
    rw [if_neg hnd]
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    rename_i envs hce
    have hceT : wordSemCutEnvs names t = some envs :=
      strongLocalsRelICutEnvs names st t envs ⟨fun k v ⟨hk, hv⟩ => hl k v ⟨by
        rw [sptDomain_sptUnion, sptDomain_sptUnion]; exact Or.inl hk, hv⟩, hce⟩
    rw [hceT]
    simp only
    split at hev
    · rename_i hc
      rw [dif_pos hc]
      simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact ⟨_, _, rfl, removeDeadPostRefl _ _ _ _ _⟩
    rename_i hc
    rw [dif_neg hc]
    split at hev
    · rename_i x ys s2 hcall
      split at hev
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      rename_i hxy
      rw [if_neg hxy]
      split at hev
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      rename_i s1 hpop
      split at hev
      · rename_i hdom
        rw [if_pos hdom]
        exact ihRet live nlive lt retH' lr nr (setVars n ys s1) (setVars n ys s1).locals
          (setVars n ys s1).store res rst
          ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _, hev, hfRet, hrr, herr⟩
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact ⟨_, _, rfl, removeDeadPostRefl _ _ _ _ _⟩
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · exact ⟨rst.locals, rst.store, hev, removeDeadPostRefl _ _ _ _ _⟩
  case some =>
    simp only at hev ⊢
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    rename_i hbad
    rw [if_neg hbad]
    have har : wordSemAddRetLoc (some (n, names, retH', l1, l2)) xs =
        wordSemAddRetLoc (some (n, names, retH, l1, l2)) xs := rfl
    rw [har]
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    rename_i args1 prog ss hfc
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    rename_i hnd
    rw [if_neg hnd]
    split at hev
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    rename_i envs hce
    have hceT : wordSemCutEnvs names t = some envs :=
      strongLocalsRelICutEnvs names st t envs ⟨fun k v ⟨hk, hv⟩ => hl k v ⟨by
        rw [sptDomain_sptUnion, sptDomain_sptUnion]; exact Or.inl hk, hv⟩, hce⟩
    rw [hceT]
    simp only
    simp only [pushEnvRemoveDead]
    split at hev
    · rename_i hc
      rw [dif_pos hc]
      simp only [Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact ⟨_, _, rfl, removeDeadPostRefl _ _ _ _ _⟩
    rename_i hc
    rw [dif_neg hc]
    split at hev
    · rename_i x ys s2 hcall
      split at hev
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      rename_i hxy
      rw [if_neg hxy]
      split at hev
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      rename_i s1 hpop
      split at hev
      · rename_i hdom
        rw [if_pos hdom]
        exact ihRet live nlive lt retH' lr nr (setVars n ys s1) (setVars n ys s1).locals
          (setVars n ys s1).store res rst
          ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _, hev, hfRet, hrr, herr⟩
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · rename_i x y s2 hcall
      split at hev
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
      rename_i hxy
      rw [if_neg hxy]
      split at hev
      · rename_i hdom
        rw [if_pos hdom]
        rcases hrh : removeDead hp live nlive lt with ⟨hp', lh, nh⟩
        exact ihH hn hp a b rfl live nlive lt hp' lh nh (setVar hn y s2) (setVar hn y s2).locals
          (setVar hn y s2).store res rst
          ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _, hev, by simpa using hfH, hrh, herr⟩
      · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    · exact ⟨rst.locals, rst.store, hev, removeDeadPostRefl _ _ _ _ _⟩


end Flapjack.WordAlloc
