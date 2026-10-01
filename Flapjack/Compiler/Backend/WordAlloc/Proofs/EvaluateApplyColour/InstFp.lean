import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace InstFpWitnesses

/-- Imported canonical finite-map carrier roundtrip. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end InstFpWitnesses

/-- Local FP-map update frame; Flapjack proof infrastructure. -/
private theorem wsrSetFp {width : Nat} [NeZero width] {C F : Type}
    {s t : WordSemStateFiniteExact width C F} (n : Nat) (v : BitVec 64)
    (h : wordStateEqRel s t) : wordStateEqRel (setFpVar n v s) (setFpVar n v t) := by
  simp_all [wordStateEqRel, setFpVar]

/-- Flapjack proof infrastructure for the source's ordered two-register
updates. Injectivity is scoped to the two writes and final live set; aliases
are allowed. This is not a separate HOL declaration. -/
private theorem twoFpWritesLocals {α : Type} (f : Nat → Nat) (a b : Nat)
    (live : Nat → Prop) (source target : Spt α) (x y : α)
    (hinj : ∀ k l, (k = a ∨ k = b ∨ live k) →
      (l = a ∨ l = b ∨ live l) → f k = f l → k = l)
    (hrel : strongLocalsRel f (fun k => live k ∧ k ≠ a ∧ k ≠ b) source target) :
    strongLocalsRel f live (sptInsert b y (sptInsert a x source))
      (sptInsert (f b) y (sptInsert (f a) x target)) := by
  apply strongLocalsRelInsert f b live _ _ y
  constructor
  · intro k l hk hl he
    exact hinj k l (hk.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)))
      (hl.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))) he
  · apply strongLocalsRelInsert f a (fun k => live k ∧ k ≠ b) source target x
    constructor
    · intro k l hk hl he
      exact hinj k l (hk.elim Or.inl (fun h => Or.inr (Or.inr h.1)))
        (hl.elim Or.inl (fun h => Or.inr (Or.inr h.1))) he
    · exact slrMono hrel (fun _ hk => ⟨hk.1.1, hk.2, hk.1.2⟩)

/-- HOL `evaluate_apply_colour[Inst]`, literal Skip instruction case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstSkip {width : Nat} [NeZero width] {C F : Type} :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst .skip : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst .skip : WordLangProgHOL (BitVec width)) live lt))
          st.locals cst.locals →
      applyColourPost f (.inst .skip : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨-, hs, hr⟩
  apply applyColourPost_self
  intro _
  simp only [applyColour, applyColourInst, applyColourInstCore]
  rw [evaluate, evaluate]
  exact ⟨rfl, hs, by simpa [inst, getLive, getLiveInst, getLiveInstCore, applyColourLocals] using hr⟩

/-- HOL `evaluate_apply_colour[Inst]`, all sixteen FP operations1374-1391.
Only original premises and full existential result. No successful conversion,
non-NaN, fixed integer width or distinct integer destination assumption. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstFp {width : Nat} [NeZero width] {C F : Type}
    (op : WordLangFp) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.fp op) : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.fp op) : WordLangProgHOL (BitVec width)) live lt))
          st.locals cst.locals →
      applyColourPost f (.inst (.fp op) : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  have hfp := hs.1
  cases op
  all_goals
    simp only [applyColour, applyColourInst, applyColourInstCore]
    simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
    rw [evaluate] at he ⊢
    rw [evaluate]
    simp only [inst, getFpVar, hfp] at he ⊢
  case fpMov =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        dsimp only
        exact ⟨rfl, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpAbs =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        dsimp only
        exact ⟨rfl, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpNeg =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        dsimp only
        exact ⟨rfl, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpSqrt =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        dsimp only
        exact ⟨rfl, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpAdd =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        dsimp only
        exact ⟨rfl, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpSub =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        dsimp only
        exact ⟨rfl, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpMul =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        dsimp only
        exact ⟨rfl, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpDiv =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        dsimp only
        exact ⟨rfl, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpFma =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        dsimp only
        exact ⟨rfl, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpToInt =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        simp_all only
        first | exact ⟨rfl, wsrSetFp _ _ hs, hr⟩ | exact ⟨trivial, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpFromInt =>
    split at he
    · rename_i rst hinst
      repeat' first | split at hinst | cases hinst
      all_goals
        simp_all only
        first | exact ⟨rfl, wsrSetFp _ _ hs, hr⟩ | exact ⟨trivial, wsrSetFp _ _ hs, hr⟩
    · exact absurd rfl he
  case fpLess =>
    split at he
    · rename_i rst hinst
      split at hinst
      · cases hinst
        dsimp only
        refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
        simp only [applyColourLocals, setVar]
        refine strongLocalsRelInsert f _ _ _ _ _ ⟨injInsertOfIset hok.2, ?_⟩
        exact slrMono hr (fun k hk => (sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)
      · cases hinst
    · exact absurd rfl he
  case fpLessEqual =>
    split at he
    · rename_i rst hinst
      split at hinst
      · cases hinst
        dsimp only
        refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
        simp only [applyColourLocals, setVar]
        refine strongLocalsRelInsert f _ _ _ _ _ ⟨injInsertOfIset hok.2, ?_⟩
        exact slrMono hr (fun k hk => (sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)
      · cases hinst
    · exact absurd rfl he
  case fpEqual =>
    split at he
    · rename_i rst hinst
      split at hinst
      · cases hinst
        dsimp only
        refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
        simp only [applyColourLocals, setVar]
        refine strongLocalsRelInsert f _ _ _ _ _ ⟨injInsertOfIset hok.2, ?_⟩
        exact slrMono hr (fun k hk => (sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)
      · cases hinst
    · exact absurd rfl he
  case fpMovToReg r1 r2 d =>
    by_cases hw : width = 64
    · simp only [if_pos hw] at hok hr he ⊢
      split at he
      · rename_i rst hinst
        split at hinst
        · cases hinst
          dsimp only
          refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
          simp only [applyColourLocals, setVar]
          refine strongLocalsRelInsert f r1 _ _ _ _ ⟨injInsertOfIset hok.2, ?_⟩
          exact slrMono hr (fun k hk => (sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)
        · cases hinst
      · exact absurd rfl he
    · simp only [if_neg hw] at hok hr he ⊢
      split at he
      · rename_i rst hinst
        split at hinst
        · cases hinst
          dsimp only
          refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
          simp only [applyColourLocals, setVar]
          apply twoFpWritesLocals f r1 r2 (sptDomain live)
          · intro k l hk hl heq
            apply hok.2 k l _ _ heq
            all_goals simp only [sptDomain_uni, sptDomain_ins, sptDomain_ln]; grind
          · apply slrMono hr
            intro k hk
            simp only [sptDomain_del]
            grind
        · cases hinst
      · exact absurd rfl he
  case fpMovFromReg d r1 r2 =>
    by_cases hw : width = 64
    · simp only [if_pos hw] at hok hr he ⊢
      split at he
      · rename_i rst hinst
        split at hinst
        · rename_i w hget
          have hc := strongLocalsRelGetVar f _ st cst r1 (.word w)
            ⟨hr, by simp [sptDomain_ins], hget⟩
          rw [hc]
          cases hinst
          dsimp only
          refine ⟨rfl, wsrSetFp _ _ hs, ?_⟩
          exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr (Or.inr hk))
        · cases hinst
      · exact absurd rfl he
    · simp only [if_neg hw] at hok hr he ⊢
      split at he
      · rename_i rst hinst
        split at hinst
        · rename_i w1 w2 hget1 hget2
          have hc1 := strongLocalsRelGetVar f _ st cst r1 (.word w1)
            ⟨hr, by simp [sptDomain_ins], hget1⟩
          have hc2 := strongLocalsRelGetVar f _ st cst r2 (.word w2)
            ⟨hr, by simp [sptDomain_ins], hget2⟩
          rw [hc1, hc2]
          cases hinst
          dsimp only
          refine ⟨rfl, wsrSetFp _ _ hs, ?_⟩
          exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
            (Or.inr ((sptDomain_ins _ _ _ k).mpr (Or.inr hk))))
        · cases hinst
      · exact absurd rfl he

end Flapjack.WordAlloc
