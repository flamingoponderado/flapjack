import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace InstArithWitnesses

/-- Imported canonical finite-map carrier roundtrip. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end InstArithWitnesses

/-- Flapjack proof infrastructure for the source's ordered two-register
updates. Injectivity is scoped to the two writes and final live set; aliases
are allowed. This is not a separate HOL declaration. -/
private theorem twoWritesLocals {α : Type} (f : Nat → Nat) (a b : Nat)
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

/-- HOL `evaluate_apply_colour[Inst]`, division subcase of the shared
get_vars block (1264-1290). The source nonzero divisor guard is retained;
no successful-evaluation or register-distinctness premise is added. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstDiv {width : Nat} [NeZero width] {C F : Type}
    (dst left right : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.arith (.div dst left right)) : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.arith (.div dst left right)) : WordLangProgHOL (BitVec width)) live lt))
          st.locals cst.locals →
      applyColourPost f (.inst (.arith (.div dst left right)) : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i q w hvars
      have hcv := strongLocalsRelGetVars [right, left] [.word q, .word w] f _ st cst
        ⟨hr, by
          intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl <;> simp [sptDomain_ins], hvars⟩
      simp only [List.map_cons, List.map_nil] at hcv
      rw [hcv]
      split at hinst
      · rename_i hq
        cases hinst
        simp only [if_pos hq]
        refine ⟨trivial, wsrLocals _ _ hs, ?_⟩
        simp only [applyColourLocals, setVar]
        refine strongLocalsRelInsert f dst _ _ _ _ ⟨injInsertOfIset hok.2, ?_⟩
        exact slrMono hr (fun k hk => (sptDomain_ins _ _ _ k).mpr
          (Or.inr ((sptDomain_ins _ _ _ k).mpr
            (Or.inr ((sptDomain_del _ _ k).mpr ⟨hk.2, hk.1⟩)))))
      · cases hinst
    · cases hinst
  · exact absurd rfl he


/-- HOL `evaluate_apply_colour[Inst]`, AddCarry subcase of the shared
get_vars block1264-1290. Original three premises and full existential result;
ordered writes preserve all alias cases without a distinctness premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstAddCarry {width : Nat} [NeZero width] {C F : Type}
    (a b c d : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.arith (.addCarry a b c d)) : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.arith (.addCarry a b c d)) : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.arith (.addCarry a b c d)) : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i w0 w1 w2 hvars
      have hcv := strongLocalsRelGetVars [b, c, d] [.word w0, .word w1, .word w2] f _ st cst
        ⟨hr, by
          intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          simp only [sptDomain_ins, sptDomain_del]
          grind, hvars⟩
      simp only [List.map_cons, List.map_nil] at hcv
      rw [hcv]
      cases hinst
      dsimp only
      refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
      simp only [applyColourLocals, setVar]
      apply twoWritesLocals f a d (sptDomain live)
      · intro k l hk hl heq
        apply hok.2 k l _ _ heq
        all_goals simp only [sptDomain_uni, sptDomain_ins, sptDomain_ln]; grind
      · apply slrMono hr
        intro k hk
        simp only [sptDomain_ins, sptDomain_del]
        grind
    · cases hinst
  · exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, AddOverflow subcase of the shared
get_vars block1264-1290. Original three premises and full existential result;
ordered writes preserve all alias cases without a distinctness premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstAddOverflow {width : Nat} [NeZero width] {C F : Type}
    (a b c d : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.arith (.addOverflow a b c d)) : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.arith (.addOverflow a b c d)) : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.arith (.addOverflow a b c d)) : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i w0 w1 hvars
      have hcv := strongLocalsRelGetVars [b, c] [.word w0, .word w1] f _ st cst
        ⟨hr, by
          intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          simp only [sptDomain_ins, sptDomain_del]
          grind, hvars⟩
      simp only [List.map_cons, List.map_nil] at hcv
      rw [hcv]
      cases hinst
      dsimp only
      refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
      simp only [applyColourLocals, setVar]
      apply twoWritesLocals f a d (sptDomain live)
      · intro k l hk hl heq
        apply hok.2 k l _ _ heq
        all_goals simp only [sptDomain_uni, sptDomain_ins, sptDomain_ln]; grind
      · apply slrMono hr
        intro k hk
        simp only [sptDomain_ins, sptDomain_del]
        grind
    · cases hinst
  · exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, SubOverflow subcase of the shared
get_vars block1264-1290. Original three premises and full existential result;
ordered writes preserve all alias cases without a distinctness premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstSubOverflow {width : Nat} [NeZero width] {C F : Type}
    (a b c d : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.arith (.subOverflow a b c d)) : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.arith (.subOverflow a b c d)) : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.arith (.subOverflow a b c d)) : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i w0 w1 hvars
      have hcv := strongLocalsRelGetVars [b, c] [.word w0, .word w1] f _ st cst
        ⟨hr, by
          intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          simp only [sptDomain_ins, sptDomain_del]
          grind, hvars⟩
      simp only [List.map_cons, List.map_nil] at hcv
      rw [hcv]
      cases hinst
      dsimp only
      refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
      simp only [applyColourLocals, setVar]
      apply twoWritesLocals f a d (sptDomain live)
      · intro k l hk hl heq
        apply hok.2 k l _ _ heq
        all_goals simp only [sptDomain_uni, sptDomain_ins, sptDomain_ln]; grind
      · apply slrMono hr
        intro k hk
        simp only [sptDomain_ins, sptDomain_del]
        grind
    · cases hinst
  · exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, LongMul subcase of the shared
get_vars block1264-1290. Original three premises and full existential result;
ordered writes preserve all alias cases without a distinctness premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstLongMul {width : Nat} [NeZero width] {C F : Type}
    (a b c d : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.arith (.longMul a b c d)) : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.arith (.longMul a b c d)) : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.arith (.longMul a b c d)) : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i w0 w1 hvars
      have hcv := strongLocalsRelGetVars [c, d] [.word w0, .word w1] f _ st cst
        ⟨hr, by
          intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          simp only [sptDomain_ins, sptDomain_del]
          grind, hvars⟩
      simp only [List.map_cons, List.map_nil] at hcv
      rw [hcv]
      cases hinst
      dsimp only
      refine ⟨rfl, wsrLocals _ _ hs, ?_⟩
      simp only [applyColourLocals, setVar]
      apply twoWritesLocals f a b (sptDomain live)
      · intro k l hk hl heq
        apply hok.2 k l _ _ heq
        all_goals simp only [sptDomain_uni, sptDomain_ins, sptDomain_ln]; grind
      · apply slrMono hr
        intro k hk
        simp only [sptDomain_ins, sptDomain_del]
        grind
    · cases hinst
  · exact absurd rfl he

/-- HOL `evaluate_apply_colour[Inst]`, LongDiv subcase of the shared
get_vars block1264-1290. Original three premises and full existential result;
ordered writes preserve all alias cases without a distinctness premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_InstLongDiv {width : Nat} [NeZero width] {C F : Type}
    (a b c d e : Nat) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.inst (.arith (.longDiv a b c d e)) : WordLangProgHOL (BitVec width)) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.inst (.arith (.longDiv a b c d e)) : WordLangProgHOL (BitVec width)) live lt)) st.locals cst.locals →
      applyColourPost f (.inst (.arith (.longDiv a b c d e)) : WordLangProgHOL (BitVec width)) live lt st cst := by
  rintro st cst f live lt ⟨hok, hs, hr⟩
  apply applyColourPost_self
  intro he
  simp only [applyColour, applyColourInst, applyColourInstCore]
  simp only [colouringOk, getWrites, getWritesInst, getLive, getLiveInst, getLiveInstCore] at hok hr
  rw [evaluate] at he ⊢
  rw [evaluate]
  simp only [inst] at he ⊢
  split at he
  · rename_i rst hinst
    split at hinst
    · rename_i w0 w1 w2 hvars
      have hcv := strongLocalsRelGetVars [c, d, e] [.word w0, .word w1, .word w2] f _ st cst
        ⟨hr, by
          intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          simp only [sptDomain_ins, sptDomain_del]
          grind, hvars⟩
      simp only [List.map_cons, List.map_nil] at hcv
      rw [hcv]
      split at hinst
      · rename_i hguard
        cases hinst
        simp only [if_pos hguard]
        refine ⟨trivial, wsrLocals _ _ hs, ?_⟩
        simp only [applyColourLocals, setVar]
        apply twoWritesLocals f b a (sptDomain live)
        · intro k l hk hl heq
          apply hok.2 k l _ _ heq
          all_goals simp only [sptDomain_uni, sptDomain_ins, sptDomain_ln]; grind
        · apply slrMono hr
          intro k hk
          simp only [sptDomain_ins, sptDomain_del]
          grind
      · cases hinst
    · cases hinst
  · exact absurd rfl he

end Flapjack.WordAlloc
