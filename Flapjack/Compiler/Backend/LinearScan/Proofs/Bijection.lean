import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.TopLevel
import Flapjack.Compiler.Backend.LinearScan.Proofs.LiveTree
import Flapjack.Compiler.Backend.RegAlloc.Proofs
import Flapjack.Compiler.Backend.RegAlloc.Proofs.SpInverts
import Flapjack.Misc.Sptree.Foldi

/-!
# linear_scanProof: register bijection invariants

Ports of `linear_scanProofScript.sml:4997-5204`. HOL sets of registers are
predicates `Nat → Prop` (`r IN s` is `s r`, `x INSERT s` is
`fun y => y = x ∨ s y`, `UNION` pointwise disjunction, `EMPTY` the false
predicate); `in_clash_tree` is the reviewed `RegAlloc.inClashTree`.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc

/-- HOL proof-script definition `good_bijection_state`
(`linear_scanProofScript.sml:4997-5016`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "good_bijection_state_def"]
def goodBijectionState (st : BijectionState) (regset : Nat → Prop) : Prop :=
  regset = sptDomain st.bij ∧
  (spInverts st.bij st.invbij ∧ spInverts st.invbij st.bij) ∧
  ((∀ r, regset r → (isStackVar r ↔ isStackVar (miscThe 0 (sptLookup r st.bij)))) ∧
    (∀ r, regset r → (isAllocVar r ↔ isAllocVar (miscThe 0 (sptLookup r st.bij)))) ∧
    (∀ r, regset r ∧ isPhyVar r → r = miscThe 0 (sptLookup r st.bij))) ∧
  (∀ r, sptDomain st.invbij r ∧ isStackVar r → r < st.nstack) ∧
  (∀ r, sptDomain st.invbij r ∧ isAllocVar r → r < st.nalloc) ∧
  (isStackVar st.nstack ∧ isAllocVar st.nalloc) ∧
  (∀ r, miscThe 0 (sptLookup r st.bij) ≤ st.nmax)

/-- Exact HOL `convention_partitions_or` (`linear_scanProofScript.sml:5018-5024`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "convention_partitions_or"]
theorem conventionPartitionsOr :
    ∀ (r : Nat),
      (isPhyVar r ∧ ¬ isStackVar r ∧ ¬ isAllocVar r) ∨
      (¬ isPhyVar r ∧ isStackVar r ∧ ¬ isAllocVar r) ∨
      (¬ isPhyVar r ∧ ¬ isStackVar r ∧ isAllocVar r) := by
  intro r
  simp only [isPhyVar, isStackVar, isAllocVar, decide_eq_true_eq]
  omega

private theorem goodCongr {st : BijectionState} {R R' : Nat → Prop}
    (h : goodBijectionState st R) (hR : ∀ x, R x ↔ R' x) : goodBijectionState st R' := by
  have : R = R' := funext fun x => propext (hR x)
  subst this; exact h

private theorem lookupOfDomain (t : Spt Nat) (r : Nat) (h : sptDomain t r) :
    ∃ v, sptLookup r t = some v := by
  unfold sptDomain at h
  cases hl : sptLookup r t with
  | none => rw [hl] at h; simp at h
  | some v => exact ⟨v, rfl⟩

/-- Exact HOL `find_bijection_invariants` (`linear_scanProofScript.sml:5026-5126`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "find_bijection_invariants"]
theorem findBijectionInvariants :
    ∀ (st : BijectionState) (r : Nat) (regset : Nat → Prop),
      goodBijectionState st regset →
      goodBijectionState (findBijectionStep st r) (fun x => x = r ∨ regset x) := by
  intro st r regset hg
  obtain ⟨hR, ⟨hi1, hi2⟩, ⟨hs, ha, hp⟩, hbs, hba, ⟨hns, hna⟩, hmax⟩ := hg
  have mod4 : ∀ n, isStackVar n = decide (n % 4 = 3) := fun _ => rfl
  have mod4a : ∀ n, isAllocVar n = decide (n % 4 = 1) := fun _ => rfl
  have mod2 : ∀ n, isPhyVar n = decide (n % 2 = 0) := fun _ => rfl
  by_cases hin : sptLookup r st.bij ≠ none
  · have hdom : regset r := by rw [hR]; simp [sptDomain, Option.isSome_iff_ne_none, hin]
    unfold findBijectionStep; rw [if_pos hin]
    refine goodCongr ⟨hR, ⟨hi1, hi2⟩, ⟨hs, ha, hp⟩, hbs, hba, ⟨hns, hna⟩, hmax⟩ ?_
    intro x; constructor
    · intro h; exact Or.inr h
    · rintro (rfl | h); exact hdom; exact h
  · have hnone : sptLookup r st.bij = none := by simpa using hin
    have hnd : ¬ sptDomain st.bij r := by simp [sptDomain, hnone]
    have hnr : ¬ regset r := by rw [hR]; exact hnd
    unfold findBijectionStep; rw [if_neg hin]
    have lk : ∀ (v : Nat) x, x ≠ r → sptLookup x (sptInsert r v st.bij) = sptLookup x st.bij :=
      fun v x hx => sptLookup_sptInsert_ne r x v st.bij hx
    have lk0 : ∀ (v : Nat), sptLookup r (sptInsert r v st.bij) = some v :=
      fun v => sptLookup_sptInsert_same r v st.bij
    -- `r` is not yet a value of `invbij` when it is a physical register
    rcases conventionPartitionsOr r with ⟨hP, hS, hA⟩ | ⟨hP, hS, hA⟩ | ⟨hP, hS, hA⟩
    · rw [if_pos hP]
      have hinv : ¬ sptDomain st.invbij r := by
        intro hd
        obtain ⟨fr, hfr⟩ := lookupOfDomain _ _ hd
        have hb := hi2 r fr hfr
        have hfrd : regset fr := by rw [hR]; simp [sptDomain, hb]
        rcases conventionPartitionsOr fr with ⟨hP', -, -⟩ | ⟨-, hS', -⟩ | ⟨-, -, hA'⟩
        · have := hp fr ⟨hfrd, hP'⟩
          rw [hb] at this; simp [miscThe] at this; subst this
          rw [hnone] at hb; cases hb
        · have := (hs fr hfrd).mp hS'
          rw [hb] at this; simp [miscThe] at this; exact hS this
        · have := (ha fr hfrd).mp hA'
          rw [hb] at this; simp [miscThe] at this; exact hA this
      refine ⟨?_, ⟨spInvertsInsert _ _ _ _ ⟨hi1, hnd, hinv⟩, spInvertsInsert _ _ _ _ ⟨hi2, hinv, hnd⟩⟩,
        ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨hns, hna⟩, ?_⟩
      · funext x; rw [sptDomainInsert, hR]
      · intro x hx
        rcases hx with rfl | hx
        · rw [lk0]; rfl
        · have hxr : x ≠ r := fun e => hnr (e ▸ hx)
          rw [lk r x hxr]; exact hs x hx
      · intro x hx
        rcases hx with rfl | hx
        · rw [lk0]; rfl
        · have hxr : x ≠ r := fun e => hnr (e ▸ hx)
          rw [lk r x hxr]; exact ha x hx
      · intro x ⟨hx, hxp⟩
        rcases hx with rfl | hx
        · rw [lk0]; rfl
        · have hxr : x ≠ r := fun e => hnr (e ▸ hx)
          rw [lk r x hxr]; exact hp x ⟨hx, hxp⟩
      · intro x ⟨hx, hxs⟩
        rw [sptDomainInsert] at hx
        rcases hx with rfl | hx
        · exact absurd hxs hS
        · exact hbs x ⟨hx, hxs⟩
      · intro x ⟨hx, hxa⟩
        rw [sptDomainInsert] at hx
        rcases hx with rfl | hx
        · exact absurd hxa hA
        · exact hba x ⟨hx, hxa⟩
      · intro x
        by_cases hxr : x = r
        · subst hxr; rw [lk0]; exact Nat.le_max_left _ _
        · rw [lk r x hxr]; exact Nat.le_trans (hmax x) (Nat.le_max_right _ _)
    · rw [if_neg hP, if_pos hS]
      have hinv : ¬ sptDomain st.invbij st.nstack := by
        intro hd; have := hbs _ ⟨hd, hns⟩; omega
      refine ⟨?_, ⟨spInvertsInsert _ _ _ _ ⟨hi1, hnd, hinv⟩, spInvertsInsert _ _ _ _ ⟨hi2, hinv, hnd⟩⟩,
        ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨?_, hna⟩, ?_⟩
      · funext x; rw [sptDomainInsert, hR]
      · intro x hx
        rcases hx with rfl | hx
        · rw [lk0]; simp only [miscThe]; exact ⟨fun _ => hns, fun _ => hS⟩
        · have hxr : x ≠ r := fun e => hnr (e ▸ hx)
          rw [lk _ x hxr]; exact hs x hx
      · intro x hx
        rcases hx with rfl | hx
        · rw [lk0]; simp only [miscThe]
          have : ¬ isAllocVar st.nstack := by
            rw [mod4] at hns; rw [mod4a]; simp at hns ⊢; omega
          exact ⟨fun h => absurd h hA, fun h => absurd h this⟩
        · have hxr : x ≠ r := fun e => hnr (e ▸ hx)
          rw [lk _ x hxr]; exact ha x hx
      · intro x ⟨hx, hxp⟩
        rcases hx with rfl | hx
        · exact absurd hxp hP
        · have hxr : x ≠ r := fun e => hnr (e ▸ hx)
          rw [lk _ x hxr]; exact hp x ⟨hx, hxp⟩
      · intro x ⟨hx, hxs⟩
        rw [sptDomainInsert] at hx
        rcases hx with rfl | hx
        · dsimp only; omega
        · have := hbs x ⟨hx, hxs⟩; show x < st.nstack + 4; omega
      · intro x ⟨hx, hxa⟩
        rw [sptDomainInsert] at hx
        rcases hx with rfl | hx
        · exfalso; rw [mod4] at hns; rw [mod4a] at hxa; simp at hns hxa; omega
        · exact hba x ⟨hx, hxa⟩
      · show isStackVar (st.nstack + 4)
        rw [mod4] at hns ⊢; simp at hns ⊢; omega
      · intro x
        by_cases hxr : x = r
        · subst hxr; rw [lk0]; exact Nat.le_max_left _ _
        · rw [lk _ x hxr]; exact Nat.le_trans (hmax x) (Nat.le_max_right _ _)
    · rw [if_neg hP, if_neg hS]
      have hinv : ¬ sptDomain st.invbij st.nalloc := by
        intro hd; have := hba _ ⟨hd, hna⟩; omega
      refine ⟨?_, ⟨spInvertsInsert _ _ _ _ ⟨hi1, hnd, hinv⟩, spInvertsInsert _ _ _ _ ⟨hi2, hinv, hnd⟩⟩,
        ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨hns, ?_⟩, ?_⟩
      · funext x; rw [sptDomainInsert, hR]
      · intro x hx
        rcases hx with rfl | hx
        · rw [lk0]; simp only [miscThe]
          have : ¬ isStackVar st.nalloc := by
            rw [mod4a] at hna; rw [mod4]; simp at hna ⊢; omega
          exact ⟨fun h => absurd h hS, fun h => absurd h this⟩
        · have hxr : x ≠ r := fun e => hnr (e ▸ hx)
          rw [lk _ x hxr]; exact hs x hx
      · intro x hx
        rcases hx with rfl | hx
        · rw [lk0]; simp only [miscThe]; exact ⟨fun _ => hna, fun _ => hA⟩
        · have hxr : x ≠ r := fun e => hnr (e ▸ hx)
          rw [lk _ x hxr]; exact ha x hx
      · intro x ⟨hx, hxp⟩
        rcases hx with rfl | hx
        · exact absurd hxp hP
        · have hxr : x ≠ r := fun e => hnr (e ▸ hx)
          rw [lk _ x hxr]; exact hp x ⟨hx, hxp⟩
      · intro x ⟨hx, hxs⟩
        rw [sptDomainInsert] at hx
        rcases hx with rfl | hx
        · exfalso; rw [mod4a] at hna; rw [mod4] at hxs; simp at hna hxs; omega
        · exact hbs x ⟨hx, hxs⟩
      · intro x ⟨hx, hxa⟩
        rw [sptDomainInsert] at hx
        rcases hx with rfl | hx
        · dsimp only; omega
        · have := hba x ⟨hx, hxa⟩; show x < st.nalloc + 4; omega
      · show isAllocVar (st.nalloc + 4)
        rw [mod4a] at hna ⊢; simp at hna ⊢; omega
      · intro x
        by_cases hxr : x = r
        · subst hxr; rw [lk0]; exact Nat.le_max_left _ _
        · rw [lk _ x hxr]; exact Nat.le_trans (hmax x) (Nat.le_max_right _ _)

/-- Exact HOL `FOLDL_find_bijection_invariants` (`linear_scanProofScript.sml:5128-5140`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "FOLDL_find_bijection_invariants"]
theorem foldlFindBijectionInvariants :
    ∀ (st : BijectionState) (l : List Nat) (regset : Nat → Prop),
      goodBijectionState st regset →
      goodBijectionState (l.foldl findBijectionStep st) (fun x => x ∈ l ∨ regset x) := by
  intro st l
  induction l generalizing st with
  | nil => intro regset h; exact goodCongr h (fun x => by simp)
  | cons h t ih =>
      intro regset hg
      have := ih _ _ (findBijectionInvariants st h regset hg)
      refine goodCongr this (fun x => ?_)
      simp only [List.mem_cons]
      constructor
      · rintro (hx | rfl | hx); exact Or.inl (Or.inr hx); exact Or.inl (Or.inl rfl); exact Or.inr hx
      · rintro ((rfl | hx) | hx); exact Or.inr (Or.inl rfl); exact Or.inl hx; exact Or.inr (Or.inr hx)

/-- Exact HOL `foldi_find_bijection_invariants` (`linear_scanProofScript.sml:5142-5154`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "foldi_find_bijection_invariants"]
theorem foldiFindBijectionInvariants {α : Type} :
    ∀ (st : BijectionState) (s : Spt α) (regset : Nat → Prop),
      goodBijectionState st regset →
      goodBijectionState (sptFoldiGen (fun r _v acc => findBijectionStep acc r) 0 st s)
        (fun x => sptDomain s x ∨ regset x) := by
  intro st s regset hg
  rw [sptFoldiGenFoldrToAList]
  have hf : ∀ (l : List (Nat × α)) (b : BijectionState),
      l.foldr (fun p acc => findBijectionStep acc p.1) b =
        (l.map Prod.fst).reverse.foldl findBijectionStep b := by
    intro l b
    rw [List.foldl_reverse]
    induction l with
    | nil => rfl
    | cons p l ih => simp only [List.foldr_cons, List.map_cons, ih]
  rw [hf]
  refine goodCongr (foldlFindBijectionInvariants st _ regset hg) (fun x => ?_)
  rw [List.mem_reverse, sptMemMapFstToAList]

/-- Exact HOL `in_clash_tree_set_eq` (`linear_scanProofScript.sml:5156-5171`); HOL
`UNION` is left-associative. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "in_clash_tree_set_eq"]
theorem inClashTreeSetEq :
    (∀ (w r : List Nat), inClashTree (.delta w r) = fun x => x ∈ w ∨ x ∈ r) ∧
    (∀ (names : NumSet), inClashTree (.set names) = sptDomain names) ∧
    (∀ (name_opt : Option NumSet) (t1 t2 : ClashTree),
      inClashTree (.branch name_opt t1 t2) =
        match name_opt with
        | some names => fun x => (sptDomain names x ∨ inClashTree t1 x) ∨ inClashTree t2 x
        | none => fun x => inClashTree t1 x ∨ inClashTree t2 x) ∧
    (∀ (t1 t2 : ClashTree), inClashTree (.seq t1 t2) = fun x => inClashTree t1 x ∨ inClashTree t2 x) := by
  refine ⟨fun w r => rfl, fun names => funext fun x => rfl, ?_, fun t1 t2 => funext fun x => rfl⟩
  intro name_opt t1 t2
  funext x
  cases name_opt with
  | none => simp [inClashTree]
  | some names =>
      simp only [inClashTree]
      apply propext
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
        · exact Or.inl (Or.inl h)
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)

/-- Exact HOL `find_bijection_clash_tree_invariants`
(`linear_scanProofScript.sml:5173-5198`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "find_bijection_clash_tree_invariants"]
theorem findBijectionClashTreeInvariants :
    ∀ (st : BijectionState) (ct : ClashTree) (regset : Nat → Prop),
      goodBijectionState st regset →
      goodBijectionState (findBijectionClashTree st ct) (fun x => inClashTree ct x ∨ regset x) := by
  intro st ct
  induction ct generalizing st with
  | delta w r =>
      intro regset hg
      have h1 := foldlFindBijectionInvariants st r regset hg
      have h2 := foldlFindBijectionInvariants _ w _ h1
      refine goodCongr h2 (fun x => ?_)
      simp only [inClashTree]
      constructor
      · rintro (h | h | h); exact Or.inl (Or.inl h); exact Or.inl (Or.inr h); exact Or.inr h
      · rintro ((h | h) | h); exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)
  | set cutset =>
      intro regset hg
      exact goodCongr (foldiFindBijectionInvariants st cutset regset hg) (fun x => Iff.rfl)
  | branch o ct1 ct2 ih1 ih2 =>
      intro regset hg
      have h1 := ih1 st regset hg
      have h2 := ih2 _ _ h1
      cases o with
      | none =>
          refine goodCongr h2 (fun x => ?_)
          simp only [inClashTree]
          constructor
          · rintro (h | h | h); exact Or.inl (Or.inr (Or.inl h)); exact Or.inl (Or.inl h); exact Or.inr h
          · rintro ((h | h | h) | h); exact Or.inr (Or.inl h); exact Or.inl h; exact absurd h id
            exact Or.inr (Or.inr h)
      | some cut =>
          refine goodCongr (foldiFindBijectionInvariants _ cut _ h2) (fun x => ?_)
          simp only [inClashTree]
          constructor
          · rintro (h | h | h | h)
            · exact Or.inl (Or.inr (Or.inr h))
            · exact Or.inl (Or.inr (Or.inl h))
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          · rintro ((h | h | h) | h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr h))
  | seq ct1 ct2 ih1 ih2 =>
      intro regset hg
      have h2 := ih2 _ _ (ih1 st regset hg)
      refine goodCongr h2 (fun x => ?_)
      simp only [inClashTree]
      constructor
      · rintro (h | h | h); exact Or.inl (Or.inr h); exact Or.inl (Or.inl h); exact Or.inr h
      · rintro ((h | h) | h); exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h)

/-- Exact HOL `find_bijection_init_invariants` (`linear_scanProofScript.sml:5200-5204`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "find_bijection_init_invariants"]
theorem findBijectionInitInvariants : goodBijectionState findBijectionInit (fun _ => False) := by
  have emp : ∀ r, ¬ sptDomain (Spt.ln : Spt Nat) r := by intro r; simp [sptDomain, sptLookup]
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · funext x; simp [findBijectionInit, sptDomain]
  · intro m fm h; simp [findBijectionInit] at h
  · intro m fm h; simp [findBijectionInit] at h
  · intro r h; exact h.elim
  · intro r h; exact h.elim
  · intro r h; exact h.1.elim
  · intro r h; exact absurd h.1 (emp r)
  · intro r h; exact absurd h.1 (emp r)
  · decide
  · decide
  · intro r; simp [findBijectionInit, miscThe]

end Flapjack.LinearScan
