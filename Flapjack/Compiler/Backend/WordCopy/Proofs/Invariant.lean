import Flapjack.Compiler.Backend.WordCopy
import Flapjack.Misc.Sptree.InterEq

/-!
# word_copyProof: the `copy_state` invariant

Ports of the `CPstate_inv` group of `cakeml/compiler/backend/proofs/word_copyProofScript.sml`
(lines 12-268 and 436-468): the invariant, its preservation by `empty_eq`, `remove_eq(s)`,
`set_eq`, `merge_eqs` and `set_store_eq`, and the `lookup_eq`/`lookup_store_eq` facts about
`set_eq`. HOL `x ∈ domain t` is `sptMem x t`, `ALOOKUP` is `List.lookup`, and
`lookup`/`insert` are the `Spt` operations.
-/

namespace Flapjack.Compiler.Backend.WordCopy

open Flapjack

/-- Exact HOL `CPstate_inv_def` (`word_copyProofScript.sml:12-24`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "CPstate_inv_def"]
def cpStateInv (cs : CopyState) : Prop :=
  (∀ v c, sptLookup v cs.toEq = some c → c < cs.next) ∧
  (∀ c, sptMem c cs.fromEq → c < cs.next) ∧
  (∀ s c, cs.storeToEq.lookup s = some c → c < cs.next) ∧
  (∀ c v, sptLookup c cs.fromEq = some v → sptLookup v cs.toEq = some c)

/-- HOL `lookup_insert` without a well-formedness premise (Flapjack infrastructure). -/
theorem sptLookupInsert {α : Type} (k k' : Nat) (v : α) (t : Spt α) :
    sptLookup k (sptInsert k' v t) = if k = k' then some v else sptLookup k t := by
  by_cases h : k = k'
  · subst h; rw [if_pos rfl, sptLookup_sptInsert_same]
  · rw [if_neg h, sptLookup_sptInsert_ne _ _ _ _ h]

/-- The class of `y` with a representative, as scrutinised by `set_eq`/`set_store_eq`
(Flapjack infrastructure). -/
def liveClass (cs : CopyState) (y : Nat) : Option Nat :=
  match sptLookup y cs.toEq with
  | none => none
  | some c => if sptLookup c cs.fromEq = none then none else some c

theorem liveClass_some {cs : CopyState} {y c : Nat} :
    liveClass cs y = some c ↔ sptLookup y cs.toEq = some c ∧ sptLookup c cs.fromEq ≠ none := by
  unfold liveClass
  cases h : sptLookup y cs.toEq with
  | none => simp
  | some c' =>
      by_cases h' : sptLookup c' cs.fromEq = none
      · simp only [h', if_true]
        constructor
        · intro h; cases h
        · rintro ⟨h1, h2⟩; cases h1; exact absurd h' h2
      · simp only [h', if_false]
        constructor
        · intro h1; cases h1; exact ⟨rfl, h'⟩
        · rintro ⟨h1, _⟩; cases h1; rfl

theorem setEq_eq (cs : CopyState) (x y : Nat) :
    setEq cs x y =
      if isAllocVar x = true ∧ isAllocVar y = true then
        match liveClass cs y with
        | none =>
          { toEq := sptInsert x cs.next (sptInsert y cs.next cs.toEq)
            fromEq := sptInsert cs.next x cs.fromEq
            storeToEq := cs.storeToEq
            next := cs.next + 1 }
        | some c =>
          { toEq := sptInsert x c cs.toEq
            fromEq := sptInsert c x cs.fromEq
            storeToEq := cs.storeToEq
            next := cs.next }
      else cs := rfl

theorem setStoreEq_eq (cs : CopyState) (s : WordStoreHOL) (y : Nat) :
    setStoreEq cs s y =
      if isAllocVar y = true then
        match liveClass cs y with
        | none =>
          { toEq := sptInsert y cs.next cs.toEq
            fromEq := sptInsert cs.next y cs.fromEq
            storeToEq := (s, cs.next) :: cs.storeToEq
            next := cs.next + 1 }
        | some c => { cs with storeToEq := (s, c) :: cs.storeToEq }
      else emptyEq := rfl

/-- Exact HOL `unique_rep` (`word_copyProofScript.sml:27-35`, `[local]`, unused in HOL). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "unique_rep"]
theorem uniqueRep {cs : CopyState} {c c' : Nat} :
    cpStateInv cs →
      sptMem c cs.fromEq ∧ sptMem c' cs.fromEq ∧ c ≠ c' →
        sptLookup c cs.fromEq ≠ sptLookup c' cs.fromEq := by
  rintro ⟨_, _, _, h4⟩ ⟨hc, _, hne⟩ heq
  simp only [sptMem, sptDomain, Option.isSome_iff_exists] at hc
  obtain ⟨v, hv⟩ := hc
  have h1 := h4 c v hv
  have h2 := h4 c' v (heq ▸ hv)
  rw [h1] at h2
  exact hne (Option.some.inj h2)

/-- Exact HOL `empty_eq_inv` (`word_copyProofScript.sml:37-41`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "empty_eq_inv"]
theorem emptyEqInv : cpStateInv emptyEq := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [emptyEq, sptMem, sptDomain]

/-- Exact HOL `remove_eq_inv` (`word_copyProofScript.sml:43-50`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eq_inv"]
theorem removeEqInv : ∀ (cs : CopyState) (v : Nat), cpStateInv cs → cpStateInv (removeEq cs v) := by
  intro cs v h
  unfold removeEq
  split
  · exact h
  · exact emptyEqInv

/-- Exact HOL `remove_eqs_inv` (`word_copyProofScript.sml:52-58`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "remove_eqs_inv"]
theorem removeEqsInv : ∀ (vv : List Nat) (cs : CopyState), cpStateInv cs →
    cpStateInv (removeEqs cs vv)
  | [], _, h => h
  | v :: vv, cs, h => removeEqsInv vv (removeEq cs v) (removeEqInv cs v h)

/-- Exact HOL `n_lt_n1` (`word_copyProofScript.sml:60-65`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "n_lt_n1"]
theorem nLtN1 {n x y z : Nat} : n < n + 1 ∧ (x < y ∧ y < z → x < z) :=
  ⟨Nat.lt_succ_self n, fun ⟨h1, h2⟩ => Nat.lt_trans h1 h2⟩

/-- Exact HOL `set_eq_inv` (`word_copyProofScript.sml:67-78`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_eq_inv"]
theorem setEqInv {cs : CopyState} {t s : Nat} :
    cpStateInv cs ∧ sptLookup t cs.toEq = none → cpStateInv (setEq cs t s) := by
  rintro ⟨⟨h1, h2, h3, h4⟩, ht⟩
  rw [setEq_eq]
  split
  case isFalse => exact ⟨h1, h2, h3, h4⟩
  case isTrue =>
  cases hcl : liveClass cs s with
  | none =>
      unfold cpStateInv; dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro v c hv
        simp only [sptLookupInsert] at hv
        split at hv
        · cases hv; omega
        split at hv
        · cases hv; omega
        · have := h1 v c hv; omega
      · intro c hc
        simp only [sptMem, sptDomain, sptLookupInsert] at hc
        split at hc
        · omega
        · have := h2 c hc; omega
      · intro s' c hc
        have := h3 s' c hc; omega
      · intro c v hc
        simp only [sptLookupInsert] at hc ⊢
        split at hc
        · cases hc; simp_all
        · have hv := h4 c v hc
          have hlt := h1 v c hv
          have hct : c ≠ cs.next := by omega
          by_cases hvt : v = t
          · subst hvt; rw [ht] at hv; cases hv
          · rw [if_neg hvt]
            by_cases hvs : v = s
            · subst hvs
              exact absurd (liveClass_some.mpr ⟨hv, by rw [hc]; simp⟩) (by rw [hcl]; simp)
            · rw [if_neg hvs]; exact hv
  | some c0 =>
      unfold cpStateInv; dsimp only
      obtain ⟨hs, hfrom⟩ := liveClass_some.mp hcl
      have hc0 := h1 s c0 hs
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro v c hv
        simp only [sptLookupInsert] at hv
        split at hv
        · cases hv; exact hc0
        · exact h1 v c hv
      · intro c hc
        simp only [sptMem, sptDomain, sptLookupInsert] at hc
        split at hc
        · subst_vars; exact hc0
        · exact h2 c hc
      · exact h3
      · intro c v hc
        simp only [sptLookupInsert] at hc ⊢
        split at hc
        · cases hc; simp_all
        · have hv := h4 c v hc
          by_cases hvt : v = t
          · subst hvt; rw [ht] at hv; cases hv
          · rw [if_neg hvt]; exact hv

/-- `ALOOKUP_MEM` for `List.lookup` (Flapjack infrastructure). -/
theorem listMemOfLookup {α β : Type} [DecidableEq α] {l : List (α × β)} {a : α} {b : β} :
    l.lookup a = some b → (a, b) ∈ l := by
  induction l with
  | nil => intro h; cases h
  | cons p l ih =>
      obtain ⟨x, y⟩ := p
      intro h
      simp only [List.lookup] at h
      split at h
      · rename_i hxa; cases h
        have : a = x := by simpa using hxa
        subst this; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- Exact HOL `merge_eqs_inv` (`word_copyProofScript.sml:80-104`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "merge_eqs_inv"]
theorem mergeEqsInv {cs1 cs2 : CopyState} :
    cpStateInv cs1 ∧ cpStateInv cs2 → cpStateInv (mergeEqs cs1 cs2) := by
  rintro ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v c hv
    simp only [mergeEqs, sptLookupInterEq] at hv ⊢
    cases hx : sptLookup v cs1.toEq with
    | none => rw [hx] at hv; cases hv
    | some x =>
        rw [hx] at hv
        simp only at hv
        split at hv
        · cases hv; have := a1 v _ hx; omega
        · cases hv
  · intro c hc
    simp only [mergeEqs, sptMem, sptDomain, sptLookupInterEq] at hc ⊢
    cases hx : sptLookup c cs1.fromEq with
    | none => rw [hx] at hc; cases hc
    | some x => have := a2 c (by simp [sptMem, sptDomain, hx]); omega
  · intro s c hc
    simp only [mergeEqs] at hc ⊢
    have hmem := listMemOfLookup hc
    have := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq] at this
    have := a3 s c this.1; omega
  · intro c v hc
    simp only [mergeEqs, sptLookupInterEq] at hc ⊢
    cases hx : sptLookup c cs1.fromEq with
    | none => rw [hx] at hc; cases hc
    | some x =>
        rw [hx] at hc
        simp only at hc
        split at hc
        · rename_i hx2
          cases hc
          rw [a4 c v hx, b4 c v hx2]; simp
        · cases hc

/-- Exact HOL `set_store_eq_inv` (`word_copyProofScript.sml:106-117`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_store_eq_inv"]
theorem setStoreEqInv {cs : CopyState} {name : WordStoreHOL} {e : Nat} :
    cpStateInv cs → cpStateInv (setStoreEq cs name e) := by
  rintro ⟨h1, h2, h3, h4⟩
  rw [setStoreEq_eq]
  split
  case isFalse => exact emptyEqInv
  case isTrue =>
  cases hcl : liveClass cs e with
  | none =>
      unfold cpStateInv; dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro v c hv
        simp only [sptLookupInsert] at hv
        split at hv
        · cases hv; omega
        · have := h1 v c hv; omega
      · intro c hc
        simp only [sptMem, sptDomain, sptLookupInsert] at hc
        split at hc
        · omega
        · have := h2 c hc; omega
      · intro s' c hc
        simp only [List.lookup] at hc
        split at hc
        · cases hc; omega
        · have := h3 s' c hc; omega
      · intro c v hc
        simp only [sptLookupInsert] at hc ⊢
        split at hc
        · cases hc; simp_all
        · have hv := h4 c v hc
          have hlt := h1 v c hv
          by_cases hve : v = e
          · subst hve
            exact absurd (liveClass_some.mpr ⟨hv, by rw [hc]; simp⟩) (by rw [hcl]; simp)
          · rw [if_neg hve]; exact hv
  | some c0 =>
      unfold cpStateInv; dsimp only
      obtain ⟨hs, _⟩ := liveClass_some.mp hcl
      have hc0 := h1 e c0 hs
      refine ⟨h1, h2, ?_, h4⟩
      intro s' c hc
      simp only [List.lookup] at hc
      split at hc
      · cases hc; exact hc0
      · exact h3 s' c hc

/-- The two shapes of `lookup_eq` (Flapjack infrastructure, from `lookup_eq_def`). -/
theorem lookupEq_cases (cs : CopyState) (v : Nat) :
    (lookupEq cs v = v ∧ ∀ c, sptLookup v cs.toEq = some c → sptLookup c cs.fromEq = none) ∨
      ∃ c r, sptLookup v cs.toEq = some c ∧ sptLookup c cs.fromEq = some r ∧ lookupEq cs v = r := by
  unfold lookupEq
  cases h : sptLookup v cs.toEq with
  | none => left; simp
  | some c =>
      cases h' : sptLookup c cs.fromEq with
      | none => left; simp [h']
      | some r => right; exact ⟨c, r, rfl, h', by simp [h']⟩

/-- Exact HOL `same_classD` (`word_copyProofScript.sml:119-132`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "same_classD"]
theorem sameClassD {cs : CopyState} {x y : Nat} :
    cpStateInv cs ∧ lookupEq cs x = lookupEq cs y →
      x = y ∨ (x ≠ y ∧ ∃ c rep, sptLookup x cs.toEq = some c ∧ sptLookup y cs.toEq = some c ∧
        sptLookup c cs.fromEq = some rep) := by
  rintro ⟨⟨_, _, _, h4⟩, h⟩
  by_cases hxy : x = y
  · exact Or.inl hxy
  right; refine ⟨hxy, ?_⟩
  rcases lookupEq_cases cs x with ⟨hx, hxn⟩ | ⟨cx, rx, hxc, hxr, hx⟩ <;>
    rcases lookupEq_cases cs y with ⟨hy, hyn⟩ | ⟨cy, ry, hyc, hyr, hy⟩
  · exact absurd (by rw [← hx, ← hy, h]) hxy
  · have : x = ry := by rw [← hx, h, hy]
    subst this
    have := hxn cy (h4 cy x hyr)
    rw [hyr] at this; cases this
  · have : y = rx := by rw [← hy, ← h, hx]
    subst this
    have := hyn cx (h4 cx y hxr)
    rw [hxr] at this; cases this
  · have hrr : rx = ry := by rw [← hx, ← hy, h]
    subst hrr
    have e1 := h4 cx rx hxr
    have e2 := h4 cy rx hyr
    rw [e1] at e2; cases e2
    exact ⟨cx, rx, hxc, hyc, hxr⟩

/-- Exact HOL `same_classD'` (`word_copyProofScript.sml:134-145`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "same_classD'"]
theorem sameClassD' {cs : CopyState} {x : WordStoreHOL} {y : Nat} :
    cpStateInv cs ∧ lookupStoreEq cs x = some (lookupEq cs y) →
      ∃ c rep, cs.storeToEq.lookup x = some c ∧ sptLookup y cs.toEq = some c ∧
        sptLookup c cs.fromEq = some rep := by
  rintro ⟨⟨_, _, _, h4⟩, h⟩
  unfold lookupStoreEq at h
  cases hs : cs.storeToEq.lookup x with
  | none => rw [hs] at h; cases h
  | some c =>
  rw [hs] at h
  simp only at h
  cases hf : sptLookup c cs.fromEq with
  | none => rw [hf] at h; cases h
  | some v' =>
  rw [hf] at h
  simp only [Option.some.injEq] at h
  rcases lookupEq_cases cs y with ⟨hy, hyn⟩ | ⟨cy, ry, hyc, hyr, hy⟩
  · rw [hy] at h; subst h
    have := hyn c (h4 c v' hf); rw [hf] at this; cases this
  · rw [hy] at h
    have e1 := h4 cy ry hyr
    have e2 := h4 c v' hf
    rw [h, e1] at e2; cases e2
    exact ⟨_, ry, rfl, hyc, hyr⟩

/-- Exact HOL `lookup_eqI` (`word_copyProofScript.sml:147-153`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eqI"]
theorem lookupEqI : ∀ (cs : CopyState) (r v : Nat),
    (r = v ∧ sptLookup v cs.toEq = none) ∨
      (∃ c, sptLookup v cs.toEq = some c ∧ sptLookup c cs.fromEq = some r) →
    lookupEq cs v = r := by
  rintro cs r v (⟨rfl, h⟩ | ⟨c, h1, h2⟩)
  · simp [lookupEq, h]
  · simp [lookupEq, h1, h2]

/-- Exact HOL `both_alloc_vars_def` (`word_copyProofScript.sml:155-157`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "both_alloc_vars_def"]
def bothAllocVars : Nat × Nat → Prop
  | (t, s) => isAllocVar t = true ∧ isAllocVar s = true

/-- Exact HOL `lookup_eq_set_eq_not_alloc_var` (`word_copyProofScript.sml:159-165`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_not_alloc_var"]
theorem lookupEqSetEqNotAllocVar {t s : Nat} {cs : CopyState} {v : Nat} :
    ¬ bothAllocVars (t, s) → lookupEq (setEq cs t s) v = lookupEq cs v := by
  intro h
  have h' : ¬(isAllocVar t = true ∧ isAllocVar s = true) := h
  rw [setEq_eq, if_neg h']

/-- `set_eq` on two alloc vars, by the class of `s` (Flapjack infrastructure). -/
theorem setEq_both {cs : CopyState} {t s : Nat} (h : bothAllocVars (t, s)) :
    setEq cs t s =
      match liveClass cs s with
      | none =>
        { toEq := sptInsert t cs.next (sptInsert s cs.next cs.toEq)
          fromEq := sptInsert cs.next t cs.fromEq
          storeToEq := cs.storeToEq
          next := cs.next + 1 }
      | some c =>
        { toEq := sptInsert t c cs.toEq
          fromEq := sptInsert c t cs.fromEq
          storeToEq := cs.storeToEq
          next := cs.next } := by
  rw [setEq_eq, if_pos (show isAllocVar t = true ∧ isAllocVar s = true from h)]

/-- Exact HOL `lookup_eq_set_eq_is_alloc_var1` (`word_copyProofScript.sml:168-186`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_is_alloc_var1"]
theorem lookupEqSetEqIsAllocVar1 {cs : CopyState} {t s v : Nat} :
    cpStateInv cs ∧ bothAllocVars (t, s) → sptLookup t cs.toEq = none →
      lookupEq cs s = lookupEq cs v → lookupEq (setEq cs t s) v = t := by
  rintro ⟨hinv, hb⟩ _ heq
  rcases sameClassD ⟨hinv, heq⟩ with rfl | ⟨_, c, rep, hs, hv, hc⟩
  · rw [setEq_both hb]
    cases hcl : liveClass cs s with
    | none =>
        apply lookupEqI; right
        exact ⟨cs.next, by simp [sptLookupInsert], by simp [sptLookupInsert]⟩
    | some c =>
        obtain ⟨hs, _⟩ := liveClass_some.mp hcl
        apply lookupEqI; right
        refine ⟨c, ?_, by simp [sptLookupInsert]⟩
        dsimp only; rw [sptLookupInsert]; split <;> simp_all
  · have hcl : liveClass cs s = some c := liveClass_some.mpr ⟨hs, by rw [hc]; simp⟩
    rw [setEq_both hb, hcl]
    apply lookupEqI; right
    refine ⟨c, ?_, by simp [sptLookupInsert]⟩
    dsimp only; rw [sptLookupInsert]; split <;> simp_all

/-- Exact HOL `lookup_eq_set_eq_is_alloc_var2` (`word_copyProofScript.sml:188-214`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_is_alloc_var2"]
theorem lookupEqSetEqIsAllocVar2 {cs : CopyState} {t s v : Nat} :
    cpStateInv cs ∧ bothAllocVars (t, s) → sptLookup t cs.toEq = none → v ≠ t →
      lookupEq cs s ≠ lookupEq cs v → lookupEq (setEq cs t s) v = lookupEq cs v := by
  rintro ⟨⟨h1, _, _, _⟩, hb⟩ _ hvt hne
  rw [setEq_both hb]
  cases hcl : liveClass cs s with
  | none =>
      have hvs : v ≠ s := by rintro rfl; exact hne rfl
      unfold lookupEq
      dsimp only
      rw [sptLookupInsert, if_neg hvt, sptLookupInsert, if_neg hvs]
      cases hl : sptLookup v cs.toEq with
      | none => rfl
      | some c =>
          have := h1 v c hl
          dsimp only
          rw [sptLookupInsert, if_neg (by omega)]
  | some c0 =>
      obtain ⟨hs, hfrom⟩ := liveClass_some.mp hcl
      unfold lookupEq
      dsimp only
      rw [sptLookupInsert, if_neg hvt]
      cases hl : sptLookup v cs.toEq with
      | none => rfl
      | some c =>
          dsimp only
          rw [sptLookupInsert]
          by_cases hcc : c = c0
          · subst hcc
            exfalso; apply hne
            cases hr : sptLookup c cs.fromEq with
            | none => exact absurd hr hfrom
            | some r =>
                rw [lookupEqI cs r s (Or.inr ⟨c, hs, hr⟩),
                  lookupEqI cs r v (Or.inr ⟨c, hl, hr⟩)]
          · rw [if_neg hcc]

/-- Exact HOL `lookup_eq_set_eq_t` (`word_copyProofScript.sml:216-223`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_t"]
theorem lookupEqSetEqT {cs : CopyState} {t s : Nat} :
    cpStateInv cs ∧ bothAllocVars (t, s) → lookupEq (setEq cs t s) t = t := by
  rintro ⟨_, hb⟩
  rw [setEq_both hb]
  cases liveClass cs s with
  | none => apply lookupEqI; right; exact ⟨cs.next, by simp [sptLookupInsert], by simp [sptLookupInsert]⟩
  | some c => apply lookupEqI; right; exact ⟨c, by simp [sptLookupInsert], by simp [sptLookupInsert]⟩

/-- Exact HOL `lookup_eq_set_eq_s` (`word_copyProofScript.sml:225-232`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eq_s"]
theorem lookupEqSetEqS {cs : CopyState} {t s : Nat} :
    cpStateInv cs ∧ bothAllocVars (t, s) → sptLookup t cs.toEq = none →
      lookupEq (setEq cs t s) s = t := by
  intro h ht
  by_cases hst : s = t
  · subst hst; exact lookupEqSetEqT h
  · exact lookupEqSetEqIsAllocVar1 h ht rfl

/-- A non-trivial class representative `t` has a class itself (Flapjack infrastructure). -/
theorem lookupEq_rep_ne {cs : CopyState} {v t : Nat} (hinv : cpStateInv cs)
    (ht : sptLookup t cs.toEq = none) (h : lookupEq cs v = t) : v = t := by
  obtain ⟨_, _, _, h4⟩ := hinv
  rcases lookupEq_cases cs v with ⟨hv, _⟩ | ⟨c, r, _, hr, hv⟩
  · rw [← hv]; exact h
  · rw [hv] at h; subst h
    have := h4 c r hr; rw [ht] at this; cases this

/-- Exact HOL `lookup_eq_set_eqD` (`word_copyProofScript.sml:234-268`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_set_eqD"]
theorem lookupEqSetEqD {cs : CopyState} {t s v r : Nat} :
    cpStateInv cs → sptLookup t cs.toEq = none → lookupEq (setEq cs t s) v = r →
      (r = t → v = t ∨ lookupEq cs v = lookupEq cs s) ∧ (r ≠ t → r = lookupEq cs v) := by
  intro hinv ht h
  by_cases hb : bothAllocVars (t, s)
  · refine ⟨?_, ?_⟩
    · intro hrt
      rw [hrt] at h
      by_cases hvt : v = t
      · exact Or.inl hvt
      · right
        refine Classical.byContradiction fun hne => ?_
        have := lookupEqSetEqIsAllocVar2 ⟨hinv, hb⟩ ht hvt (Ne.symm hne)
        rw [h] at this
        exact hvt (lookupEq_rep_ne hinv ht this.symm)
    · intro hrt
      by_cases hvt : v = t
      · subst hvt; exact absurd (h ▸ lookupEqSetEqT ⟨hinv, hb⟩) hrt
      by_cases hsv : lookupEq cs s = lookupEq cs v
      · exact absurd (h ▸ lookupEqSetEqIsAllocVar1 ⟨hinv, hb⟩ ht hsv) hrt
      · rw [← h]; exact lookupEqSetEqIsAllocVar2 ⟨hinv, hb⟩ ht hvt hsv
  · rw [lookupEqSetEqNotAllocVar hb] at h
    refine ⟨?_, fun _ => h.symm⟩
    intro hrt
    rw [hrt] at h
    exact Or.inl (lookupEq_rep_ne hinv ht h)

/-- Exact HOL `set_eq_store_to_eq` (`word_copyProofScript.sml:436-440`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "set_eq_store_to_eq"]
theorem setEqStoreToEq {cs : CopyState} {t s : Nat} : (setEq cs t s).storeToEq = cs.storeToEq := by
  rw [setEq_eq]
  split
  · cases liveClass cs s <;> rfl
  · rfl

/-- Exact HOL `lookup_eq_remove_eq_t` (`word_copyProofScript.sml:442-452`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_eq_remove_eq_t"]
theorem lookupEqRemoveEqT {cs : CopyState} {t x : Nat} :
    cpStateInv cs ∧ lookupEq (removeEq cs t) x = t → x = t := by
  rintro ⟨hinv, h⟩
  unfold removeEq at h
  cases ht : sptLookup t cs.toEq with
  | none => rw [ht] at h; exact lookupEq_rep_ne hinv ht h
  | some _ => rw [ht] at h; simpa [lookupEq, emptyEq, sptLookup] using h

/-- Exact HOL `lookup_store_eq_set_eqD` (`word_copyProofScript.sml:454-468`). -/
@[hol "cakeml/compiler/backend/proofs/word_copyProofScript.sml" "lookup_store_eq_set_eqD"]
theorem lookupStoreEqSetEqD {cs : CopyState} {t s : Nat} {v : WordStoreHOL} {r : Nat} :
    cpStateInv cs → sptLookup t cs.toEq = none → lookupStoreEq (setEq cs t s) v = some r →
      (r = t → lookupStoreEq cs v = some (lookupEq cs s)) ∧
        (r ≠ t → lookupStoreEq cs v = some r) := by
  intro hinv ht h
  obtain ⟨_, _, h3, h4⟩ := hinv
  have hrep : ∀ c, sptLookup c cs.fromEq ≠ some t := by
    intro c hc; have := h4 c t hc; rw [ht] at this; cases this
  unfold lookupStoreEq at h ⊢
  rw [setEqStoreToEq] at h
  cases hs : cs.storeToEq.lookup v with
  | none => rw [hs] at h; cases h
  | some c =>
  rw [hs] at h
  simp only at h ⊢
  have hcn := h3 v c hs
  by_cases hb : bothAllocVars (t, s)
  · rw [setEq_both hb] at h
    cases hcl : liveClass cs s with
    | none =>
        rw [hcl] at h
        simp only [sptLookupInsert, if_neg (show c ≠ cs.next by omega)] at h
        cases hf : sptLookup c cs.fromEq with
        | none => rw [hf] at h; cases h
        | some r' =>
            rw [hf] at h; cases h
            exact ⟨fun hr => absurd (hr ▸ hf) (hrep c), fun _ => rfl⟩
    | some c0 =>
        obtain ⟨hsc, hfrom⟩ := liveClass_some.mp hcl
        rw [hcl] at h
        simp only [sptLookupInsert] at h
        by_cases hcc : c = c0
        · subst hcc
          simp only [if_true] at h
          cases h
          refine ⟨fun _ => ?_, fun hr => absurd rfl hr⟩
          cases hr : sptLookup c cs.fromEq with
          | none => exact absurd hr hfrom
          | some r' => simp only; rw [lookupEqI cs r' s (Or.inr ⟨c, hsc, hr⟩)]
        · simp only [if_neg hcc] at h
          cases hf : sptLookup c cs.fromEq with
          | none => rw [hf] at h; cases h
          | some r' =>
              rw [hf] at h; cases h
              exact ⟨fun hr => absurd (hr ▸ hf) (hrep c), fun _ => rfl⟩
  · rw [setEq_eq, if_neg (show ¬(isAllocVar t = true ∧ isAllocVar s = true) from hb)] at h
    cases hf : sptLookup c cs.fromEq with
    | none => rw [hf] at h; cases h
    | some r' =>
        rw [hf] at h; cases h
        exact ⟨fun hr => absurd (hr ▸ hf) (hrep c), fun _ => rfl⟩

end Flapjack.Compiler.Backend.WordCopy
