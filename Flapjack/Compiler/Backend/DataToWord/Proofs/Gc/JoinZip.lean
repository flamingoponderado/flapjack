module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LocMerge

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "join_env_EQ_ZIP"
  (words_as_type_indexed_bitvec) (total_function_inhabitants := [β])]
theorem joinEnv_eq_zip {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (vs : List (Nat × WordLocW width)) (s : Spt β) (zs : List (WordLocW width))
    (h : (∀ p ∈ vs, p.1 ≠ 0 ∧ p.1 % 2 = 0) ∧ (joinEnv s vs).length = zs.length ∧
      ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
        (wordSemIsWordLoc x = false → x = y)) ((joinEnv s vs).map Prod.snd) zs) :
    joinEnv s (List.zip (vs.map Prod.fst) (locMerge (vs.map Prod.snd) (zs.filter wordSemIsWordLoc))) =
      List.zip ((joinEnv s vs).map Prod.fst) zs := by
  induction vs generalizing zs with
  | nil =>
    have hz : zs = [] := by simpa [joinEnv_nil] using h.2.1.symm
    subst zs
    simp [joinEnv_nil, locMerge]
  | cons p vs ih =>
    rcases p with ⟨n, v⟩
    have hn : n ≠ 0 ∧ n % 2 = 0 := h.1 (n,v) (by simp)
    have ht : ∀ p ∈ vs, p.1 ≠ 0 ∧ p.1 % 2 = 0 := by
      intro p hp; exact h.1 p (by simp [hp])
    rw [joinEnv_cons, if_pos hn] at h
    simp only [List.length_cons, List.map_cons] at h
    cases zs with
    | nil => simp at h
    | cons z zs =>
      cases h.2.2 with
      | cons hr hrel =>
        have htail : (∀ p ∈ vs, p.1 ≠ 0 ∧ p.1 % 2 = 0) ∧
            (joinEnv s vs).length = zs.length ∧
            ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
              (wordSemIsWordLoc x = false → x = y)) ((joinEnv s vs).map Prod.snd) zs := by
          exact ⟨ht, Nat.succ.inj h.2.1, hrel⟩
        have hind := ih zs htail
        cases v with
        | word w =>
          cases z with
          | loc a b => simp [wordSemIsWordLoc] at hr
          | word z =>
            simp only [List.map_cons, List.filter_cons, wordSemIsWordLoc, ↓reduceIte, locMerge, List.zip_cons_cons, joinEnv_cons, if_pos hn]
            rw [hind]
        | loc a b =>
          have hz : z = .loc a b := (hr.2 rfl).symm
          subst z
          simp only [List.map_cons, List.filter_cons, wordSemIsWordLoc, Bool.false_eq_true, ↓reduceIte, locMerge, List.zip_cons_cons, joinEnv_cons, if_pos hn]
          rw [hind]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "LENGTH_MAP_SND_join_env_IMP"
  (words_as_type_indexed_bitvec) (total_function_inhabitants := [β])]
theorem length_filter_snd_joinEnv_imp {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (vs : List (Nat × WordLocW width)) (zs : List (WordLocW width)) (s : Spt β)
    (h : ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
        (wordSemIsWordLoc x = false → x = y)) ((joinEnv s vs).map Prod.snd) zs ∧
      (∀ p ∈ vs, p.1 ≠ 0 ∧ p.1 % 2 = 0) ∧ (joinEnv s vs).length = zs.length) :
    ((vs.map Prod.snd).filter wordSemIsWordLoc).length = (zs.filter wordSemIsWordLoc).length := by
  induction vs generalizing zs with
  | nil =>
    have hz : zs = [] := by simpa [joinEnv_nil] using h.2.2.symm
    subst zs
    rfl
  | cons p vs ih =>
    rcases p with ⟨n, v⟩
    have hn : n ≠ 0 ∧ n % 2 = 0 := h.2.1 (n,v) (by simp)
    have ht : ∀ p ∈ vs, p.1 ≠ 0 ∧ p.1 % 2 = 0 := by
      intro p hp; exact h.2.1 p (by simp [hp])
    rw [joinEnv_cons, if_pos hn] at h
    simp only [List.length_cons, List.map_cons] at h
    cases zs with
    | nil => cases h.1
    | cons z zs =>
      cases h.1 with
      | cons hr hrel =>
        have htail : ListRel (fun x y => (wordSemIsWordLoc x = wordSemIsWordLoc y) ∧
              (wordSemIsWordLoc x = false → x = y)) ((joinEnv s vs).map Prod.snd) zs ∧
            (∀ p ∈ vs, p.1 ≠ 0 ∧ p.1 % 2 = 0) ∧ (joinEnv s vs).length = zs.length :=
          ⟨hrel, ht, Nat.succ.inj h.2.2⟩
        have hind := ih zs htail
        simp only [List.map_cons, List.filter_cons]
        rw [hr.1]
        split <;> simp_all

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "lemma1"]
theorem lemma1 {α β γ : Type} (y1 y2 : α) (x1 x2 : β) (f : β → α → γ)
    (h : y1 = y2 ∧ x1 = x2) : f x1 y1 = f x2 y2 := by
  obtain ⟨rfl, rfl⟩ := h
  rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
