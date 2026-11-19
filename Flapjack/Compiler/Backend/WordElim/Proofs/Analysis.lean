module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Definitions
public import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

@[expose] public section

/-!
# Analysis lemmas of HOL `word_elimProof`

Counterpart of `cakeml/compiler/backend/proofs/word_elimProofScript.sml:17-40`:
`lookup_analyse_word_code`, `remove_word_code_thm`,
`remove_word_code_thm_FST` and `remove_word_code_MAP_FST_lemma`.

HOL's `ALOOKUP` is `holAlookup`, `ALL_DISTINCT` is `List.Nodup` and
`MAP FST` is `List.map Prod.fst`.
-/

namespace Flapjack.Compiler.Backend.WordElim

open Flapjack.Compiler.Backend.FlatElim

/-- Exact HOL `lookup_analyse_word_code`
    (`word_elimProofScript.sml:17-23`): an entry found by `ALOOKUP` is found by
    `lookup` in the analysed dependency map. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "lookup_analyse_word_code"]
theorem lookupAnalyseWordCode {α β : Type} (code : List (Nat × α × WordLangProgHOL β))
    (n : Nat) (arity : α) (prog : WordLangProgHOL β)
    (found : holAlookup code n = some (arity, prog)) :
    sptLookup n (analyseWordCode code) = some (findWordRef prog) := by
  induction code with
  | nil => simp [holAlookup] at found
  | cons head rest ih =>
      obtain ⟨key, arity', prog'⟩ := head
      simp only [holAlookup, analyseWordCode] at found ⊢
      by_cases h : key = n
      · rw [if_pos h] at found
        obtain ⟨rfl, rfl⟩ := Option.some.inj found
        rw [← h]
        exact sptLookup_sptInsert_same key (findWordRef prog) (analyseWordCode rest)
      · rw [if_neg h] at found
        rw [sptLookup_sptInsert_ne key n (findWordRef prog') (analyseWordCode rest)
          (fun hnk => h hnk.symm)]
        exact ih found

/-- Exact HOL `remove_word_code_thm` (`word_elimProofScript.sml:25-39`): under
    distinct labels, an entry is kept exactly when its label is reachable. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "remove_word_code_thm"]
theorem removeWordCode_thm {α : Type} (n : Nat) (reachable : NumSet) (l : List (Nat × α))
    (_distinct : (l.map Prod.fst).Nodup) (v : α) :
    (sptMem n reachable ∧ (n, v) ∈ l) ↔ (n, v) ∈ removeWordCode reachable l := by
  constructor
  · rintro ⟨mem, hmem⟩
    refine List.mem_filter.mpr ⟨hmem, ?_⟩
    obtain ⟨u, hlookup⟩ := (sptMem_iff_lookup n reachable).mp mem
    simp [hlookup]
  · intro hmem
    obtain ⟨hmem, keep⟩ := List.mem_filter.mp hmem
    exact ⟨(sptMem_iff_lookup n reachable).mpr (Option.isSome_iff_exists.mp keep), hmem⟩

/-- Exact HOL `remove_word_code_MAP_FST_lemma`
    (`word_elimProofScript.sml:524-530`): mapping `FST` after the filter equals
    filtering the mapped labels. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml"
  "remove_word_code_MAP_FST_lemma"]
theorem removeWordCode_MAP_FST_lemma {α : Type}
    (reachable : NumSet) (l : List (Nat × Nat × WordLangProgHOL α)) :
    (removeWordCode reachable l).map Prod.fst =
      (l.map Prod.fst).filter (fun key => (sptLookup key reachable).isSome) := by
  induction l with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨key, arity, prog⟩ := head
      simp only [removeWordCode, List.filter_cons, List.map_cons] at ih ⊢
      split <;> simp [ih]

/-- Exact HOL `remove_word_code_thm_FST` (`word_elimProofScript.sml:510-522`):
    the label-level form of `remove_word_code_thm`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "remove_word_code_thm_FST"]
theorem removeWordCode_thm_FST {α : Type} (n : Nat) (reachable : NumSet) (l : List (Nat × α))
    (distinct : (l.map Prod.fst).Nodup) :
    (sptMem n reachable ∧ n ∈ l.map Prod.fst) ↔
      n ∈ (removeWordCode reachable l).map Prod.fst := by
  constructor
  · rintro ⟨mem, hmem⟩
    obtain ⟨entry, hentry, hfst⟩ := List.mem_map.mp hmem
    obtain ⟨key, v⟩ := entry
    have hkey : key = n := hfst
    rw [hkey] at hentry
    exact List.mem_map.mpr
      ⟨(n, v), (removeWordCode_thm n reachable l distinct v).mp ⟨mem, hentry⟩, rfl⟩
  · intro hmem
    obtain ⟨entry, hentry, hfst⟩ := List.mem_map.mp hmem
    obtain ⟨key, v⟩ := entry
    have hkey : key = n := hfst
    rw [hkey] at hentry
    obtain ⟨mem, hmem⟩ := (removeWordCode_thm n reachable l distinct v).mpr hentry
    exact ⟨mem, List.mem_map.mpr ⟨(n, v), hmem, rfl⟩⟩

end Flapjack.Compiler.Backend.WordElim
