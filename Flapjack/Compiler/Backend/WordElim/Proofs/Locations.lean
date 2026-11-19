module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Analysis
public import Flapjack.Misc.Sptree.UnionAlgebra
public import Flapjack.Misc.Sptree.FromList2
public import Mathlib.Data.Set.Defs

@[expose] public section

/-!
# Location-set lemmas of HOL `word_elimProof`

Counterpart of `cakeml/compiler/backend/proofs/word_elimProofScript.sml:72-203`
and `:438-462`: the `get_locals`, `get_num_wordloc_alist` and `fromList2`
domain lemmas.  HOL's `domain t` is the reviewed `sptDomain`
(`Flapjack/Misc/Sptree.lean`); `sptDomainSet` is the same predicate at
Mathlib's `Set` carrier so HOL's `SUBSET`/`UNION` notation is stated literally
(`A ⊆ B ∪ {n}`).  Membership statements keep `sptMem`, which is definitionally
`sptDomain t key`.

The untagged helpers below are Flapjack infrastructure with no separate HOL
original: `sptDomainSet` (the `Set` carrier bridge), the
`getLocals`/`destWordLoc` clause equations, `destWordLoc_eq_some_iff`
for the `Loc` clause, `sptMem_foldl_sptInsert` for the left fold used by
`get_num_wordloc_alist`, and the `sptLookup_exists_*` lemmas that move an
existential lookup through the `BN`/`BS` key arithmetic.
-/

namespace Flapjack.Compiler.Backend.WordElim

open Flapjack.Compiler.Backend.FlatElim

/-- Flapjack-only bridge: the reviewed `sptDomain` predicate at Mathlib's
    `Set` carrier, so the source's `⊆`/`∪` notation applies unchanged. -/
def sptDomainSet {α : Type} (tree : Spt α) : Set Nat := sptDomain tree

/-- Flapjack-only helper: `dest_word_loc` on a `Word`. -/
@[simp] theorem destWordLoc_word {width : Nat} [NeZero width] (value : BitVec width) :
    destWordLoc (.word value : WordLocW width) = none := rfl

/-- Flapjack-only helper: `dest_word_loc` on a `Loc`. -/
@[simp] theorem destWordLoc_loc {width : Nat} [NeZero width] (block offset : Nat) :
    destWordLoc (.loc block offset : WordLocW width) = some block := rfl

/-- Flapjack-only helper: `dest_word_loc` succeeds exactly on `Loc` values. -/
theorem destWordLoc_eq_some_iff {width : Nat} [NeZero width] (value : WordLocW width)
    (location : Nat) :
    destWordLoc value = some location ↔ ∃ offset, value = .loc location offset := by
  cases value with
  | word w => simp
  | loc block offset =>
      simp only [destWordLoc_loc, Option.some.injEq]
      constructor
      · intro h
        exact ⟨offset, by rw [h]⟩
      · rintro ⟨other, h⟩
        injection h with hblock _

/-- Flapjack-only helper: the `getLocals` clauses as equations. -/
@[simp] theorem getLocals_ln {width : Nat} [NeZero width] :
    getLocals (.ln : Spt (WordLocW width)) = .ln := rfl

@[simp] theorem getLocals_ls_word {width : Nat} [NeZero width] (value : BitVec width) :
    getLocals (.ls (.word value) : Spt (WordLocW width)) = .ln := rfl

@[simp] theorem getLocals_ls_loc {width : Nat} [NeZero width] (block offset : Nat) :
    getLocals (.ls (.loc block offset) : Spt (WordLocW width)) =
      sptInsert block () .ln := rfl

@[simp] theorem getLocals_bn {width : Nat} [NeZero width]
    (left right : Spt (WordLocW width)) :
    getLocals (.bn left right) = sptUnion (getLocals left) (getLocals right) := rfl

@[simp] theorem getLocals_bs_word {width : Nat} [NeZero width]
    (left : Spt (WordLocW width)) (value : BitVec width) (right : Spt (WordLocW width)) :
    getLocals (.bs left (.word value) right) = sptUnion (getLocals left) (getLocals right) := rfl

@[simp] theorem getLocals_bs_loc {width : Nat} [NeZero width]
    (left : Spt (WordLocW width)) (block offset : Nat) (right : Spt (WordLocW width)) :
    getLocals (.bs left (.loc block offset) right) =
      sptInsert block () (sptUnion (getLocals left) (getLocals right)) := rfl

/-- Flapjack-only helper: membership in the left fold of single insertions. -/
theorem sptMem_foldl_sptInsert (locations : List Nat) (key : Nat) (tree : Spt Unit) :
    sptMem key (locations.foldl (fun accumulator location => sptInsert location () accumulator)
      tree) ↔ key ∈ locations ∨ sptMem key tree := by
  induction locations generalizing tree with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih, sptMem_sptInsert]
      simp only [List.mem_cons]
      tauto

/-- Flapjack-only helper: an existential `Loc` lookup in a `BN` node is an
    existential lookup in one of the children (the key arithmetic
    `k = 2 * m + 2` / `k = 2 * m + 1` inverts `(k - 1) / 2`). -/
theorem sptLookup_exists_bn {width : Nat} [NeZero width] (left right : Spt (WordLocW width))
    (location : Nat) :
    (∃ key offset, sptLookup key (.bn left right) = some (.loc location offset)) ↔
      (∃ key offset, sptLookup key left = some (.loc location offset)) ∨
        ∃ key offset, sptLookup key right = some (.loc location offset) := by
  constructor
  · rintro ⟨key, offset, hkey⟩
    by_cases hzero : key = 0
    · rw [hzero, sptLookup] at hkey
      simp at hkey
    · rw [sptLookup, if_neg hzero] at hkey
      by_cases heven : key % 2 = 0
      · left
        exact ⟨(key - 1) / 2, offset, by simpa [heven] using hkey⟩
      · right
        exact ⟨(key - 1) / 2, offset, by simpa [heven] using hkey⟩
  · rintro (⟨key, offset, hkey⟩ | ⟨key, offset, hkey⟩)
    · refine ⟨2 * key + 2, offset, ?_⟩
      rw [sptLookup]
      simp only [if_neg (by omega : ¬ 2 * key + 2 = 0),
        if_pos (by omega : (2 * key + 2) % 2 = 0)]
      rw [show (2 * key + 2 - 1) / 2 = key by omega]
      exact hkey
    · refine ⟨2 * key + 1, offset, ?_⟩
      rw [sptLookup]
      simp only [if_neg (by omega : ¬ 2 * key + 1 = 0),
        if_neg (by omega : ¬(2 * key + 1) % 2 = 0)]
      rw [show (2 * key + 1 - 1) / 2 = key by omega]
      exact hkey

/-- Flapjack-only helper: the `BS` analogue of `sptLookup_exists_bn`, adding
    the node's own payload at key `0`. -/
theorem sptLookup_exists_bs {width : Nat} [NeZero width] (left : Spt (WordLocW width))
    (middle : WordLocW width) (right : Spt (WordLocW width)) (location : Nat) :
    (∃ key offset, sptLookup key (.bs left middle right) = some (.loc location offset)) ↔
      (∃ offset, middle = .loc location offset) ∨
        (∃ key offset, sptLookup key left = some (.loc location offset)) ∨
          ∃ key offset, sptLookup key right = some (.loc location offset) := by
  constructor
  · rintro ⟨key, offset, hkey⟩
    by_cases hzero : key = 0
    · left
      rw [hzero, sptLookup] at hkey
      exact ⟨offset, by simpa using hkey⟩
    · rw [sptLookup, if_neg hzero] at hkey
      by_cases heven : key % 2 = 0
      · right; left
        exact ⟨(key - 1) / 2, offset, by simpa [heven] using hkey⟩
      · right; right
        exact ⟨(key - 1) / 2, offset, by simpa [heven] using hkey⟩
  · rintro (⟨offset, hvalue⟩ | ⟨key, offset, hkey⟩ | ⟨key, offset, hkey⟩)
    · exact ⟨0, offset, by rw [sptLookup]; simpa using hvalue⟩
    · refine ⟨2 * key + 2, offset, ?_⟩
      rw [sptLookup]
      simp only [if_neg (by omega : ¬ 2 * key + 2 = 0),
        if_pos (by omega : (2 * key + 2) % 2 = 0)]
      rw [show (2 * key + 2 - 1) / 2 = key by omega]
      exact hkey
    · refine ⟨2 * key + 1, offset, ?_⟩
      rw [sptLookup]
      simp only [if_neg (by omega : ¬ 2 * key + 1 = 0),
        if_neg (by omega : ¬(2 * key + 1) % 2 = 0)]
      rw [show (2 * key + 1 - 1) / 2 = key by omega]
      exact hkey

/-- Exact HOL `domain_get_locals_lookup` (`word_elimProofScript.sml:72-103`):
    a location is in `get_locals` exactly when the tree stores a `Loc` with
    that block. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "domain_get_locals_lookup"
  (words_as_type_indexed_bitvec)]
theorem domainGetLocalsLookup {width : Nat} [NeZero width] (location : Nat)
    (tree : Spt (WordLocW width)) :
    sptMem location (getLocals tree) ↔
      ∃ key offset, sptLookup key tree = some (.loc location offset) := by
  induction tree with
  | ln => simp
  | ls value =>
      cases value with
      | word w =>
          simp only [getLocals_ls_word, sptMem_ln]
          constructor
          · intro h
            exact absurd h (by simp)
          · rintro ⟨key, other, hkey⟩
            simp only [sptLookup] at hkey
            split at hkey <;> simp at hkey
      | loc block offset =>
          simp only [getLocals_ls_loc, sptMem_sptInsert, sptMem_ln, sptLookup, or_false]
          constructor
          · rintro rfl
            exact ⟨0, offset, rfl⟩
          · rintro ⟨key, other, hkey⟩
            by_cases hzero : key = 0
            · rw [hzero] at hkey
              simp only [if_true] at hkey
              have hloc : (.loc block offset : WordLocW width) = .loc location other :=
                Option.some.inj hkey
              injection hloc with hblock _
              exact hblock.symm
            · rw [if_neg hzero] at hkey
              simp at hkey
  | bn left right ih_left ih_right =>
      rw [getLocals_bn, sptMem_sptUnion, sptLookup_exists_bn]
      exact or_congr ih_left ih_right
  | bs left value right ih_left ih_right =>
      cases value with
      | word w =>
          simp only [getLocals_bs_word, sptMem_sptUnion, sptLookup_exists_bs]
          constructor
          · rintro (hmem | hmem)
            · exact Or.inr (Or.inl (ih_left.mp hmem))
            · exact Or.inr (Or.inr (ih_right.mp hmem))
          · rintro (⟨offset, hvalue⟩ | hl | hr)
            · simp at hvalue
            · exact Or.inl (ih_left.mpr hl)
            · exact Or.inr (ih_right.mpr hr)
      | loc block offset =>
          simp only [getLocals_bs_loc, sptMem_sptInsert, sptMem_sptUnion,
            sptLookup_exists_bs]
          constructor
          · rintro (rfl | hmem | hmem)
            · exact Or.inl ⟨offset, rfl⟩
            · exact Or.inr (Or.inl (ih_left.mp hmem))
            · exact Or.inr (Or.inr (ih_right.mp hmem))
          · rintro (⟨other, hvalue⟩ | hl | hr)
            · injection hvalue with hblock _
              exact Or.inl hblock.symm
            · exact Or.inr (Or.inl (ih_left.mpr hl))
            · exact Or.inr (Or.inr (ih_right.mpr hr))

/-- Flapjack-only helper: appending one element inserts its value at the next
    even index. -/
theorem sptFromList2_append_singleton {α : Type} (values : List α) (value : α) :
    sptFromList2 (values ++ [value]) =
      sptInsert (2 * values.length) value (sptFromList2 values) := by
  simp only [sptFromList2, List.foldl_append, List.foldl_cons, List.foldl_nil,
    sptFromList2FoldIndex, Nat.zero_add]

/-- Exact HOL `get_locals_insert_Loc` (`word_elimProofScript.sml:105-114`):
    inserting a `Loc` adds at most its block. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_locals_insert_Loc"
  (words_as_type_indexed_bitvec)]
theorem getLocals_insert_Loc {width : Nat} [NeZero width] (k n1 n0 : Nat)
    (locals : Spt (WordLocW width)) :
    sptDomainSet (getLocals (sptInsert k (.loc n1 n0) locals)) ⊆
      sptDomainSet (getLocals locals) ∪ ({n1} : Set Nat) := by
  intro location hmem
  obtain ⟨found, other, hkey⟩ :=
    (domainGetLocalsLookup location (sptInsert k (.loc n1 n0) locals)).mp hmem
  by_cases hsame : found = k
  · rw [hsame, sptLookup_sptInsert_same] at hkey
    have hinj := Option.some.inj hkey
    injection hinj with hblock _
    exact Or.inr hblock.symm
  · rw [sptLookup_sptInsert_ne k found (.loc n1 n0) locals hsame] at hkey
    exact Or.inl ((domainGetLocalsLookup location locals).mpr ⟨found, other, hkey⟩)

/-- Exact HOL `get_locals_insert` (`word_elimProofScript.sml:116-128`):
    inserting a value adds at most its own block. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_locals_insert"
  (words_as_type_indexed_bitvec)]
theorem getLocals_insert {width : Nat} [NeZero width] (k : Nat) (v : WordLocW width)
    (locals : Spt (WordLocW width)) :
    sptDomainSet (getLocals (sptInsert k v locals)) ⊆
      sptDomainSet (getLocals locals) ∪
        (match destWordLoc v with | none => (∅ : Set Nat) | some n => ({n} : Set Nat)) := by
  cases v with
  | word w =>
      intro location hmem
      obtain ⟨found, other, hkey⟩ :=
        (domainGetLocalsLookup location (sptInsert k (.word w) locals)).mp hmem
      by_cases hsame : found = k
      · rw [hsame, sptLookup_sptInsert_same] at hkey
        simp at hkey
      · rw [sptLookup_sptInsert_ne k found (.word w) locals hsame] at hkey
        exact Or.inl ((domainGetLocalsLookup location locals).mpr ⟨found, other, hkey⟩)
  | loc block offset =>
      intro location hmem
      simp only [destWordLoc_loc, Set.mem_union, Set.mem_singleton_iff]
      obtain ⟨found, other, hkey⟩ :=
        (domainGetLocalsLookup location (sptInsert k (.loc block offset) locals)).mp hmem
      by_cases hsame : found = k
      · rw [hsame, sptLookup_sptInsert_same] at hkey
        have hinj := Option.some.inj hkey
        injection hinj with hblock _
        exact Or.inr hblock.symm
      · rw [sptLookup_sptInsert_ne k found (.loc block offset) locals hsame] at hkey
        exact Or.inl ((domainGetLocalsLookup location locals).mpr ⟨found, other, hkey⟩)

/-- Flapjack-only helper: membership in the filtered `Loc` list of an
    association list, as an existential over the stored offsets. -/
theorem mem_filterMap_destWordLoc {width : Nat} [NeZero width] :
    ∀ (entries : List (Nat × WordLocW width)) (location : Nat),
      location ∈ entries.filterMap (fun entry => destWordLoc entry.2) ↔
        ∃ offset, (.loc location offset) ∈ entries.map Prod.snd := by
  intro entries
  induction entries with
  | nil => intro location; simp
  | cons head rest ih =>
      intro location
      obtain ⟨key, value⟩ := head
      cases value with
      | word w =>
          simp only [List.map_cons, List.filterMap_cons, destWordLoc_word, List.mem_cons]
          constructor
          · intro h
            obtain ⟨offset, hoffset⟩ := (ih location).mp h
            exact ⟨offset, Or.inr hoffset⟩
          · rintro ⟨offset, h | h⟩
            · exact absurd h (by simp)
            · exact (ih location).mpr ⟨offset, h⟩
      | loc block offset =>
          simp only [List.map_cons, List.filterMap_cons, destWordLoc_loc, List.mem_cons]
          rw [ih location]
          constructor
          · rintro (rfl | ⟨other, h⟩)
            · exact ⟨offset, Or.inl rfl⟩
            · exact ⟨other, Or.inr h⟩
          · rintro ⟨other, hvalue | h⟩
            · left
              injection hvalue with hloc _
            · right
              exact ⟨other, h⟩

/-- Exact HOL `get_num_wordloc_alist_thm` (`word_elimProofScript.sml:166-176`):
    the association list's `Loc` blocks are exactly the collected locations.
    HOL's `e` is unused and keeps an independent type. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml"
  "get_num_wordloc_alist_thm" (words_as_type_indexed_bitvec)]
theorem getNumWordlocAlist_thm {width : Nat} [NeZero width] {α : Type} (location : Nat)
    (_e : α) (entries : List (Nat × WordLocW width)) :
    (∃ offset, (.loc location offset) ∈ entries.map Prod.snd) ↔
      sptMem location (getNumWordlocAlist entries) := by
  simp only [getNumWordlocAlist, sptMem_foldl_sptInsert]
  constructor
  · rintro ⟨offset, hmem⟩
    exact Or.inl ((mem_filterMap_destWordLoc entries location).mpr ⟨offset, hmem⟩)
  · rintro (hmem | hmem)
    · exact (mem_filterMap_destWordLoc entries location).mp hmem
    · exact absurd hmem (by simp)

/-- Exact HOL `get_num_wordloc_alist_get_locals`
    (`word_elimProofScript.sml:178-191`): `fromAList`'s locals are inside the
    association list's collected locations. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml"
  "get_num_wordloc_alist_get_locals" (words_as_type_indexed_bitvec)]
theorem getNumWordlocAlist_get_locals {width : Nat} [NeZero width]
    (e : List (Nat × WordLocW width)) :
    sptDomainSet (getLocals (sptFromAList e)) ⊆ sptDomainSet (getNumWordlocAlist e) := by
  intro location hmem
  obtain ⟨key, offset, hkey⟩ := (domainGetLocalsLookup location (sptFromAList e)).mp hmem
  rw [sptLookup_sptFromAList] at hkey
  have hentry := sptAListLookup_mem key e (.loc location offset) hkey
  exact (getNumWordlocAlist_thm (α := Unit) location () e).mp
    ⟨offset, List.mem_map.mpr ⟨(key, .loc location offset), hentry, rfl⟩⟩

/-- Exact HOL `get_locals_union_subset` (`word_elimProofScript.sml:193-201`):
    the locations of a union are inside the union of the location sets. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml"
  "get_locals_union_subset" (words_as_type_indexed_bitvec)]
theorem getLocals_union_subset {width : Nat} [NeZero width]
    (A B : Spt (WordLocW width)) :
    sptDomainSet (getLocals (sptUnion A B)) ⊆
      sptDomainSet (sptUnion (getLocals A) (getLocals B)) := by
  intro location hmem
  obtain ⟨key, offset, hkey⟩ :=
    (domainGetLocalsLookup location (sptUnion A B)).mp hmem
  rw [sptLookup_sptUnion] at hkey
  change sptMem location (sptUnion (getLocals A) (getLocals B))
  rw [sptMem_sptUnion]
  cases hfirst : sptLookup key A with
  | none =>
      rw [hfirst] at hkey
      exact Or.inr ((domainGetLocalsLookup location B).mpr ⟨key, offset, hkey⟩)
  | some value =>
      rw [hfirst] at hkey
      have hval := Option.some.inj hkey
      rw [hval] at hfirst
      exact Or.inl ((domainGetLocalsLookup location A).mpr ⟨key, offset, hfirst⟩)

/-- Exact HOL `get_locals_fromList2_extension`
    (`word_elimProofScript.sml:448-462`): appending one value keeps every
    existing `fromList2` location. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml"
  "get_locals_fromList2_extension" (words_as_type_indexed_bitvec)]
theorem getLocals_fromList2_extension {width : Nat} [NeZero width] (location : Nat)
    (value : WordLocW width) (values : List (WordLocW width)) :
    sptMem location (getLocals (sptFromList2 values)) →
      sptMem location (getLocals (sptFromList2 (values ++ [value]))) := by
  intro hmem
  obtain ⟨key, offset, hkey⟩ :=
    (domainGetLocalsLookup location (sptFromList2 values)).mp hmem
  have hmember : key ∈ (List.range values.length).map (fun index => 2 * index) := by
    have hdom : sptDomain (sptFromList2 values) key :=
      (sptDomain_iff_lookup (sptFromList2 values) key).mpr ⟨.loc location offset, hkey⟩
    simpa [sptDomainFromList2 values] using hdom
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hmember
  have hsmall : 2 * index < 2 * values.length := by
    have := List.mem_range.mp hindex
    omega
  refine (domainGetLocalsLookup location (sptFromList2 (values ++ [value]))).mpr
    ⟨2 * index, offset, ?_⟩
  rw [sptFromList2_append_singleton,
    sptLookup_sptInsert_ne (2 * values.length) (2 * index) value (sptFromList2 values)
      (by omega)]
  exact hkey

/-- Exact HOL `get_locals_inter_subset` (`word_elimProofScript.sml:924-930`):
    intersecting a locals tree with another tree keeps only the locations of
    the left tree.  HOL marks it `[local]` and writes it
    `domain (get_locals (inter a b)) ⊆ domain (get_locals a)`; the right tree's
    payload type is independent, as in the typed capture. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_locals_inter_subset"
  (words_as_type_indexed_bitvec)]
theorem getLocals_inter_subset {width : Nat} [NeZero width] {β : Type}
    (a : Spt (WordLocW width)) (b : Spt β) :
    sptDomainSet (getLocals (sptInter a b)) ⊆ sptDomainSet (getLocals a) := by
  intro location hmem
  obtain ⟨key, offset, hkey⟩ :=
    (domainGetLocalsLookup location (sptInter a b)).mp hmem
  rw [sptLookup_sptInterCases] at hkey
  cases hleft : sptLookup key a with
  | none =>
      cases hright : sptLookup key b with
      | none =>
          rw [hleft, hright] at hkey
          simp at hkey
      | some other =>
          rw [hleft, hright] at hkey
          simp at hkey
  | some value =>
      cases hright : sptLookup key b with
      | none =>
          rw [hleft, hright] at hkey
          simp at hkey
      | some other =>
          rw [hleft, hright] at hkey
          simp only [Option.some.injEq] at hkey
          exact (domainGetLocalsLookup location a).mpr
            ⟨key, offset, by rw [hleft]; exact congrArg some hkey⟩

end Flapjack.Compiler.Backend.WordElim
