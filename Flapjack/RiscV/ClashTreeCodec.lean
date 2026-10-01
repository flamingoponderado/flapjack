import Flapjack.RiscV.Allocator
import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Misc.SptreeLookup
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EnvFrame
import Mathlib.Data.List.Nodup

set_option maxHeartbeats 1000000

/-!
# Codec between the executed `WordClashTree` and the reviewed `RegAlloc.ClashTree`

The executed RISC-V allocator builds its own clash tree
(`Flapjack.WordClashTree`, `Flapjack/RiscV/Allocator.lean`) whose `set`/`branch`
payloads are `List Nat`, and checks it with `wordClashTreeCheck` /
`wordCheckColour` / `wordCheckPartialColour`.  The reviewed proof-side carrier
(`Flapjack.RegAlloc.ClashTree`) stores those payloads as `NumSet` (`= Spt Unit`)
and is checked by `checkClashTree` / `checkCol` / `checkPartialCol`
(`Flapjack/Compiler/Backend/RegAlloc/ClashTree.lean`, tagged against HOL
`reg_allocScript.sml`).

This module is Flapjack-internal representation infrastructure: it ports no HOL
declaration, so it carries no `@[hol]` tag.  It provides

* `wordClashTreeToReviewed` / `reviewedToWordClashTree`, a codec between the two
  carriers (the `List Nat` payload is mapped through the set codec
  `listToNumSet` / `numSetToList`);
* roundtrip laws on the precisely stated `CanonicalTree` / `ReviewedCanonical`
  fragments (the structural roundtrip) and unconditional domain-level
  roundtrips (`DomEq`);
* `wordClashTreeCheck_agrees`: the executed checker's `Option` result corresponds
  to the reviewed checker's `Option` result under the codec, including the
  domains of the returned live/coloured sets.

## Source comparison (executed vs reviewed checker)

`wordCheckColour`/`wordCheckPartialColour`/`wordClashTreeCheck` are the same
functions as the reviewed `checkCol`/`checkPartialCol`/`checkClashTree`
(clause for clause: `Delta` checks writes then deletes writes from both live sets
before adding reads; `Set`/`Branch.some` check the fixed set; `Branch.none`
checks the right-minus-left set on the left outputs; `Seq` checks right first).
The only difference is the representation of a set:

* the executed live/coloured sets are `List Nat`; the reviewed ones are
  `NumSet = Spt Unit`;
* the executed `set`/`branch.some` payloads are pre-deduplicated with
  `eraseDups` before `wordCheckColour`, while the reviewed carrier is already a
  set.  `checkCol`'s `ALL_DISTINCT` test and `wordCheckColour`'s `Nodup` test
  both reduce to injectivity of the colour on the underlying set, so the
  `eraseDups` step is representation normalisation, not a semantic difference.

`DomEq` (`∀ k, sptMem k t ↔ k ∈ l`) is the set-codec relation used below; it is
discharged for the executed callers' inputs (`[]` and the `listToNumSet` of a
payload) and preserved by every operation.
-/

namespace Flapjack.ClashTreeCodec

open Flapjack
open Flapjack.RegAlloc
open Flapjack.WordAlloc (sptToAListKeysNodup)

/-- The canonical `NumSet` built from a source list of names (last inserted
first, matching the reviewed checker's insertion convention for a list). -/
def listToNumSet (names : List Nat) : NumSet :=
  sptFromAList (names.map (fun name => (name, ())))

/-- The key enumeration of a `NumSet` in the exact HOL `toAList` order. -/
def numSetToList (tree : NumSet) : List Nat :=
  (sptToAList tree).map Prod.fst

/-- Set-codec relation: `tree` has exactly the members of `names`. -/
def DomEq (names : List Nat) (tree : NumSet) : Prop :=
  ∀ key, sptMem key tree ↔ key ∈ names

/-- A colouring is injective on a set of names. -/
def ColourInjectiveOn (colour : Nat → Nat) (tree : NumSet) : Prop :=
  ∀ left right, sptMem left tree → sptMem right tree →
    colour left = colour right → left = right

/-- The two checkers return corresponding results: both fail, or both succeed
with domain-equal live and coloured sets. -/
def CheckResultRel : Option (List Nat × List Nat) → Option (NumSet × NumSet) → Prop
  | some (names, coloured), some (namesSet, colouredSet) =>
      DomEq names namesSet ∧ DomEq coloured colouredSet
  | none, none => True
  | _, _ => False

/-! ## Basic set-codec laws -/

/-- Lookup in `listToNumSet` is membership in the source list. -/
theorem sptLookup_listToNumSet (key : Nat) (names : List Nat) :
    sptLookup key (listToNumSet names) = if key ∈ names then some () else none := by
  induction names with
  | nil => simp [listToNumSet, sptFromAList]
  | cons name rest ih =>
      have hunfold : listToNumSet (name :: rest) =
          sptInsert name () (listToNumSet rest) := by
        simp [listToNumSet, sptFromAList]
      rw [hunfold]
      by_cases h : key = name
      · subst h
        rw [sptLookup_sptInsert_same]
        simp
      · rw [sptLookup_sptInsert_ne name key () _ h, ih]
        simp only [List.mem_cons, h, false_or]

/-- Membership in `listToNumSet`. -/
theorem sptMem_listToNumSet (key : Nat) (names : List Nat) :
    sptMem key (listToNumSet names) ↔ key ∈ names := by
  unfold sptMem sptDomain
  rw [sptLookup_listToNumSet]
  by_cases h : key ∈ names <;> simp [h]

/-- Membership in `numSetToList`. -/
theorem mem_numSetToList (key : Nat) (tree : NumSet) :
    key ∈ numSetToList tree ↔ sptMem key tree := by
  unfold numSetToList
  rw [List.mem_map]
  constructor
  · rintro ⟨entry, hentry, hfst⟩
    obtain ⟨found, value⟩ := entry
    dsimp at hfst
    subst hfst
    exact (sptMem_iff_lookup found tree).mpr
      ⟨value, (sptToAList_mem_iff_lookup tree found value).mp hentry⟩
  · intro hmem
    obtain ⟨value, hlookup⟩ := (sptMem_iff_lookup key tree).mp hmem
    exact ⟨(key, value), (sptToAList_mem_iff_lookup tree key value).mpr hlookup, rfl⟩

/-- `numSetToList` enumerates exactly the domain of the tree. -/
theorem DomEq_numSetToList (tree : NumSet) : DomEq (numSetToList tree) tree := by
  intro key
  exact (mem_numSetToList key tree).symm

/-- `listToNumSet` has exactly the members of its source list. -/
theorem DomEq_listToNumSet (names : List Nat) : DomEq names (listToNumSet names) := by
  intro key
  exact sptMem_listToNumSet key names

/-- Deduplicating a payload does not change its member set. -/
theorem DomEq_eraseDups_listToNumSet (names : List Nat) :
    DomEq names.eraseDups (listToNumSet names) := by
  intro key
  rw [sptMem_listToNumSet, List.mem_eraseDups]

/-- `eraseDups` produces a duplicate-free list. -/
theorem nodup_eraseDups : ∀ (names : List Nat), names.eraseDups.Nodup
  | [] => by simp
  | name :: rest => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups (rest.filter (fun b => !b == name))⟩
      intro hmem
      rw [List.mem_eraseDups, List.mem_filter] at hmem
      obtain ⟨-, hb⟩ := hmem
      simp at hb
termination_by names => names.length
decreasing_by
  simp_wf
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-! ## `sptDelete` / `sptDifference` domain laws -/

/-- Membership after `sptDelete`. -/
theorem sptMem_sptDelete (key name : Nat) (tree : NumSet) :
    sptMem key (sptDelete name tree) ↔ sptMem key tree ∧ key ≠ name := by
  unfold sptMem sptDomain
  rw [sptLookup_sptDelete]
  by_cases h : key = name <;> simp [h]

/-- Membership after `numsetListDelete`. -/
theorem sptMem_numsetListDelete (names : List Nat) (tree : NumSet) (key : Nat) :
    sptMem key (numsetListDelete names tree) ↔ sptMem key tree ∧ key ∉ names := by
  induction names generalizing tree with
  | nil => simp [numsetListDelete]
  | cons name rest ih =>
      rw [numsetListDelete, ih, sptMem_sptDelete]
      simp only [List.mem_cons, not_or]
      tauto

/-- Lookup-level `sptDifference`; copied from the external HOL-library rendering
(`Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.sptLookup_sptDifference`)
to keep this module's imports free of the LoopToWord proof tree. -/
theorem sptLookup_sptDifference {α β : Type} :
    ∀ (t1 : Spt α) (t2 : Spt β) (k : Nat),
      sptLookup k (sptDifference t1 t2) =
        if (sptLookup k t2).isSome then none else sptLookup k t1
  | .ln, t2, k => by simp [sptDifference, sptLookup]
  | .ls v, t2, k => by
      cases t2 <;> simp only [sptDifference] <;>
        by_cases hk : k = 0 <;> simp [sptLookup, hk]
  | .bn l r, t2, k => by
      cases t2 with
      | ln => simp [sptDifference, sptLookup]
      | ls _ => simp only [sptDifference]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
      | bn l' r' =>
        simp only [sptDifference, sptLookup_sptMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptDifference l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptDifference r r']
      | bs l' _ r' =>
        simp only [sptDifference, sptLookup_sptMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptDifference l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptDifference r r']
  | .bs l v r, t2, k => by
      cases t2 with
      | ln => simp [sptDifference, sptLookup]
      | ls _ => simp only [sptDifference]; by_cases hk : k = 0 <;> simp [sptLookup, hk]
      | bn l' r' =>
        simp only [sptDifference, sptLookup_sptMkBS]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptDifference l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptDifference r r']
      | bs l' _ r' =>
        simp only [sptDifference, sptLookup_sptMkBN]
        by_cases hk : k = 0
        · simp [sptLookup, hk]
        · by_cases he : k % 2 = 0
          · simp only [sptLookup, hk, he, if_false, if_true, sptLookup_sptDifference l l']
          · simp only [sptLookup, hk, he, if_false, sptLookup_sptDifference r r']

/-- Membership after `sptDifference`. -/
theorem sptMem_sptDifference (left right : NumSet) (key : Nat) :
    sptMem key (sptDifference left right) ↔ sptMem key left ∧ ¬ sptMem key right := by
  simp only [sptMem_iff_lookup, sptLookup_sptDifference]
  cases sptLookup key right <;> cases sptLookup key left <;> simp

/-! ## Partial-colour agreement -/

/-- In a `NumSet`, `some ()` lookup is exactly membership. -/
theorem sptLookup_eq_some_unit_iff (key : Nat) (tree : NumSet) :
    sptLookup key tree = some () ↔ sptMem key tree := by
  unfold sptMem sptDomain
  cases h : sptLookup key tree with
  | none => simp
  | some value => cases value; simp

/-- `wordCheckPartialColour` corresponds to `checkPartialCol` on domain-equal
inputs. -/
theorem checkPartialCol_agrees (colour : Nat → Nat) :
    ∀ (names : List Nat) (live flive : List Nat) (liveS fliveS : NumSet),
      DomEq live liveS → DomEq flive fliveS →
      CheckResultRel (wordCheckPartialColour colour names live flive)
        (checkPartialCol colour names liveS fliveS) := by
  intro names
  induction names with
  | nil =>
      intro live flive liveS fliveS hlive hflive
      simp only [wordCheckPartialColour, checkPartialCol, CheckResultRel]
      exact ⟨hlive, hflive⟩
  | cons name rest ih =>
      intro live flive liveS fliveS hlive hflive
      by_cases hmem : name ∈ live
      · have hlookup : sptLookup name liveS = some () :=
          (sptLookup_eq_some_unit_iff name liveS).mpr ((hlive name).mpr hmem)
        simp only [wordCheckPartialColour, checkPartialCol, hmem, if_true, hlookup]
        exact ih live flive liveS fliveS hlive hflive
      · have hlookupNone : sptLookup name liveS = none := by
          cases h : sptLookup name liveS with
          | none => rfl
          | some value =>
              cases value
              exact absurd ((hlive name).mp ((sptLookup_eq_some_unit_iff name liveS).mp h)) hmem
        by_cases hcol : colour name ∈ flive
        · have hflookup : sptLookup (colour name) fliveS = some () :=
            (sptLookup_eq_some_unit_iff (colour name) fliveS).mpr
              ((hflive (colour name)).mpr hcol)
          simp only [wordCheckPartialColour, checkPartialCol, hmem, if_false,
            hcol, if_true, hlookupNone, hflookup, CheckResultRel]
        · have hflookupNone : sptLookup (colour name) fliveS = none := by
            cases h : sptLookup (colour name) fliveS with
            | none => rfl
            | some value =>
                cases value
                exact absurd ((hflive (colour name)).mp
                  ((sptLookup_eq_some_unit_iff (colour name) fliveS).mp h)) hcol
          simp only [wordCheckPartialColour, checkPartialCol, hmem, if_false,
            hcol, if_false, hlookupNone, hflookupNone]
          apply ih
          · intro key
            rw [sptMem_sptInsert, List.mem_cons]
            exact or_congr_right (hlive key)
          · intro key
            rw [sptMem_sptInsert, List.mem_cons]
            exact or_congr_right (hflive key)

/-! ## Fixed-set (`checkCol`) agreement -/

/-- `sptAListLookup` on unit-valued entries is exactly key membership. -/
theorem sptAListLookup_unit (key : Nat) :
    ∀ (entries : List (Nat × Unit)),
      sptAListLookup key entries = some () ↔ key ∈ entries.map Prod.fst
  | [] => by simp [sptAListLookup]
  | (entryKey, ()) :: rest => by
      simp only [sptAListLookup, List.map_cons, List.mem_cons]
      by_cases h : key = entryKey
      · subst h; simp
      · rw [if_neg h]
        rw [sptAListLookup_unit key rest]
        simp [h]

/-- The image `sptFromAList` produced by `checkCol`: its members are exactly the
colours of the tree's domain. -/
theorem mem_map_fst_toAList_map_unit (colour : Nat → Nat) (tree : NumSet) (key : Nat) :
    key ∈ ((sptToAList tree).map (fun entry => (colour entry.1, ()))).map Prod.fst ↔
      ∃ name, sptMem name tree ∧ colour name = key := by
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [List.mem_map]
  constructor
  · rintro ⟨entry, hentry, heq⟩
    obtain ⟨name, value⟩ := entry
    exact ⟨name, (sptMem_iff_lookup name tree).mpr
      ⟨value, (sptToAList_mem_iff_lookup tree name value).mp hentry⟩, heq⟩
  · rintro ⟨name, hmem, heq⟩
    obtain ⟨value, hlookup⟩ := (sptMem_iff_lookup name tree).mp hmem
    exact ⟨(name, value), (sptToAList_mem_iff_lookup tree name value).mpr hlookup, heq⟩

/-- The image `sptFromAList` produced by `checkCol`: its members are exactly the
colours of the tree's domain. -/
theorem sptMem_sptFromAList_map_unit (colour : Nat → Nat) (tree : NumSet) (key : Nat) :
    sptMem key (sptFromAList ((sptToAList tree).map (fun entry => (colour entry.1, ())))) ↔
      ∃ name, sptMem name tree ∧ colour name = key := by
  unfold sptMem sptDomain
  rw [sptLookup_sptFromAList, Option.isSome_iff_exists]
  constructor
  · rintro ⟨value, hlookup⟩
    cases value
    exact (mem_map_fst_toAList_map_unit colour tree key).mp
      ((sptAListLookup_unit key _).mp hlookup)
  · rintro h
    exact ⟨(), (sptAListLookup_unit key _).mpr
      ((mem_map_fst_toAList_map_unit colour tree key).mpr h)⟩

/-- `ColourInjectiveOn` on a `NumSet` is exactly the `Pairwise` condition
`checkCol` tests. -/
theorem pairwise_map_toAList_iff (colour : Nat → Nat) (tree : NumSet) :
    ((sptToAList tree).map (fun entry => colour entry.1)).Pairwise (· ≠ ·) ↔
      ColourInjectiveOn colour tree := by
  rw [← List.nodup_iff_pairwise_ne]
  have hkeys : ((sptToAList tree).map Prod.fst).Nodup := sptToAListKeysNodup tree
  have hmap : (sptToAList tree).map (fun entry => colour entry.1) =
      ((sptToAList tree).map Prod.fst).map colour := by
    rw [List.map_map]; rfl
  rw [hmap, List.nodup_map_iff_inj_on hkeys]
  unfold ColourInjectiveOn
  constructor
  · intro h left right hleft hright heq
    exact h left ((mem_numSetToList left tree).mpr hleft)
      right ((mem_numSetToList right tree).mpr hright) heq
  · intro h left hleft right hright heq
    exact h left right ((mem_numSetToList left tree).mp hleft)
      ((mem_numSetToList right tree).mp hright) heq

/-- `wordCheckColour` and `checkCol` agree on a duplicate-free payload. -/
theorem checkCol_agrees (colour : Nat → Nat) (names : List Nat) (tree : NumSet)
    (hnd : names.Nodup) (hd : DomEq names tree) :
    CheckResultRel (wordCheckColour colour names) (checkCol colour tree) := by
  by_cases h : (names.map colour).Nodup
  · have hinj : ColourInjectiveOn colour tree := by
      have hinjList := (List.nodup_map_iff_inj_on hnd).mp h
      intro left right hleft hright heq
      exact hinjList left ((hd left).mp hleft) right ((hd right).mp hright) heq
    have hcol : checkCol colour tree =
        some (tree, sptFromAList ((sptToAList tree).map (fun entry => (colour entry.1, ())))) := by
      unfold checkCol
      rw [if_pos ((pairwise_map_toAList_iff colour tree).mpr hinj)]
      simp only [List.map_map, Function.comp_def]
    rw [hcol]
    simp only [wordCheckColour, if_pos h, CheckResultRel]
    refine ⟨hd, ?_⟩
    intro key
    rw [sptMem_sptFromAList_map_unit]
    constructor
    · rintro ⟨name, hmem, heq⟩
      exact List.mem_map.mpr ⟨name, (hd name).mp hmem, heq⟩
    · intro hmem
      obtain ⟨name, hname, heq⟩ := List.mem_map.mp hmem
      exact ⟨name, (hd name).mpr hname, heq⟩
  · have hcol : checkCol colour tree = none := by
      unfold checkCol
      rw [if_neg]
      intro hp
      have hc : ColourInjectiveOn colour tree := (pairwise_map_toAList_iff colour tree).mp hp
      apply h
      apply (List.nodup_map_iff_inj_on hnd).mpr
      intro left hleft right hright heq
      exact hc left right ((hd left).mpr hleft) ((hd right).mpr hright) heq
    rw [hcol]
    simp only [wordCheckColour, if_neg h, CheckResultRel]

/-! ## Permutation invariance of the reviewed partial check

The executed `branch none` case passes a filtered `List Nat` of names while the
reviewed checker passes the `toAList` enumeration of a `NumSet`; the two lists
have the same member set and are duplicate-free.  `checkPartialCol`'s outcome
depends only on that member set, which is recorded below as invariance under
`List.Perm` (and hence, for duplicate-free lists with equal membership, under the
`ListDomEq` relation). -/

/-- Domain equality of two `NumSet`s. -/
def SetDomEq (left right : NumSet) : Prop := ∀ key, sptMem key left ↔ sptMem key right

/-- Result correspondence for two reviewed checker runs. -/
def ReviewedResultRel : Option (NumSet × NumSet) → Option (NumSet × NumSet) → Prop
  | some (names, coloured), some (names', coloured') =>
      SetDomEq names names' ∧ SetDomEq coloured coloured'
  | none, none => True
  | _, _ => False

/-- One step of the reviewed partial check, exposed so that reordering can be
reasoned about without unfolding the recursive function. -/
def partialStep (colour : Nat → Nat) (name : Nat) (state : NumSet × NumSet) :
    Option (NumSet × NumSet) :=
  if sptLookup name state.1 = some () then some state
  else if sptLookup (colour name) state.2 = some () then none
  else some (sptInsert name () state.1, sptInsert (colour name) () state.2)

/-- The reviewed partial check as a fold over `partialStep`. -/
def checkPartialColAux (colour : Nat → Nat) :
    List Nat → NumSet × NumSet → Option (NumSet × NumSet)
  | [], state => some state
  | name :: rest, state =>
      match partialStep colour name state with
      | none => none
      | some state' => checkPartialColAux colour rest state'

/-- `checkPartialCol` is the `partialStep` fold. -/
theorem checkPartialCol_eq_aux (colour : Nat → Nat) (names : List Nat)
    (liveS fliveS : NumSet) :
    checkPartialCol colour names liveS fliveS =
      checkPartialColAux colour names (liveS, fliveS) := by
  induction names generalizing liveS fliveS with
  | nil => rfl
  | cons name rest ih =>
      by_cases h : sptLookup name liveS = some ()
      · simp only [checkPartialCol, partialStep, h, if_true, checkPartialColAux]
        exact ih liveS fliveS
      · have hnone : sptLookup name liveS = none := by
          cases hh : sptLookup name liveS with
          | none => rfl
          | some value => cases value; exact absurd hh h
        by_cases hc : sptLookup (colour name) fliveS = some ()
        · simp only [checkPartialCol, partialStep, if_false, hc, if_true,
            checkPartialColAux, hnone, reduceCtorEq]
        · have hcnone : sptLookup (colour name) fliveS = none := by
            cases hh : sptLookup (colour name) fliveS with
            | none => rfl
            | some value => cases value; exact absurd hh hc
          simp only [checkPartialCol, partialStep, if_false, if_false,
            checkPartialColAux, hnone, hcnone, reduceCtorEq]
          exact ih _ _

/-- `partialStep` respects domain-equal states. -/
theorem partialStep_congr (colour : Nat → Nat) (name : Nat) (s s' : NumSet × NumSet)
    (h1 : SetDomEq s.1 s'.1) (h2 : SetDomEq s.2 s'.2) :
    ReviewedResultRel (partialStep colour name s) (partialStep colour name s') := by
  obtain ⟨L, C⟩ := s
  obtain ⟨L', C'⟩ := s'
  have hL : sptLookup name L = some () ↔ sptLookup name L' = some () := by
    rw [sptLookup_eq_some_unit_iff, sptLookup_eq_some_unit_iff]; exact h1 name
  have hC : sptLookup (colour name) C = some () ↔ sptLookup (colour name) C' = some () := by
    rw [sptLookup_eq_some_unit_iff, sptLookup_eq_some_unit_iff]; exact h2 (colour name)
  by_cases hmL : sptLookup name L = some ()
  · have hmL' : sptLookup name L' = some () := hL.mp hmL
    simp only [partialStep, hmL, hmL', if_true, ReviewedResultRel]
    exact ⟨h1, h2⟩
  · have hmL' : ¬ sptLookup name L' = some () := fun h => hmL (hL.mpr h)
    by_cases hmC : sptLookup (colour name) C = some ()
    · have hmC' : sptLookup (colour name) C' = some () := hC.mp hmC
      simp only [partialStep, hmL, hmL', hmC, hmC', if_false, if_true, ReviewedResultRel]
    · have hmC' : ¬ sptLookup (colour name) C' = some () := fun h => hmC (hC.mpr h)
      simp only [partialStep, hmL, hmL', hmC, hmC', if_false, ReviewedResultRel]
      refine ⟨?_, ?_⟩
      · intro key
        rw [sptMem_sptInsert, sptMem_sptInsert]
        exact or_congr_right (h1 key)
      · intro key
        rw [sptMem_sptInsert, sptMem_sptInsert]
        exact or_congr_right (h2 key)

/-- The fold respects domain-equal states. -/
theorem checkPartialColAux_congr (colour : Nat → Nat) (names : List Nat) :
    ∀ (s s' : NumSet × NumSet), SetDomEq s.1 s'.1 → SetDomEq s.2 s'.2 →
      ReviewedResultRel (checkPartialColAux colour names s)
        (checkPartialColAux colour names s') := by
  induction names with
  | nil => intro s s' h1 h2; exact ⟨h1, h2⟩
  | cons name rest ih =>
      intro s s' h1 h2
      have hs := partialStep_congr colour name s s' h1 h2
      cases hp : partialStep colour name s with
      | none =>
          cases hp' : partialStep colour name s' with
          | none => simp only [checkPartialColAux, hp, hp']; exact trivial
          | some b =>
              rw [hp, hp'] at hs
              simp only [ReviewedResultRel] at hs
      | some a =>
          cases hp' : partialStep colour name s' with
          | none =>
              rw [hp, hp'] at hs
              simp only [ReviewedResultRel] at hs
          | some b =>
              rw [hp, hp'] at hs
              simp only [ReviewedResultRel] at hs
              obtain ⟨g1, g2⟩ := hs
              simp only [checkPartialColAux, hp, hp']
              exact ih a b g1 g2

/-- A name already live is skipped. -/
theorem partialStep_of_mem (colour : Nat → Nat) (x : Nat) (s : NumSet × NumSet)
    (h : sptMem x s.1) : partialStep colour x s = some s := by
  obtain ⟨L, C⟩ := s
  simp only [partialStep, (sptLookup_eq_some_unit_iff x L).mpr h, if_true]

/-- A non-live name whose colour is live fails the step. -/
theorem partialStep_of_not_mem_none (colour : Nat → Nat) (x : Nat) (s : NumSet × NumSet)
    (h1 : ¬ sptMem x s.1) (h2 : sptMem (colour x) s.2) :
    partialStep colour x s = none := by
  obtain ⟨L, C⟩ := s
  simp only [partialStep, (sptLookup_eq_some_unit_iff x L).not.mpr h1,
    (sptLookup_eq_some_unit_iff (colour x) C).mpr h2, if_false, if_true]

/-- A non-live name with an unused colour is added. -/
theorem partialStep_of_not_mem_some (colour : Nat → Nat) (x : Nat) (s : NumSet × NumSet)
    (h1 : ¬ sptMem x s.1) (h2 : ¬ sptMem (colour x) s.2) :
    partialStep colour x s =
      some (sptInsert x () s.1, sptInsert (colour x) () s.2) := by
  obtain ⟨L, C⟩ := s
  simp only [partialStep, (sptLookup_eq_some_unit_iff x L).not.mpr h1,
    (sptLookup_eq_some_unit_iff (colour x) C).not.mpr h2, if_false]

/-- Two `partialStep`s commute up to domain equality. -/
theorem partialStep_swap (colour : Nat → Nat) (x y : Nat) (state : NumSet × NumSet) :
    ReviewedResultRel
      ((partialStep colour x state).bind (partialStep colour y))
      ((partialStep colour y state).bind (partialStep colour x)) := by
  obtain ⟨L, C⟩ := state
  by_cases hxL : sptMem x L
  · rw [partialStep_of_mem colour x (L, C) hxL]; simp only [Option.bind_some]
    by_cases hyL : sptMem y L
    · rw [partialStep_of_mem colour y (L, C) hyL]; simp only [Option.bind_some]
      rw [partialStep_of_mem colour x (L, C) hxL]
      exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    · by_cases hyC : sptMem (colour y) C
      · rw [partialStep_of_not_mem_none colour y (L, C) hyL hyC]; simp only [Option.bind_none]
        exact trivial
      · rw [partialStep_of_not_mem_some colour y (L, C) hyL hyC]; simp only [Option.bind_some]
        rw [partialStep_of_mem colour x (sptInsert y () L, sptInsert (colour y) () C)
          (by rw [sptMem_sptInsert]; exact Or.inr hxL)]
        exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · by_cases hxC : sptMem (colour x) C
    · rw [partialStep_of_not_mem_none colour x (L, C) hxL hxC]
      by_cases hyL : sptMem y L
      · rw [partialStep_of_mem colour y (L, C) hyL]; simp only [Option.bind_some]
        rw [partialStep_of_not_mem_none colour x (L, C) hxL hxC]; simp only [Option.bind_none]
        exact trivial
      · by_cases hyC : sptMem (colour y) C
        · rw [partialStep_of_not_mem_none colour y (L, C) hyL hyC]; simp only [Option.bind_none]
          exact trivial
        · rw [partialStep_of_not_mem_some colour y (L, C) hyL hyC]; simp only [Option.bind_some]
          have hxne : x ≠ y := by intro h; subst h; exact hyC hxC
          rw [partialStep_of_not_mem_none colour x
            (sptInsert y () L, sptInsert (colour y) () C)
            (by rw [sptMem_sptInsert]; exact fun h => h.elim (fun hxy => hxne hxy) hxL)
            (by rw [sptMem_sptInsert]; exact Or.inr hxC)]
          simp only [Option.bind_none]
          exact trivial
    · rw [partialStep_of_not_mem_some colour x (L, C) hxL hxC]; simp only [Option.bind_some]
      by_cases hyL : sptMem y L
      · rw [partialStep_of_mem colour y (L, C) hyL]; simp only [Option.bind_some]
        rw [partialStep_of_mem colour y (sptInsert x () L, sptInsert (colour x) () C)
          (by rw [sptMem_sptInsert]; exact Or.inr hyL)]
        rw [partialStep_of_not_mem_some colour x (L, C) hxL hxC]
        exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
      · by_cases hyC : sptMem (colour y) C
        · rw [partialStep_of_not_mem_none colour y (L, C) hyL hyC]; simp only [Option.bind_none]
          by_cases hxy : x = y
          · subst hxy; exact absurd hyC hxC
          · rw [partialStep_of_not_mem_none colour y
              (sptInsert x () L, sptInsert (colour x) () C)
              (by rw [sptMem_sptInsert]; exact fun h => h.elim (fun hxy' => hxy hxy'.symm) hyL)
              (by rw [sptMem_sptInsert]; exact Or.inr hyC)]
            exact trivial
        · rw [partialStep_of_not_mem_some colour y (L, C) hyL hyC]; simp only [Option.bind_some]
          by_cases hxy : x = y
          · subst hxy
            rw [partialStep_of_mem colour x (sptInsert x () L, sptInsert (colour x) () C)
              (by rw [sptMem_sptInsert]; exact Or.inl rfl)]
            exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
          · by_cases hcxy : colour x = colour y
            · rw [partialStep_of_not_mem_none colour y
                (sptInsert x () L, sptInsert (colour x) () C)
                (by rw [sptMem_sptInsert]; exact fun h => h.elim (fun hxy' => hxy hxy'.symm) hyL)
                (by rw [sptMem_sptInsert]; exact Or.inl hcxy.symm)]
              rw [partialStep_of_not_mem_none colour x
                (sptInsert y () L, sptInsert (colour y) () C)
                (by rw [sptMem_sptInsert]; exact fun h => h.elim (fun hxy' => hxy hxy') hxL)
                (by rw [sptMem_sptInsert]; exact Or.inl hcxy)]
              exact trivial
            · rw [partialStep_of_not_mem_some colour y
                (sptInsert x () L, sptInsert (colour x) () C)
                (by rw [sptMem_sptInsert]; exact fun h => h.elim (fun hxy' => hxy hxy'.symm) hyL)
                (by rw [sptMem_sptInsert]; exact fun h => h.elim (fun h' => hcxy h'.symm) hyC)]
              rw [partialStep_of_not_mem_some colour x
                (sptInsert y () L, sptInsert (colour y) () C)
                (by rw [sptMem_sptInsert]; exact fun h => h.elim (fun hxy' => hxy hxy') hxL)
                (by rw [sptMem_sptInsert]; exact fun h => h.elim (fun h' => hcxy h') hxC)]
              refine ⟨fun key => ?_, fun key => ?_⟩ <;>
                simp only [sptMem_sptInsert] <;> tauto

/-- The reviewed result relation is transitive. -/
theorem ReviewedResultRel_trans {a b c : Option (NumSet × NumSet)}
    (h1 : ReviewedResultRel a b) (h2 : ReviewedResultRel b c) :
    ReviewedResultRel a c := by
  cases a with
  | none => cases b <;> cases c <;> simp_all only [ReviewedResultRel]
  | some a =>
    cases b with
    | none => cases c <;> simp_all only [ReviewedResultRel]
    | some b =>
      cases c with
      | none => simp_all only [ReviewedResultRel]
      | some c =>
        simp only [ReviewedResultRel] at h1 h2 ⊢
        exact ⟨fun k => (h1.1 k).trans (h2.1 k), fun k => (h1.2 k).trans (h2.2 k)⟩

/-- `Option.bind` preserves the reviewed result relation for congruent
continuations. -/
theorem ReviewedResultRel_bind (f g : Option (NumSet × NumSet))
    (h : ReviewedResultRel f g)
    (k : NumSet × NumSet → Option (NumSet × NumSet))
    (hk : ∀ a b, SetDomEq a.1 b.1 → SetDomEq a.2 b.2 → ReviewedResultRel (k a) (k b)) :
    ReviewedResultRel
      (match f with | none => none | some a => k a)
      (match g with | none => none | some a => k a) := by
  cases f with
  | none =>
      cases g with
      | none => exact trivial
      | some b => simp only [ReviewedResultRel] at h
  | some a =>
      cases g with
      | none => simp only [ReviewedResultRel] at h
      | some b =>
          simp only [ReviewedResultRel] at h
          obtain ⟨g1, g2⟩ := h
          exact hk a b g1 g2

/-- If the left run fails, the right run fails too. -/
theorem ReviewedResultRel_none_left {g : Option (NumSet × NumSet)}
    (h : ReviewedResultRel none g) : g = none := by
  cases g <;> simp_all only [ReviewedResultRel]

/-- If the right run fails, the left run fails too. -/
theorem ReviewedResultRel_none_right {f : Option (NumSet × NumSet)}
    (h : ReviewedResultRel f none) : f = none := by
  cases f <;> simp_all only [ReviewedResultRel]

/-- Reordering the first two names preserves the reviewed partial-check result. -/
theorem checkPartialColAux_cons_swap (colour : Nat → Nat) (x y : Nat)
    (rest : List Nat) (state : NumSet × NumSet) :
    ReviewedResultRel (checkPartialColAux colour (x :: y :: rest) state)
      (checkPartialColAux colour (y :: x :: rest) state) := by
  have hs := partialStep_swap colour x y state
  cases hx : partialStep colour x state with
  | none =>
      cases hy : partialStep colour y state with
      | none => simp only [checkPartialColAux, hx, hy]; exact trivial
      | some b =>
          rw [hx, hy, Option.bind_none, Option.bind_some] at hs
          have hb := ReviewedResultRel_none_left hs
          simp only [checkPartialColAux, hx, hy, hb, ReviewedResultRel]
  | some a =>
      cases hy : partialStep colour y state with
      | none =>
          rw [hx, hy, Option.bind_none, Option.bind_some] at hs
          have ha := ReviewedResultRel_none_right hs
          simp only [checkPartialColAux, hx, hy, ha, ReviewedResultRel]
      | some b =>
          rw [hx, hy] at hs
          change ReviewedResultRel (partialStep colour y a) (partialStep colour x b) at hs
          simp only [checkPartialColAux, hx, hy]
          cases hy' : partialStep colour y a with
          | none =>
              cases hx' : partialStep colour x b with
              | none => exact trivial
              | some d => rw [hy', hx'] at hs; simp only [ReviewedResultRel] at hs
          | some c =>
              cases hx' : partialStep colour x b with
              | none => rw [hy', hx'] at hs; simp only [ReviewedResultRel] at hs
              | some d =>
                  rw [hy', hx'] at hs
                  simp only [ReviewedResultRel] at hs
                  obtain ⟨g1, g2⟩ := hs
                  exact checkPartialColAux_congr colour rest c d g1 g2

/-- The fold is invariant under `List.Perm`. -/
theorem checkPartialColAux_perm (colour : Nat → Nat) {names names' : List Nat}
    (h : names.Perm names') (state : NumSet × NumSet) :
    ReviewedResultRel (checkPartialColAux colour names state)
      (checkPartialColAux colour names' state) := by
  induction h generalizing state with
  | nil => exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  | cons x _ ih =>
      simp only [checkPartialColAux]
      cases hp : partialStep colour x state with
      | none => exact trivial
      | some a => exact ih a
  | swap x y l => exact checkPartialColAux_cons_swap colour y x l state
  | trans _ _ ih1 ih2 => exact ReviewedResultRel_trans (ih1 state) (ih2 state)

/-- `checkPartialCol` is invariant under `List.Perm` of its name list. -/
theorem checkPartialCol_perm (colour : Nat → Nat) {names names' : List Nat}
    (h : names.Perm names') (liveS fliveS : NumSet) :
    ReviewedResultRel (checkPartialCol colour names liveS fliveS)
      (checkPartialCol colour names' liveS fliveS) := by
  rw [checkPartialCol_eq_aux, checkPartialCol_eq_aux]
  exact checkPartialColAux_perm colour h (liveS, fliveS)

/-- Two name lists with the same member set. -/
def ListDomEq (left right : List Nat) : Prop := ∀ key, key ∈ left ↔ key ∈ right

/-- A live name is skipped by the fold. -/
theorem checkPartialColAux_skip (colour : Nat → Nat) (name : Nat) (rest : List Nat)
    (state : NumSet × NumSet) (h : sptMem name state.1) :
    checkPartialColAux colour (name :: rest) state = checkPartialColAux colour rest state := by
  simp only [checkPartialColAux, partialStep_of_mem colour name state h]

/-- Removing occurrences of a live name does not change the fold. -/
theorem checkPartialColAux_filter_ne (colour : Nat → Nat) (name : Nat) (rest : List Nat) :
    ∀ (state : NumSet × NumSet), sptMem name state.1 →
      checkPartialColAux colour (rest.filter (fun other => other != name)) state =
        checkPartialColAux colour rest state := by
  induction rest with
  | nil => intro state _; rfl
  | cons head tail ih =>
      intro state h
      by_cases hhead : head = name
      · subst head
        have hf : (name :: tail).filter (fun other => other != name) =
            tail.filter (fun other => other != name) := by simp
        rw [hf, checkPartialColAux_skip colour name tail state h]
        exact ih state h
      · have hf : (head :: tail).filter (fun other => other != name) =
            head :: tail.filter (fun other => other != name) := by
          simp [hhead]
        rw [hf]
        by_cases hhm : sptMem head state.1
        · rw [checkPartialColAux_skip colour head (tail.filter _) state hhm,
              checkPartialColAux_skip colour head tail state hhm]
          exact ih state h
        · by_cases hhc : sptMem (colour head) state.2
          · simp only [checkPartialColAux,
              partialStep_of_not_mem_none colour head state hhm hhc]
          · simp only [checkPartialColAux,
              partialStep_of_not_mem_some colour head state hhm hhc]
            apply ih
            rw [sptMem_sptInsert]; exact Or.inr h

/-- The fold ignores duplicates in its name list. -/
theorem checkPartialColAux_eraseDups (colour : Nat → Nat) :
    ∀ (names : List Nat) (state : NumSet × NumSet),
      checkPartialColAux colour names state =
        checkPartialColAux colour names.eraseDups state
  | [], state => rfl
  | name :: rest, state => by
      rw [List.eraseDups_cons]
      by_cases hm : sptMem name state.1
      · rw [checkPartialColAux_skip colour name rest state hm,
            checkPartialColAux_skip colour name ((rest.filter _).eraseDups) state hm,
            ← checkPartialColAux_filter_ne colour name rest state hm]
        exact checkPartialColAux_eraseDups colour (rest.filter fun other => other != name) state
      · by_cases hc : sptMem (colour name) state.2
        · simp only [checkPartialColAux, partialStep_of_not_mem_none colour name state hm hc]
        · simp only [checkPartialColAux, partialStep_of_not_mem_some colour name state hm hc]
          have hmem : sptMem name (sptInsert name () state.1) := by
            rw [sptMem_sptInsert]; exact Or.inl rfl
          rw [← checkPartialColAux_filter_ne colour name rest
            (sptInsert name () state.1, sptInsert (colour name) () state.2) hmem]
          exact checkPartialColAux_eraseDups colour (rest.filter fun other => other != name)
            (sptInsert name () state.1, sptInsert (colour name) () state.2)
termination_by names _ => names.length
decreasing_by
  all_goals
    simp_wf
    exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- `checkPartialCol` ignores duplicates in its name list. -/
theorem checkPartialCol_eraseDups (colour : Nat → Nat) (names : List Nat)
    (liveS fliveS : NumSet) :
    checkPartialCol colour names liveS fliveS =
      checkPartialCol colour names.eraseDups liveS fliveS := by
  rw [checkPartialCol_eq_aux, checkPartialCol_eq_aux]
  exact checkPartialColAux_eraseDups colour names (liveS, fliveS)

/-- `checkPartialCol` is invariant under name lists with the same member set. -/
theorem checkPartialCol_listDomEq (colour : Nat → Nat) {names names' : List Nat}
    (h : ListDomEq names names') (liveS fliveS : NumSet) :
    ReviewedResultRel (checkPartialCol colour names liveS fliveS)
      (checkPartialCol colour names' liveS fliveS) := by
  rw [checkPartialCol_eraseDups colour names, checkPartialCol_eraseDups colour names']
  apply checkPartialCol_perm
  apply (List.perm_ext_iff_of_nodup (nodup_eraseDups names) (nodup_eraseDups names')).mpr
  intro key
  rw [List.mem_eraseDups, List.mem_eraseDups, h key]

/-- Composing the executed/reviewed correspondence with reviewed result
correspondence. -/
theorem CheckResultRel_trans {exec : Option (List Nat × List Nat)}
    {a b : Option (NumSet × NumSet)}
    (h1 : CheckResultRel exec a) (h2 : ReviewedResultRel a b) :
    CheckResultRel exec b := by
  cases exec with
  | none => cases a <;> cases b <;> simp_all only [CheckResultRel, ReviewedResultRel]
  | some e =>
      cases a with
      | none => cases b <;> simp_all only [CheckResultRel]
      | some av =>
          cases b with
          | none => simp_all only [CheckResultRel, ReviewedResultRel]
          | some bv =>
              simp only [CheckResultRel, ReviewedResultRel] at h1 h2 ⊢
              exact ⟨fun k => (h2.1 k).symm.trans (h1.1 k),
                fun k => (h2.2 k).symm.trans (h1.2 k)⟩

/-! ## The codec and the executed/reviewed checker agreement -/

/-- Codec from the executed `WordClashTree` to the reviewed `RegAlloc.ClashTree`:
the `List Nat` payloads are mapped to `NumSet`s through `listToNumSet`. -/
def wordClashTreeToReviewed : WordClashTree → ClashTree
  | .delta writes reads => .delta writes reads
  | .seq first second =>
      .seq (wordClashTreeToReviewed first) (wordClashTreeToReviewed second)
  | .branch live thenBranch elseBranch =>
      .branch (live.map listToNumSet)
        (wordClashTreeToReviewed thenBranch) (wordClashTreeToReviewed elseBranch)
  | .set names => .set (listToNumSet names)

/-- Reverse codec: reviewed `NumSet` payloads are enumerated by `numSetToList`. -/
def reviewedToWordClashTree : ClashTree → WordClashTree
  | .delta writes reads => .delta writes reads
  | .seq first second =>
      .seq (reviewedToWordClashTree first) (reviewedToWordClashTree second)
  | .branch live thenBranch elseBranch =>
      .branch (live.map numSetToList)
        (reviewedToWordClashTree thenBranch) (reviewedToWordClashTree elseBranch)
  | .set tree => .set (numSetToList tree)

/-- Membership after the executed `wordNumSetDelete`. -/
theorem mem_wordNumSetDelete (names live : List Nat) (key : Nat) :
    key ∈ wordNumSetDelete names live ↔ key ∈ live ∧ key ∉ names := by
  induction names generalizing live with
  | nil => simp [wordNumSetDelete]
  | cons name rest ih =>
      rw [wordNumSetDelete, ih, List.mem_filter]
      by_cases hkn : key = name
      · subst hkn; simp
      · simp [hkn]

/-- The executed and reviewed deletions agree on domain-equal inputs. -/
theorem DomEq_wordNumSetDelete (names : List Nat) (live : List Nat) (liveS : NumSet)
    (hd : DomEq live liveS) :
    DomEq (wordNumSetDelete names live) (numsetListDelete names liveS) := by
  intro key
  rw [sptMem_numsetListDelete, mem_wordNumSetDelete, hd key]

/-- The executed `elseOut.filter (· ∉ thenOut)` and the reviewed `toAList` of
`rightS \ leftS` have the same member set. -/
theorem ListDomEq_filter_not_toAList_difference
    (left right : List Nat) (leftS rightS : NumSet)
    (hleft : DomEq left leftS) (hright : DomEq right rightS) :
    ListDomEq (right.filter (fun name => name ∉ left))
      (numSetToList (sptDifference rightS leftS)) := by
  intro key
  rw [List.mem_filter, mem_numSetToList, sptMem_sptDifference]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨hr, hn⟩
    exact ⟨(hright key).mpr hr, fun hl => hn ((hleft key).mp hl)⟩
  · rintro ⟨hr, hn⟩
    exact ⟨(hright key).mp hr, fun hl => hn ((hleft key).mpr hl)⟩

/-- The executed checker and the reviewed checker agree under the codec: both
fail, or both succeed with domain-equal live and coloured sets. -/
theorem wordClashTreeCheck_agrees (colour : Nat → Nat) :
    ∀ (tree : WordClashTree) (live flive : List Nat) (liveS fliveS : NumSet),
      DomEq live liveS → DomEq flive fliveS →
      CheckResultRel (wordClashTreeCheck colour tree live flive)
        (checkClashTree colour (wordClashTreeToReviewed tree) liveS fliveS) := by
  intro tree
  induction tree with
  | delta writes reads =>
      intro live flive liveS fliveS hlive hflive
      simp only [wordClashTreeCheck, checkClashTree, wordClashTreeToReviewed]
      have hw := checkPartialCol_agrees colour writes live flive liveS fliveS hlive hflive
      cases h1 : wordCheckPartialColour colour writes live flive with
      | none =>
          cases h2 : checkPartialCol colour writes liveS fliveS with
          | none => simp only [CheckResultRel]
          | some r => rw [h1, h2] at hw; simp only [CheckResultRel] at hw
      | some r1 =>
          cases h2 : checkPartialCol colour writes liveS fliveS with
          | none => rw [h1, h2] at hw; simp only [CheckResultRel] at hw
          | some r2 =>
              rw [h1, h2] at hw
              obtain ⟨g1, g2⟩ := hw
              have hdelLive := DomEq_wordNumSetDelete writes live liveS hlive
              have hdelFlive :=
                DomEq_wordNumSetDelete (writes.map colour) flive fliveS hflive
              have hr := checkPartialCol_agrees colour reads
                (wordNumSetDelete writes live)
                (wordNumSetDelete (writes.map colour) flive)
                (numsetListDelete writes liveS)
                (numsetListDelete (writes.map colour) fliveS)
                hdelLive hdelFlive
              exact hr
  | set names =>
      intro live flive liveS fliveS _ _
      simp only [wordClashTreeCheck, checkClashTree, wordClashTreeToReviewed]
      exact checkCol_agrees colour names.eraseDups (listToNumSet names)
        (nodup_eraseDups names) (DomEq_eraseDups_listToNumSet names)
  | seq first second ihfirst ihsecond =>
      intro live flive liveS fliveS hlive hflive
      simp only [wordClashTreeCheck, checkClashTree, wordClashTreeToReviewed]
      have hsec := ihsecond live flive liveS fliveS hlive hflive
      cases h1 : wordClashTreeCheck colour second live flive with
      | none =>
          cases h2 : checkClashTree colour (wordClashTreeToReviewed second) liveS fliveS with
          | none => simp only [CheckResultRel]
          | some r => rw [h1, h2] at hsec; simp only [CheckResultRel] at hsec
      | some r1 =>
          cases h2 : checkClashTree colour (wordClashTreeToReviewed second) liveS fliveS with
          | none => rw [h1, h2] at hsec; simp only [CheckResultRel] at hsec
          | some r2 =>
              rw [h1, h2] at hsec
              obtain ⟨g1, g2⟩ := hsec
              have hfir := ihfirst r1.1 r1.2 r2.1 r2.2 g1 g2
              exact hfir
  | branch branchLive thenBranch elseBranch ihthen ihelse =>
      intro liveState flive liveS fliveS hlive hflive
      simp only [wordClashTreeCheck, checkClashTree, wordClashTreeToReviewed]
      have hthen := ihthen liveState flive liveS fliveS hlive hflive
      cases h1 : wordClashTreeCheck colour thenBranch liveState flive with
      | none =>
          cases h1' : checkClashTree colour (wordClashTreeToReviewed thenBranch) liveS fliveS with
          | none => simp only [CheckResultRel]
          | some r => rw [h1, h1'] at hthen; simp only [CheckResultRel] at hthen
      | some r1 =>
          cases h1' : checkClashTree colour (wordClashTreeToReviewed thenBranch) liveS fliveS with
          | none => rw [h1, h1'] at hthen; simp only [CheckResultRel] at hthen
          | some r2 =>
              rw [h1, h1'] at hthen
              obtain ⟨g1, g2⟩ := hthen
              have helse := ihelse liveState flive liveS fliveS hlive hflive
              cases h3 : wordClashTreeCheck colour elseBranch liveState flive with
              | none =>
                  cases h3' : checkClashTree colour (wordClashTreeToReviewed elseBranch)
                      liveS fliveS with
                  | none => simp only [CheckResultRel]
                  | some r => rw [h3, h3'] at helse; simp only [CheckResultRel] at helse
              | some r3 =>
                  cases h3' : checkClashTree colour (wordClashTreeToReviewed elseBranch)
                      liveS fliveS with
                  | none => rw [h3, h3'] at helse; simp only [CheckResultRel] at helse
                  | some r4 =>
                      rw [h3, h3'] at helse
                      obtain ⟨g3, g4⟩ := helse
                      cases branchLive with
                      | none =>
                          have hnames := ListDomEq_filter_not_toAList_difference
                            r1.1 r3.1 r2.1 r4.1 g1 g3
                          have hbase := checkPartialCol_agrees colour
                            (r3.1.filter (fun name => name ∉ r1.1)) r1.1 r1.2 r2.1 r2.2 g1 g2
                          have hperm := checkPartialCol_listDomEq colour hnames r2.1 r2.2
                          exact CheckResultRel_trans hbase hperm
                      | some names =>
                          exact checkCol_agrees colour names.eraseDups (listToNumSet names)
                            (nodup_eraseDups names) (DomEq_eraseDups_listToNumSet names)

/-! ## Roundtrip laws -/

/-- A payload list that is already in the canonical `toAList` enumeration order
of its `NumSet`. -/
def CanonicalList (names : List Nat) : Prop := numSetToList (listToNumSet names) = names

/-- Executed trees all of whose set/branch payloads are canonical. -/
def CanonicalTree : WordClashTree → Prop
  | .delta _ _ => True
  | .seq first second => CanonicalTree first ∧ CanonicalTree second
  | .branch live thenBranch elseBranch =>
      (∀ names, live = some names → CanonicalList names) ∧
        CanonicalTree thenBranch ∧ CanonicalTree elseBranch
  | .set names => CanonicalList names

/-- On canonical executed trees the codec roundtrips. -/
theorem reviewedToWordClashTree_toReviewed (tree : WordClashTree)
    (h : CanonicalTree tree) :
    reviewedToWordClashTree (wordClashTreeToReviewed tree) = tree := by
  induction tree with
  | delta => rfl
  | seq first second ihfirst ihsecond =>
      simp only [wordClashTreeToReviewed, reviewedToWordClashTree, CanonicalTree] at h ⊢
      rw [ihfirst h.1, ihsecond h.2]
  | branch live thenBranch elseBranch ihthen ihelse =>
      simp only [wordClashTreeToReviewed, reviewedToWordClashTree, CanonicalTree] at h ⊢
      rw [ihthen h.2.1, ihelse h.2.2]
      have hlive : (live.map listToNumSet).map numSetToList = live := by
        cases live with
        | none => rfl
        | some names => exact congrArg some (h.1 names rfl)
      rw [hlive]
  | set names =>
      simp only [wordClashTreeToReviewed, reviewedToWordClashTree]
      rw [h]

end Flapjack.ClashTreeCodec
