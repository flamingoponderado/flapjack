module

public import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
public import Flapjack.Compiler.Backend.WordBignum.Proofs.EvaluateLemmas
public import Flapjack.Pancake.Semantics.LoopSemStateExact
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Compiler.Backend.BackendCommon

@[expose] public section

/-! The heap-list and list-update lemmas of
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. `word_list_APPEND`
is the same fact as the tagged `stack_removeProof` port in
`Flapjack/Compiler/Backend/StackRemove/Proofs/StackHeap.lean`, restated here
for its own source declaration; the `list_update` family is new to this
script. -/

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack
open Flapjack.Misc
open Flapjack.SetSep
open Flapjack.Compiler.Backend.StackRemove

/-- HOL `word_list_APPEND` (`word_bignumProofScript.sml:499`): appending two
payload lists lays the second list after the first, at the address advanced by
`LENGTH xs * bytes_in_word`. HOL writes the product as
`n2w (LENGTH xs) * bytes_in_word`; Lean keeps that order, its element type
variable `α` matching HOL's `α` payload type, and proves the fact from the
tagged `stack_removeProof` port, whose statement has the same product in the
commuted order. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "word_list_APPEND"
  (words_as_type_indexed_bitvec)]
theorem wordListAppendWordBignum {width : Nat} [NeZero width] {α : Type}
    (xs ys : List α) (a : BitVec width) :
    Misc.wordList a (xs ++ ys) =
      star (Misc.wordList a xs)
        (Misc.wordList (a + BitVec.ofNat width xs.length * bytesInWord width) ys) := by
  rw [StackHeap.wordListAppend]
  simp only [BitVec.mul_comm]

/-- HOL `list_update_def` (`word_bignumProofScript.sml:527`): insert the paired
payloads into the tree at the given keys, using HOL's `ARB` for payloads that
the source list does not supply. The `ARB` is the shared opaque `holArb`, so the
declaration needs only the carrier's `Nonempty` instance, recorded by the
`total_function_inhabitants` qualifier. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "list_update_def"
  (total_function_inhabitants := [α])]
noncomputable def listUpdateSpt {α : Type} [Nonempty α] :
    List Nat → List α → Spt α → Spt α
  | [], _, t => t
  | x :: xs, y :: ys, t => sptInsert x y (listUpdateSpt xs ys t)
  | x :: xs, [], t => sptInsert x (holArb α) (listUpdateSpt xs [] t)

/-- HOL `domain_list_update` (`word_bignumProofScript.sml:575`): a key is in the
tree after the update exactly when it is one of the inserted keys or was already
in the tree. HOL's `x IN domain t` is the reviewed `sptMem` (domain membership of
the `sptree$num_map` carrier). -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "domain_list_update"]
theorem domainListUpdate {α : Type} [Nonempty α]
    (xs : List Nat) (ys : List α) (x : Nat) (t : Spt α) :
    sptMem x (listUpdateSpt xs ys t) ↔ x ∈ xs ∨ sptMem x t := by
  induction xs generalizing ys t with
  | nil => simp [listUpdateSpt]
  | cons head tail ih =>
    cases ys with
    | nil =>
      by_cases h : x = head
      · subst h
        simp [listUpdateSpt, sptMem_iff_lookup, sptLookup_sptInsert_same]
      · simp only [listUpdateSpt]
        rw [sptMem_iff_lookup, sptLookup_sptInsert_ne head x _ _ h, ← sptMem_iff_lookup, ih]
        simp [h]
    | cons value values =>
      by_cases h : x = head
      · subst h
        simp [listUpdateSpt, sptMem_iff_lookup, sptLookup_sptInsert_same]
      · simp only [listUpdateSpt]
        rw [sptMem_iff_lookup, sptLookup_sptInsert_ne head x _ _ h, ← sptMem_iff_lookup, ih]
        simp [h]

/-- HOL `list_update_alist_insert` (`word_bignumProofScript.sml:533`): with equal
list lengths the `ARB`-completing update is HOL's `alist_insert`, the tagged
`sptAlistInsert` rendering of the sptree library function. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "list_update_alist_insert"]
theorem listUpdateSpt_alistInsert {α : Type} [Nonempty α]
    (xs : List Nat) (ys : List α) (t : Spt α) :
    xs.length = ys.length →
      listUpdateSpt xs ys t = LoopSemStateFiniteExact.sptAlistInsert xs ys t := by
  induction xs generalizing ys t with
  | nil =>
    cases ys with
    | nil =>
      intro _
      rfl
    | cons value values =>
      intro h
      simp at h
  | cons head tail ih =>
    cases ys with
    | nil =>
      intro h
      simp at h
    | cons value values =>
      intro h
      simp only [listUpdateSpt, LoopSemStateFiniteExact.sptAlistInsert]
      have hlen : tail.length = values.length := by
        simp at h
        exact h
      rw [ih values t hlen]

/-- HOL `lookup_list_update_ADD_2` (`word_bignumProofScript.sml:641`): inserting
the shifted keys `n + 2` leaves the key `0` untouched. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "lookup_list_update_ADD_2"]
theorem lookupListUpdateAdd2 {α : Type} [Nonempty α]
    (saveRegs : List Nat) (ws : List α) (l : Spt α) :
    sptLookup 0 (listUpdateSpt (saveRegs.map (· + 2)) ws l) = sptLookup 0 l := by
  induction saveRegs generalizing ws l with
  | nil => rfl
  | cons head tail ih =>
    cases ws with
    | nil =>
      simp only [List.map_cons, listUpdateSpt]
      rw [sptLookup_sptInsert_ne (head + 2) 0 _ _ (by omega)]
      exact ih [] l
    | cons value values =>
      simp only [List.map_cons, listUpdateSpt]
      rw [sptLookup_sptInsert_ne (head + 2) 0 _ _ (by omega)]
      exact ih values l

/-- HOL `shift_eq_bytes_in_word` (`word_bignumProofScript.sml:507`): at a
`good_dimindex` width, shifting left by `shift` (HOL's `word_shift`, the
reviewed `wordShiftAmount`) multiplies by `bytes_in_word`. HOL writes the shift
amount as `shift (:α) MOD dimword (:α)`; Lean keeps that modulo, `dimword` is
`2 ^ width`, and `bytes_in_word` is the reviewed `bytesInWord` (`width / 8`). -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "shift_eq_bytes_in_word"
  (words_as_type_indexed_bitvec)]
theorem shiftEqBytesInWord {width : Nat} [NeZero width] (w : BitVec width) :
    goodDimindex width →
      w <<< (wordShiftAmount width % 2 ^ width) = w * bytesInWord width := by
  intro h
  rcases h with h32 | h64
  · subst h32
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, wordShiftAmount, bytesInWord]
  · subst h64
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, wordShiftAmount, bytesInWord]

/-- HOL `LIST_REL_lemma` (`word_bignumProofScript.sml:668`): a pointwise
relation implication over members of both lists lifts to `LIST_REL`. HOL's `P`
and `Q` are Boolean relations, rendered here as `= true`, and HOL's
`LIST_REL` is `List.Forall₂`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "LIST_REL_lemma"]
theorem listRelLemma {α β : Type} (P Q : α → β → Bool) (xs : List α) (ys : List β)
    (h : ∀ x y, (x ∈ xs ∧ y ∈ ys) → P x y = true → Q x y = true) :
    List.Forall₂ (fun x y => P x y = true) xs ys →
      List.Forall₂ (fun x y => Q x y = true) xs ys := by
  induction xs generalizing ys with
  | nil =>
    intro hrel
    cases hrel
    exact .nil
  | cons head tail ih =>
    intro hrel
    cases hrel with
    | cons hP htail =>
      refine .cons (h head _ ⟨List.mem_cons_self, List.mem_cons_self⟩ hP) (ih _ ?_ htail)
      intro a b hab hp
      exact h a b ⟨List.mem_cons_of_mem _ hab.1, List.mem_cons_of_mem _ hab.2⟩ hp

/-! ## The `list_store` group (`word_bignumProofScript.sml:581-618`) -/

/-- Flapjack-only unfolding of the tagged `updateEq` at the lookup level. -/
theorem listStoreLookupUpdateEq {κ β : Type} [DecidableEq κ]
    (map : HolFiniteMapExact κ β) (entry : κ × β) (key : κ) :
    (map.updateEq entry).lookup key = FUPDATE_HOL map.lookup entry key := rfl

/-- Flapjack-only: HOL-equality updates at distinct keys commute. -/
theorem updateEq_comm {κ β : Type} [DecidableEq κ] (map : HolFiniteMapExact κ β)
    (e1 e2 : κ × β) (h : e1.1 ≠ e2.1) :
    (map.updateEq e1).updateEq e2 = (map.updateEq e2).updateEq e1 := by
  apply HolFiniteMapExact.ext_of_lookup
  intro key
  simp only [listStoreLookupUpdateEq, FUPDATE_HOL]
  by_cases h2 : key = e2.1 <;> by_cases h1 : key = e1.1 <;> simp_all

/-- Flapjack-only: the two `n2w` register names are equal exactly when their
numbers are, below the word-5 width. -/
theorem temp_eq_iff {a b : Nat} (ha : a < 32) (hb : b < 32) :
    ((.temp (BitVec.ofNat 5 a) : WordStoreHOL) = .temp (BitVec.ofNat 5 b)) ↔ a = b := by
  constructor
  · intro heq
    have hbit : BitVec.ofNat 5 a = BitVec.ofNat 5 b := by injection heq
    have hmod := congrArg (fun x : BitVec 5 => x.toNat) hbit
    simp only [BitVec.toNat_ofNat] at hmod
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    exact hmod
  · intro heq
    rw [heq]

/-- Flapjack untagged: the raw lookup rendering of HOL `list_store` over a plain
lookup function, used only by the canonical result witness below. -/
noncomputable def listStoreRaw {α : Type} [Nonempty α] :
    List Nat → List α → (WordStoreHOL → Option α) → WordStoreHOL → Option α
  | [], _, f => f
  | x :: xs, ys, f =>
      FUPDATE_HOL (listStoreRaw xs ys.tail f) (.temp (BitVec.ofNat 5 x), holHd ys)

/-- HOL `list_store_def` (`word_bignumProofScript.sml:581`): store the payload
list at the temporaries named by the register list, the payloads' heads going
to the first registers and HOL's `TL` to the rest of the payload list. `HD` on
an exhausted payload list is the reviewed total `holHd`, so the declaration
lists the element type's `Nonempty` instance, and `|+` is the HOL-equality
`updateEq`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "list_store_def"
  (fmap_as_finite_support_result) (total_function_inhabitants := [α])]
noncomputable def listStore {α : Type} [Nonempty α] :
    List Nat → List α → HolFiniteMapExact WordStoreHOL α → HolFiniteMapExact WordStoreHOL α
  | [], _, s => s
  | x :: xs, ys, s => (listStore xs ys.tail s).updateEq (.temp (BitVec.ofNat 5 x), holHd ys)

/-- Canonical standalone finite-map witness for `listStore`: its lookup is the
HOL-shaped raw `listStoreRaw` applied to the canonical input map's lookup, with
no premises and no dependence on the `HolFiniteMapExact` wrapper. -/
theorem holFmapAsFiniteSupportResultWitness_listStore {α : Type} [Nonempty α]
    (xs : List Nat) (ys : List α) (s : HolFiniteMapExact WordStoreHOL α)
    (key : WordStoreHOL) :
    (listStore xs ys s).lookup key = listStoreRaw xs ys s.lookup key := by
  induction xs generalizing ys s with
  | nil => rfl
  | cons head tail ih =>
    simp only [listStore, listStoreRaw, listStoreLookupUpdateEq, FUPDATE_HOL]
    by_cases hk : key = .temp (BitVec.ofNat 5 head)
    · simp [hk]
    · simp [hk]
      exact ih ys.tail s

/-- HOL `list_store_FUPDATE` (`word_bignumProofScript.sml:586`): an update at a
register outside the saved list commutes with the whole store, because the
saved registers are all below the generator's bound `max_var_name` (25). HOL's
single conjunction premise is one hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "list_store_FUPDATE"
  (fmap_as_finite_support_parameters := [st]) (words_as_type_indexed_bitvec)]
theorem listStore_FUPDATE {width : Nat} [NeZero width]
    (saveRegs : List Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (ys : List (WordLocW width)) (h : Nat) (v : BitVec width) :
    ¬ h ∈ saveRegs ∧ h < 25 ∧ (∀ n ∈ saveRegs, n < 25) →
      listStore saveRegs ys (st.updateEq (.temp (BitVec.ofNat 5 h), .word v)) =
        (listStore saveRegs ys st).updateEq (.temp (BitVec.ofNat 5 h), .word v) := by
  intro hpre
  obtain ⟨hmem, hlt, hall⟩ := hpre
  induction saveRegs generalizing ys st with
  | nil => rfl
  | cons head tail ih =>
    have hhead : h ≠ head := by
      intro heq
      have hmem' : h ∈ head :: tail := by
        rw [heq]
        exact List.mem_cons_self
      exact hmem hmem'
    have htail : ¬ h ∈ tail := by
      intro hin
      exact hmem (List.mem_cons_of_mem head hin)
    have hheadlt : head < 25 := hall head List.mem_cons_self
    have halltail : ∀ n ∈ tail, n < 25 := fun n hn => hall n (List.mem_cons_of_mem head hn)
    have hne : (.temp (BitVec.ofNat 5 h) : WordStoreHOL) ≠ .temp (BitVec.ofNat 5 head) := by
      intro heq
      exact hhead ((temp_eq_iff (a := h) (b := head) (by omega) (by omega)).mp heq)
    have ih' := ih st ys.tail htail halltail
    have hcomm := updateEq_comm (listStore tail ys.tail st)
      (.temp (BitVec.ofNat 5 h), .word v) (.temp (BitVec.ofNat 5 head), holHd ys) hne
    calc listStore (head :: tail) ys (st.updateEq (.temp (BitVec.ofNat 5 h), .word v))
        = (listStore tail ys.tail (st.updateEq (.temp (BitVec.ofNat 5 h), .word v))).updateEq
            (.temp (BitVec.ofNat 5 head), holHd ys) := rfl
      _ = ((listStore tail ys.tail st).updateEq (.temp (BitVec.ofNat 5 h), .word v)).updateEq
            (.temp (BitVec.ofNat 5 head), holHd ys) := by rw [ih']
      _ = ((listStore tail ys.tail st).updateEq (.temp (BitVec.ofNat 5 head), holHd ys)).updateEq
            (.temp (BitVec.ofNat 5 h), .word v) := hcomm

/-- Canonical standalone-map witness for the store parameter of
`listStore_FUPDATE`: the broad lookup codec roundtrips. -/
theorem holFmapAsFiniteSupportParamWitness_listStore_FUPDATE_st {width : Nat} [NeZero width]
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    HolFiniteMapExact.ofBroadlookup (HolFiniteMapExact.toBroadlookup st) st.finiteSupport = st := by
  cases st
  rfl

/-- HOL `FLOOKUP_list_store_ignore` (`word_bignumProofScript.sml:618`): storing
the saved registers never touches the three argument temporaries, nor any name
that is not a temporary, since every saved register is below `max_var_name`.
HOL's right-associated conjunction is kept, and `FLOOKUP` is the map's
`lookup`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "FLOOKUP_list_store_ignore"
  (fmap_as_finite_support_parameters := [st])]
theorem FLOOKUP_list_store_ignore {α : Type} [Nonempty α]
    (saveRegs : List Nat) (vals : List α) (st : HolFiniteMapExact WordStoreHOL α) :
    (∀ n ∈ saveRegs, n < 25) →
      (listStore saveRegs vals st).lookup tempIn1 = st.lookup tempIn1 ∧
      (listStore saveRegs vals st).lookup tempIn2 = st.lookup tempIn2 ∧
      (listStore saveRegs vals st).lookup tempOut = st.lookup tempOut ∧
      ∀ n : WordStoreHOL, (∀ r : BitVec 5, n ≠ .temp r) →
        (listStore saveRegs vals st).lookup n = st.lookup n := by
  intro hall
  induction saveRegs generalizing vals st with
  | nil =>
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro n _
    rfl
  | cons head tail ih =>
    have hheadlt : head < 25 := hall head List.mem_cons_self
    have halltail : ∀ n ∈ tail, n < 25 := fun n hn => hall n (List.mem_cons_of_mem head hn)
    have ih' := ih vals.tail st halltail
    have hne31 : tempIn1 ≠ .temp (BitVec.ofNat 5 head) := by
      intro heq
      have hdef : tempIn1 = (.temp 31 : WordStoreHOL) := rfl
      rw [hdef] at heq
      have h31 := (temp_eq_iff (a := 31) (b := head) (by omega) (by omega)).mp heq
      omega
    have hne30 : tempIn2 ≠ .temp (BitVec.ofNat 5 head) := by
      intro heq
      have hdef : tempIn2 = (.temp 30 : WordStoreHOL) := rfl
      rw [hdef] at heq
      have h30 := (temp_eq_iff (a := 30) (b := head) (by omega) (by omega)).mp heq
      omega
    have hne29 : tempOut ≠ .temp (BitVec.ofNat 5 head) := by
      intro heq
      have hdef : tempOut = (.temp 29 : WordStoreHOL) := rfl
      rw [hdef] at heq
      have h29 := (temp_eq_iff (a := 29) (b := head) (by omega) (by omega)).mp heq
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [listStore, listStoreLookupUpdateEq, FUPDATE_HOL]
      rw [if_neg hne31, ih'.1]
    · simp only [listStore, listStoreLookupUpdateEq, FUPDATE_HOL]
      rw [if_neg hne30, ih'.2.1]
    · simp only [listStore, listStoreLookupUpdateEq, FUPDATE_HOL]
      rw [if_neg hne29, ih'.2.2.1]
    · intro n hn
      simp only [listStore, listStoreLookupUpdateEq, FUPDATE_HOL]
      rw [if_neg ?_, ih'.2.2.2 n hn]
      intro heq
      exact hn (BitVec.ofNat 5 head) heq

/-- Canonical standalone-map witness for the store parameter of
`FLOOKUP_list_store_ignore`: the broad lookup codec roundtrips. -/
theorem holFmapAsFiniteSupportParamWitness_FLOOKUP_list_store_ignore_st {α : Type}
    (st : HolFiniteMapExact WordStoreHOL α) :
    HolFiniteMapExact.ofBroadlookup (HolFiniteMapExact.toBroadlookup st) st.finiteSupport = st := by
  cases st
  rfl

end Flapjack.Compiler.Backend.WordBignum
