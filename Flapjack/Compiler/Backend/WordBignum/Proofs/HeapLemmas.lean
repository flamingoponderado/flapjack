module

public import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
public import Flapjack.Compiler.Backend.WordBignum.Proofs.EvaluateLemmas
public import Flapjack.Pancake.Semantics.LoopSemStateExact

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
`n2w (LENGTH xs) * bytes_in_word`; Lean keeps that order and proves the fact
from the tagged `stack_removeProof` port, whose statement has the same product
in the commuted order. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "word_list_APPEND"
  (words_as_type_indexed_bitvec)]
theorem wordListAppendWordBignum {width : Nat} [NeZero width] {β : Type}
    (xs ys : List β) (a : BitVec width) :
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

end Flapjack.Compiler.Backend.WordBignum
