import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
import Flapjack.Compiler.Backend.StackRemove.Proofs.Memory
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListInjective
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListReverse
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.ListEl

/-! Word-list heap lemmas of `stack_removeProofScript.sml` (lines 2827-3222)
used by the initializer proof. HOL sets are predicates; `set (GENLIST f n)` is
the membership predicate of `(List.range n).map f`, and `EL` is the exact
`holEl`. HOL's inhabited payload types are rendered by `[Nonempty β]` exactly
where a statement mentions `EL`.
-/

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory
open Flapjack Flapjack.Compiler.Backend.StackRemove

/-- Original local set identity on arbitrary predicate sets: HOL
`x INSERT s` is `fun y => y = x ∨ s y` and `s DELETE x` is
`fun y => s y ∧ y ≠ x`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "INSERT_DELETE_EQ_DELETE"]
theorem insertDeleteEqDelete {α : Type} (x : α) (s : α → Prop) :
    (fun y => (y = x ∨ s y) ∧ y ≠ x) = (fun y => s y ∧ y ≠ x) := by
  funext y
  apply propext
  constructor
  · rintro ⟨rfl | member, ne⟩
    · exact absurd rfl ne
    · exact ⟨member, ne⟩
  · rintro ⟨member, ne⟩
    exact ⟨Or.inr member, ne⟩

/-- Complete original join of a forward list with a reversed tail. The heap,
frames and the trailing proposition remain arbitrary; the end address is the
literal original equation. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_and_rev_join_lemma"
  (words_as_type_indexed_bitvec)]
theorem wordListAndRevJoinLemma {width : Nat} [NeZero width] {β : Type}
    (a b : BitVec width) (xs ys : List β)
    (p q : ((BitVec width × β) → Prop) → Prop) (ss : (BitVec width × β) → Prop) (b1 : Prop)
    (hyp : b = a + BitVec.ofNat width (xs.length + ys.length) * bytesInWord width ∧
      SetSep.star (SetSep.star p (Misc.wordList a (xs ++ ys.reverse))) q ss ∧ b1) :
    SetSep.star (SetSep.star (SetSep.star p (Misc.wordList a xs)) (wordListRev b ys)) q ss ∧
      b1 := by
  obtain ⟨rfl, assertion, side⟩ := hyp
  refine ⟨?_, side⟩
  have revEq := WordListReverse.wordListEqRev ys.reverse
    (a + bytesInWord width * BitVec.ofNat width xs.length)
  rw [List.reverse_reverse, List.length_reverse] at revEq
  have addressEq : a + bytesInWord width * BitVec.ofNat width xs.length +
      BitVec.ofNat width ys.length * bytesInWord width =
      a + BitVec.ofNat width (xs.length + ys.length) * bytesInWord width := by
    rw [BitVec.ofNat_add, BitVec.add_mul, BitVec.mul_comm (bytesInWord width), BitVec.add_assoc]
  rw [addressEq] at revEq
  rw [StackHeap.wordListAppend, revEq, SetSep.starAssoc] at assertion
  exact assertion

/-- Positive byte width under the original good dimension. -/
private theorem bytesInWord_toNat {width : Nat} [NeZero width] (good : goodDimindex width) :
    (bytesInWord width).toNat = width / 8 := by
  rcases good with rfl | rfl <;> rfl

private theorem bytes_pos {width : Nat} (good : goodDimindex width) : 0 < width / 8 := by
  rcases good with rfl | rfl <;> decide

/-- Distinct-address form of a wrap-free forward list: the heap is exactly
the indexed graph. Flapjack proof factoring shared by `word_list_set` and
`word_list_exists_addresses`; it has no separate HOL original. -/
private theorem wordListIndexed {width : Nat} [NeZero width] {β : Type}
    (good : goodDimindex width) :
    ∀ (xs : List β) (a : BitVec width), xs.length * (width / 8) < 2 ^ width →
      Misc.wordList a xs (fun e => ∃ i, ∃ h : i < xs.length,
        e = (a + BitVec.ofNat width i * bytesInWord width, xs[i])) := by
  intro xs
  induction xs with
  | nil =>
    intro a _
    show _ = _
    funext e
    simp
  | cons x xs ih =>
    intro a bound
    have pos := bytes_pos good
    have tailBound : xs.length * (width / 8) < 2 ^ width := by
      simp only [List.length_cons, Nat.succ_mul] at bound
      omega
    refine ⟨(fun e => e = (a, x)), _, ⟨?_, ?_⟩, rfl, ih (a + bytesInWord width) tailBound⟩
    · funext e
      apply propext
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by simp, by simp⟩
        · refine ⟨i + 1, by simp [hi], ?_⟩
          simp only [List.getElem_cons_succ, Prod.mk.injEq, and_true]
          rw [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
          ac_rfl
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl (by simp)
        | succ i =>
          refine Or.inr ⟨i, by simpa using hi, ?_⟩
          simp only [List.getElem_cons_succ, Prod.mk.injEq, and_true]
          rw [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
          ac_rfl
    · rintro e ⟨rfl, i, hi, eq⟩
      have addrEq := congrArg Prod.fst eq
      simp only at addrEq
      have zero : BitVec.ofNat width ((i + 1) * (width / 8)) = 0 := by
        have h := congrArg (fun z => z - a) addrEq
        simp only [BitVec.sub_self] at h
        rw [BitVec.add_assoc, BitVec.add_comm a, BitVec.add_sub_cancel] at h
        refine Eq.trans ?_ h.symm
        rw [bytesInWord, ← BitVec.ofNat_mul_ofNat, BitVec.ofNat_add, BitVec.add_mul,
          BitVec.add_comm]
        simp
      have lt : (i + 1) * (width / 8) < 2 ^ width := by
        simp only [List.length_cons] at bound
        have : (i + 1) * (width / 8) ≤ (xs.length + 1) * (width / 8) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have := congrArg BitVec.toNat zero
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt] at this
      simp at this
      have : 0 < (i + 1) * (width / 8) := Nat.mul_pos (by omega) pos
      omega

private theorem genlistSet {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (a : BitVec width) (xs : List β) :
    (fun e => e ∈ (List.range xs.length).map
        (fun i => (a + BitVec.ofNat width i * bytesInWord width, holEl i xs))) =
      (fun e => ∃ i, ∃ h : i < xs.length,
        e = (a + BitVec.ofNat width i * bytesInWord width, xs[i])) := by
  funext e
  apply propext
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [holEl_eq_getElem i xs hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [holEl_eq_getElem i xs hi]⟩

private theorem wrapFree {width : Nat} [NeZero width] {β : Type} (xs : List β) (a : BitVec width)
    (good : goodDimindex width)
    (bound : a.toNat + xs.length * (bytesInWord width).toNat < 2 ^ width) :
    xs.length * (width / 8) < 2 ^ width := by
  rw [bytesInWord_toNat good] at bound
  omega

/-- Complete original wrap-free forward list on the actual set of its indexed
graph, with the original good dimension and unsigned end-address bound. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_set"
  (words_as_type_indexed_bitvec)]
theorem wordListSet {width : Nat} [NeZero width] {β : Type} [Nonempty β] :
    ∀ (xs : List β) (a : BitVec width),
      goodDimindex width ∧
        a.toNat + xs.length * (bytesInWord width).toNat < 2 ^ width →
      Misc.wordList a xs (fun e => e ∈ (List.range xs.length).map
        (fun i => (a + BitVec.ofNat width i * bytesInWord width, holEl i xs))) := by
  rintro xs a ⟨good, bound⟩
  rw [genlistSet]
  exact wordListIndexed good xs a (wrapFree xs a good bound)

/-- Complete original characterisation of the wrap-free forward list
assertion as equality with its indexed graph. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_seteq"
  (words_as_type_indexed_bitvec)]
theorem wordListSeteq {width : Nat} [NeZero width] {β : Type} [Nonempty β] :
    ∀ (xs : List β) (a : BitVec width),
      goodDimindex width ∧
        a.toNat + xs.length * (bytesInWord width).toNat < 2 ^ width →
      Misc.wordList a xs = (fun s => s = (fun e => e ∈ (List.range xs.length).map
        (fun i => (a + BitVec.ofNat width i * bytesInWord width, holEl i xs)))) := by
  intro xs a hyp
  have listSet := wordListSet xs a hyp
  funext s
  apply propext
  constructor
  · intro assertion
    exact WordListInjective.wordListInj xs a s _ ⟨assertion, listSet⟩
  · rintro rfl
    exact listSet

/-- Complete original framed element read. The frames, memory and domain are
arbitrary; the original good-dimension and no-wrap premises are retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_EL_in_memory"
  (words_as_type_indexed_bitvec)]
theorem wordListElInMemory {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (a : BitVec width) (xs : List β) (r1 r2 : ((BitVec width × β) → Prop) → Prop)
    (m : BitVec width → β) (dm : BitVec width → Prop) (i : Nat)
    (hyp : goodDimindex width ∧
      a.toNat + xs.length * (bytesInWord width).toNat < 2 ^ width ∧
      SetSep.star (SetSep.star r1 (Misc.wordList a xs)) r2 (SetSep.fun2Set (m, dm)) ∧
      i < xs.length) :
    m (a + BitVec.ofNat width i * bytesInWord width) = holEl i xs := by
  obtain ⟨_, _, assertion, hi⟩ := hyp
  rcases assertion with ⟨left, right, outer, ⟨first, middle, inner, _, listHeap⟩, _⟩
  have member := StackHeap.wordListNth a xs middle i hi listHeap
  have graph : SetSep.fun2Set (m, dm)
      (a + bytesInWord width * BitVec.ofNat width i, xs[i]) := by
    rw [← outer.1]
    refine Or.inl ?_
    rw [← inner.1]
    exact Or.inr member
  rw [holEl_eq_getElem i xs hi, BitVec.mul_comm]
  exact ((SetSep.fun2SetThm m dm _ _).mp graph).1

/-- Complete original identification of the framed wrap-free list with the
memory assertion on its address range. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_in_memory"
  (words_as_type_indexed_bitvec)]
theorem wordListInMemory {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (a : BitVec width) (xs : List β) (r1 r2 : ((BitVec width × β) → Prop) → Prop)
    (m : BitVec width → β) (dm : BitVec width → Prop)
    (hyp : SetSep.star (SetSep.star r1 (Misc.wordList a xs)) r2 (SetSep.fun2Set (m, dm)) ∧
      goodDimindex width ∧
      a.toNat + xs.length * (bytesInWord width).toNat < 2 ^ width) :
    memoryHOL m (addresses a xs.length) = Misc.wordList a xs := by
  obtain ⟨assertion, good, bound⟩ := hyp
  rw [wordListSeteq xs a ⟨good, bound⟩]
  have graphEq : SetSep.fun2Set (m, addresses a xs.length) =
      (fun e => e ∈ (List.range xs.length).map
        (fun i => (a + BitVec.ofNat width i * bytesInWord width, holEl i xs))) := by
    funext e
    apply propext
    simp only [SetSep.fun2Set, mem_addresses, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, by
        rw [wordListElInMemory a xs r1 r2 m dm i ⟨good, bound, assertion, hi⟩]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, by
        rw [wordListElInMemory a xs r1 r2 m dm i ⟨good, bound, assertion, hi⟩]⟩
  funext s
  simp only [memoryHOL, graphEq]

private theorem readMem_getElem {width : Nat} [NeZero width] {β : Type}
    (m : BitVec width → β) :
    ∀ (n : Nat) (a : BitVec width) (i : Nat) (h : i < (readMem a m n).length),
      (readMem a m n)[i] = m (a + BitVec.ofNat width i * bytesInWord width)
  | 0, _, _, h => by simp [readMem] at h
  | n + 1, a, 0, _ => by simp [readMem]
  | n + 1, a, i + 1, h => by
    simp only [readMem, List.getElem_cons_succ]
    rw [readMem_getElem m n (a + bytesInWord width) i (by simpa [readMem] using h),
      BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
    ac_rfl

/-- Flapjack proof factoring: the memory graph on an address range is the
indexed graph of the words read there. No separate HOL declaration. -/
private theorem fun2SetAddresses {width : Nat} [NeZero width] {β : Type}
    (m : BitVec width → β) (n : Nat) (a : BitVec width) :
    SetSep.fun2Set (m, addresses a n) =
      (fun e => ∃ i, ∃ h : i < (readMem a m n).length,
        e = (a + BitVec.ofNat width i * bytesInWord width, (readMem a m n)[i])) := by
  funext e
  apply propext
  simp only [SetSep.fun2Set, mem_addresses]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, by rw [length_readMem]; exact hi, by rw [readMem_getElem]⟩
  · rintro ⟨i, hi, rfl⟩
    rw [length_readMem] at hi
    exact ⟨_, ⟨i, hi, rfl⟩, by rw [readMem_getElem]⟩

/-- Complete original existence of a word list covering exactly the address
range, for an arbitrary memory function and base address. Only the original
range-size bound and good dimension are assumed; the base may wrap. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_exists_addresses"
  (words_as_type_indexed_bitvec)]
theorem wordListExistsAddresses {width : Nat} [NeZero width] {β : Type}
    (m1 : BitVec width → β) :
    ∀ (n : Nat) (a : BitVec width),
      (width / 8) * n < 2 ^ width ∧ goodDimindex width →
      Misc.wordListExists a n (SetSep.fun2Set (m1, addresses a n)) := by
  rintro n a ⟨bound, good⟩
  refine ⟨readMem a m1 n, (WordListExists.starCond _ _ _).mpr ⟨?_, length_readMem n a m1⟩⟩
  rw [fun2SetAddresses]
  exact wordListIndexed good (readMem a m1 n) a
    (by rw [length_readMem, Nat.mul_comm]; exact bound)

/-- Complete original identification of the memory assertion on an address
range with the forward list of the words read there. Only the original
range-size bound and good dimension are assumed; the base may wrap. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "memory_addresses"
  (words_as_type_indexed_bitvec)]
theorem memoryAddresses {width : Nat} [NeZero width] :
    ∀ (n : Nat) (a : BitVec width) (m : BitVec width → WordLocW width),
      n * (width / 8) < 2 ^ width ∧ goodDimindex width →
      memoryHOL m (addresses a n) = Misc.wordList a (readMem a m n) := by
  rintro n a m ⟨bound, good⟩
  have indexed := wordListIndexed good (readMem a m n) a
    (by rw [length_readMem]; exact bound)
  funext heap
  apply propext
  simp only [memoryHOL, fun2SetAddresses]
  constructor
  · rintro rfl
    exact indexed
  · intro assertion
    exact WordListInjective.wordListInj _ a heap _ ⟨assertion, indexed⟩

/-- Complete original wrap decomposition: a list longer than the address space
splits into two non-empty lists starting at the same base address. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_wrap"
  (words_as_type_indexed_bitvec)]
theorem wordListWrap {width : Nat} [NeZero width] {β : Type}
    (a : BitVec width) (ls : List β)
    (hyp : goodDimindex width ∧ 2 ^ width / (width / 8) < ls.length) :
    ∃ (x : β) (xs : List β) (y : β) (ys : List β) (b : BitVec width),
      Misc.wordList a ls = SetSep.star (Misc.wordList a (x :: xs)) (Misc.wordList b (y :: ys)) ∧
        b = a := by
  obtain ⟨good, long⟩ := hyp
  have pos := bytes_pos good
  set r := 2 ^ width / (width / 8) with hr
  have rpos : 0 < r := by rcases good with rfl | rfl <;> decide
  have wraps : a + bytesInWord width * BitVec.ofNat width r = a := by
    have zero : bytesInWord width * BitVec.ofNat width r = 0 := by
      rw [bytesInWord, BitVec.ofNat_mul_ofNat]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, hr]
      rcases good with rfl | rfl <;> decide
    rw [zero]
    simp
  have split := StackHeap.wordListAppend (ls.take r) (ls.drop r) a
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left (Nat.le_of_lt long), wraps]
    at split
  cases hTake : ls.take r with
  | nil =>
    have := congrArg List.length hTake
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt long)] at this
    simp only [List.length_nil] at this
    omega
  | cons x xs =>
    cases hDrop : ls.drop r with
    | nil =>
      have := congrArg List.length hDrop
      rw [List.length_drop] at this
      simp only [List.length_nil] at this
      omega
    | cons y ys =>
      rw [hTake, hDrop] at split
      exact ⟨x, xs, y, ys, a, split, rfl⟩

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩

private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) :=
  ⟨SetSep.starComm⟩

/-- Complete original separation rearrangement over arbitrary assertions on
an arbitrary heap-element type; HOL `*` is left-associated `STAR`. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "star_move_lemma"]
theorem starMoveLemma {α : Type} (p0 p1 p1' p2 p3 p4 : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star p0 p1) p1') p2) p3) p4 =
      SetSep.star p2 (SetSep.star (SetSep.star p1 p1') (SetSep.star p3 (SetSep.star p4 p0))) := by
  ac_rfl

end Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory
