module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockElement
public import Flapjack.Misc.Multiword.Compare

@[expose] public section

/-! Correctness of the word-list comparison loop. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Misc.Multiword
open Classical
noncomputable section

/-- A nonempty snoc list has its appended element as HOL LAST (Flapjack helper). -/
private theorem lastSnoc {α : Type} [Nonempty α] (xs : List α) (x : α) : holLast (xs ++ [x]) = x := by
  induction xs with
  | nil => simp [holLast]
  | cons a xs ih =>
    cases xs with
    | nil => simp [holLast]
    | cons b xs => simpa [holLast] using ih

/-- Compare lists from their last elements (Flapjack helper). -/
private theorem cmpSnoc {width : Nat} [NeZero width] (xs ys : List (BitVec width)) (x y : BitVec width) :
    mwCmp (xs ++ [x]) (ys ++ [y]) = if x = y then mwCmp xs ys else some (decide (x < y)) := by
  rw [mwCmp]
  simp [lastSnoc]

/-- Extract the last word and retain the rest of a separated list (Flapjack helper). -/
private theorem snocFrame {width : Nat} [NeZero width] (xs : List (BitVec width)) (x : BitVec width)
    (base : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (h : SetSep.star (Misc.wordList (base + StackRemove.bytesInWord width)
      ((xs ++ [x]).map WordLocW.word)) frame (SetSep.fun2Set (memory, fun a => domain a = true))) :
    let lastAddr := base + StackRemove.bytesInWord width * BitVec.ofNat width (xs.length + 1)
    memory lastAddr = .word x ∧ domain lastAddr = true ∧
      ∃ rest, SetSep.star (Misc.wordList (base + StackRemove.bytesInWord width) (xs.map WordLocW.word)) rest
        (SetSep.fun2Set (memory, fun a => domain a = true)) := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.length_map, wordListAppend, Misc.wordList,
    SetSep.starComm (SetSep.one _) SetSep.emp, StackRemove.StackHeap.starEmptyLeft] at h
  have addressEq : base + StackRemove.bytesInWord width +
      BitVec.ofNat width xs.length * StackRemove.bytesInWord width =
      base + StackRemove.bytesInWord width * BitVec.ofNat width (xs.length + 1) := by
    simp only [BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one]
    ac_rfl
  rw [addressEq] at h
  rw [← SetSep.starAssoc] at h
  have saved := h
  obtain ⟨before, last, split1, _, ⟨one, rest, split2, singleton, _⟩⟩ := h
  have inOne : one (base + StackRemove.bytesInWord width * BitVec.ofNat width (xs.length + 1), .word x) := by
    rw [singleton]
  have inLast : last (base + StackRemove.bytesInWord width * BitVec.ofNat width (xs.length + 1), .word x) := by
    rw [← split2.1]; exact Or.inl inOne
  have inWhole : SetSep.fun2Set (memory, fun a => domain a = true)
      (base + StackRemove.bytesInWord width * BitVec.ofNat width (xs.length + 1), .word x) := by
    rw [← split1.1]; exact Or.inr inLast
  obtain ⟨contents, inDomain⟩ := (SetSep.fun2SetThm memory _ _ _).mp inWhole
  exact ⟨contents, inDomain, _, saved⟩

/-- The word loop implements multiword comparison over separated word lists. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_cmp_loop_thm"
  (words_as_type_indexed_bitvec)]
theorem wordCmpLoopThm {width : Nat} [NeZero width]
    (xs ys : List (BitVec width)) (f1 f2 : ((BitVec width × WordLocW width) → Prop) → Prop)
    (a1 a2 : BitVec width) (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width) :
    xs.length = ys.length ∧ xs.length < 2 ^ width ∧
    SetSep.star (Misc.wordList (a1 + StackRemove.bytesInWord width) (xs.map WordLocW.word)) f1
      (SetSep.fun2Set (memory, fun a => domain a = true)) ∧
    SetSep.star (Misc.wordList (a2 + StackRemove.bytesInWord width) (ys.map WordLocW.word)) f2
      (SetSep.fun2Set (memory, fun a => domain a = true)) →
    wordCmpLoop (BitVec.ofNat width xs.length)
      (a1 + StackRemove.bytesInWord width * BitVec.ofNat width xs.length)
      (a2 + StackRemove.bytesInWord width * BitVec.ofNat width xs.length) domain memory =
    some (match mwCmp xs ys with | none => 1 | some true => 0 | some false => 2) := by
  induction n : xs.length using Nat.strong_induction_on generalizing xs ys f1 f2 a1 a2 with
  | h n ih =>
    intro ⟨lengths, bound, h1, h2⟩
    simp only [← n] at lengths bound ⊢
    rcases List.eq_nil_or_concat xs with empty | ⟨xs', x, eq⟩
    · subst xs
      have : ys = [] := by simpa using lengths.symm
      subst ys
      rw [wordCmpLoop, mwCmp]
      simp
    · simp only [List.concat_eq_append] at eq
      subst xs
      rcases List.eq_nil_or_concat ys with empty | ⟨ys', y, eq⟩
      · subst ys
        simp at lengths
      · simp only [List.concat_eq_append] at eq
        subst ys
        simp only [List.length_append, List.length_singleton] at lengths bound n ⊢
        obtain ⟨m1, d1, fr1, prefix1⟩ := snocFrame xs' x a1 f1 memory domain h1
        obtain ⟨m2, d2, fr2, prefix2⟩ := snocFrame ys' y a2 f2 memory domain h2
        have prefixLen : xs'.length = ys'.length := by omega
        rw [← prefixLen] at m2 d2
        rw [cmpSnoc]
        have nonzero : BitVec.ofNat width (xs'.length + 1) ≠ 0 := by
          intro eq
          have ht := congrArg BitVec.toNat eq
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at ht
        have sub : BitVec.ofNat width (xs'.length + 1) - 1 = BitVec.ofNat width xs'.length := by
          rw [BitVec.ofNat_add]
          change (BitVec.ofNat width xs'.length + (1 : BitVec width)) - 1 = _
          exact BitVec.add_sub_cancel _ _
        have offset (a : BitVec width) :
            a + StackRemove.bytesInWord width * BitVec.ofNat width (xs'.length + 1) - StackRemove.bytesInWord width =
              a + StackRemove.bytesInWord width * BitVec.ofNat width xs'.length := by
          rw [BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one, ← BitVec.add_assoc, BitVec.add_sub_cancel]
        have inductionResult := ih xs'.length (by omega) xs' ys' fr1 fr2 a1 a2
          rfl ⟨prefixLen, by omega, prefix1, prefix2⟩
        rw [wordCmpLoop]
        simp only [nonzero, ↓reduceIte, d1, d2, true_and, m1, m2, sub, offset]
        by_cases eq : x = y
        · simp [eq, inductionResult]
        · by_cases lt : x < y <;> simp [eq, lt]

/-- Equal-length multiword values have equal magnitudes exactly when their words match. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "mw2n_inj"
  (words_as_type_indexed_bitvec)]
theorem mw2nInj {width : Nat} [NeZero width] : ∀ xs ys : List (BitVec width),
    xs.length = ys.length → (mw2n xs = mw2n ys ↔ xs = ys) := by
  intro xs
  induction xs with
  | nil =>
    intro ys len
    have : ys = [] := by simpa using len.symm
    subst ys
    simp
  | cons x xs ih =>
    intro ys len
    cases ys with
    | nil => simp at len
    | cons y ys =>
      have len' : xs.length = ys.length := by simpa using len
      constructor
      · intro equal
        have mods := congrArg (fun n => n % (2 ^ width)) equal
        simp only [mw2n, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
          Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at mods
        have xy : x = y := BitVec.eq_of_toNat_eq mods
        subst y
        simp only [mw2n] at equal
        have tailEqual : mw2n xs = mw2n ys := by
          apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos width)
          omega
        have tails := (ih ys len').1 tailEqual
        simp [tails]
      · intro equal
        cases equal
        rfl

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
