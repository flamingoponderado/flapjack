module

public import Flapjack.Misc.SetSep.Read
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.XorWords
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteStore
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataToWord.Proofs.Memory


@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Read the head of a separated word list; Flapjack infrastructure for the XOR proof. -/
private theorem readHead {width : Nat} [NeZero width] (a : BitVec width) (x : BitVec width)
    (xs : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (sep : SetSep.star (Misc.wordList a (.word x :: xs)) frame
      (SetSep.fun2Set (m, fun k => dm k = true))) :
    readWord dm m a = (x, true) := by
  simp only [Misc.wordList, ← SetSep.starAssoc] at sep
  have h := SetSep.readFun2Set a (.word x) _ m (fun k => dm k = true) sep
  simp [readWord, h.1, h.2, wordSemTheWord, wordSemIsWordLoc]

/-- Read the heads of two separated word lists; Flapjack infrastructure for the XOR proof. -/
private theorem twoHeads {width : Nat} [NeZero width] (a b : BitVec width) (x y : BitVec width)
    (xs ys : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (sep : SetSep.star (SetSep.star (Misc.wordList a (.word x :: xs)) (Misc.wordList b (.word y :: ys))) frame
      (SetSep.fun2Set (m, fun k => dm k = true))) :
    readWord dm m a = (x, true) ∧ readWord dm m b = (y, true) := by
  have first : SetSep.star (Misc.wordList a (.word x :: xs))
      (SetSep.star (Misc.wordList b (.word y :: ys)) frame) (SetSep.fun2Set (m, fun k => dm k = true)) := by
    rw [SetSep.starAssoc]; exact sep
  have second : SetSep.star (Misc.wordList b (.word y :: ys))
      (SetSep.star (Misc.wordList a (.word x :: xs)) frame) (SetSep.fun2Set (m, fun k => dm k = true)) := by
    rw [SetSep.starAssoc, SetSep.starComm (Misc.wordList b (.word y :: ys)) (Misc.wordList a (.word x :: xs))]
    exact sep
  exact ⟨readHead a x xs _ m dm first, readHead b y ys _ m dm second⟩

/-- Update the destination head while retaining the source and frame; Flapjack infrastructure for the XOR proof. -/
private theorem writeSecondHead {width : Nat} [NeZero width] (a b : BitVec width) (x y z : BitVec width)
    (xs ys : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (sep : SetSep.star (SetSep.star (Misc.wordList a (.word x :: xs)) (Misc.wordList b (.word y :: ys))) frame
      (SetSep.fun2Set (m, fun k => dm k = true))) :
    SetSep.star (SetSep.star (Misc.wordList a (.word x :: xs)) (Misc.wordList b (.word z :: ys))) frame
      (SetSep.fun2Set ((fun k => if k = b then .word z else m k), fun k => dm k = true)) := by
  have second : SetSep.star (Misc.wordList b (.word y :: ys))
      (SetSep.star (Misc.wordList a (.word x :: xs)) frame) (SetSep.fun2Set (m, fun k => dm k = true)) := by
    rw [SetSep.starAssoc, SetSep.starComm (Misc.wordList b (.word y :: ys)) (Misc.wordList a (.word x :: xs))]
    exact sep
  have result := wordList_write b (.word y :: ys) 0 (.word z) m (fun k => dm k = true)
    (SetSep.star (Misc.wordList a (.word x :: xs)) frame) (by simp) second
  simp only [List.set_cons_zero] at result
  simp at result
  rw [SetSep.starAssoc, SetSep.starComm (Misc.wordList b (.word z :: ys)) (Misc.wordList a (.word x :: xs))] at result
  exact result

/-- Read an indexed word from a separated list; Flapjack infrastructure for the XOR proof. -/
private theorem readAt {width : Nat} [NeZero width] (a : BitVec width) (xs : List (WordLocW width))
    (i : Nat) (bound : i < xs.length) (value : BitVec width) (eq : xs[i] = .word value)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (sep : SetSep.star (Misc.wordList a xs) frame (SetSep.fun2Set (m, fun k => dm k = true))) :
    readWord dm m (a + BitVec.ofNat width i * StackRemove.bytesInWord width) = (value, true) := by
  have graph : SetSep.fun2Set (m, fun k => dm k = true)
      (a + BitVec.ofNat width i * StackRemove.bytesInWord width, .word value) := by
    obtain ⟨left, right, split, assertion, other⟩ := sep
    rw [← split.1]
    left
    simpa [eq] using wordList_indexMember xs i bound a left assertion
  have fact := (SetSep.fun2SetThm m (fun k => dm k = true) _ _).mp graph
  simp [readWord, fact.1, fact.2, wordSemTheWord, wordSemIsWordLoc]

/-- Update the second destination word while retaining the source and frame; Flapjack infrastructure for the XOR proof. -/
private theorem writeSecondNext {width : Nat} [NeZero width] (a b : BitVec width) (xs : List (WordLocW width))
    (y0 y1 z : BitVec width) (ys : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (sep : SetSep.star (SetSep.star (Misc.wordList a xs) (Misc.wordList b (.word y0 :: .word y1 :: ys))) frame
      (SetSep.fun2Set (m, fun k => dm k = true))) :
    SetSep.star (SetSep.star (Misc.wordList a xs) (Misc.wordList b (.word y0 :: .word z :: ys))) frame
      (SetSep.fun2Set ((fun k => if k = b + wordSemBytesInWord then .word z else m k), fun k => dm k = true)) := by
  have second : SetSep.star (Misc.wordList b (.word y0 :: .word y1 :: ys))
      (SetSep.star (Misc.wordList a xs) frame) (SetSep.fun2Set (m, fun k => dm k = true)) := by
    rw [SetSep.starAssoc, SetSep.starComm (Misc.wordList b (.word y0 :: .word y1 :: ys)) (Misc.wordList a xs)]
    exact sep
  have result := wordList_write b (.word y0 :: .word y1 :: ys) 1 (.word z) m (fun k => dm k = true)
    (SetSep.star (Misc.wordList a xs) frame) (by simp) second
  simp only [List.set_cons_succ, List.set_cons_zero] at result
  simp [StackRemove.bytesInWord] at result
  rw [SetSep.starAssoc, SetSep.starComm (Misc.wordList b (.word y0 :: .word z :: ys)) (Misc.wordList a xs)] at result
  exact result

/-- Permute separated assertions while preserving a frame; Flapjack infrastructure for the XOR proof. -/
private theorem starPerm {α : Type} (p q r s t : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star p q) (SetSep.star r s)) t =
      SetSep.star (SetSep.star q s) (SetSep.star (SetSep.star p r) t) := by
  let : Std.Associative (@SetSep.star α) := ⟨fun a b c => (SetSep.starAssoc a b c).symm⟩
  let : Std.Commutative (@SetSep.star α) := ⟨fun a b => SetSep.starComm a b⟩
  ac_rfl



/-- XORing disjoint separated word lists preserves the source and frame while storing the full result. The unused `be` binder retains its independent HOL type. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "xor_words_word_list"
  (words_as_type_indexed_bitvec)]
theorem xorWordsWordList {width : Nat} [NeZero width] {β : Type} (xs ys res : List (BitVec width))
    (a b : BitVec width) (_be : β) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (h : xorWords xs ys = some res) (good : goodDimindex width) (bound : xs.length < 2 ^ width)
    (sep : SetSep.star (SetSep.star (Misc.wordList a (xs.map WordLocW.word))
      (Misc.wordList b (ys.map WordLocW.word))) frame (SetSep.fun2Set (m, fun k => dm k = true))) :
    ∃ m1, SetSep.star (SetSep.star (Misc.wordList a (xs.map WordLocW.word))
      (Misc.wordList b (res.map WordLocW.word))) frame (SetSep.fun2Set (m1, fun k => dm k = true)) ∧
      wordXorBytes a b (BitVec.ofNat width xs.length) dm m = some m1 := by
  induction xs using List.twoStepInduction generalizing ys res a b frame m with
  | nil =>
    simp [xorWords] at h
    subst res
    refine ⟨m, sep, ?_⟩
    rcases good with hw | hw <;> subst width <;> rw [wordXorBytes] <;> simp [goodDimindex]
  | singleton x =>
    cases ys with
    | nil => simp [xorWords] at h
    | cons y ys =>
      simp [xorWords] at h
      subst res
      have reads := twoHeads a b x y [] (ys.map WordLocW.word) frame m dm (by simpa using sep)
      have writes := writeSecondHead a b x y (x ^^^ y) [] (ys.map WordLocW.word) frame m dm (by simpa using sep)
      refine ⟨(fun k => if k = b then .word (x ^^^ y) else m k), by simpa using writes, ?_⟩
      rcases good with hw | hw <;> subst width <;> rw [wordXorBytes] <;> simp [reads.1, reads.2, goodDimindex]
  | cons_cons x x2 xs ih ih1 =>
    cases ys with
    | nil => simp [xorWords] at h
    | cons y ys =>
      cases ys with
      | nil => simp [xorWords] at h
      | cons y2 ys =>
        simp only [xorWords] at h
        cases hx : xorWords xs ys with
        | none => simp [hx] at h
        | some rest =>
          simp [hx] at h
          subst res
          have sep0 : SetSep.star (SetSep.star
              (Misc.wordList a (.word x :: .word x2 :: xs.map WordLocW.word))
              (Misc.wordList b (.word y :: .word y2 :: ys.map WordLocW.word))) frame
              (SetSep.fun2Set (m, fun k => dm k = true)) := by simpa using sep
          have r12 := twoHeads a b x y (.word x2 :: xs.map WordLocW.word)
            (.word y2 :: ys.map WordLocW.word) frame m dm sep0
          have srcSep : SetSep.star (Misc.wordList a (.word x :: .word x2 :: xs.map WordLocW.word))
              (SetSep.star (Misc.wordList b (.word y :: .word y2 :: ys.map WordLocW.word)) frame)
              (SetSep.fun2Set (m, fun k => dm k = true)) := by rw [SetSep.starAssoc]; exact sep0
          have dstSep : SetSep.star (Misc.wordList b (.word y :: .word y2 :: ys.map WordLocW.word))
              (SetSep.star (Misc.wordList a (.word x :: .word x2 :: xs.map WordLocW.word)) frame)
              (SetSep.fun2Set (m, fun k => dm k = true)) := by
            rw [SetSep.starAssoc, SetSep.starComm (Misc.wordList b (.word y :: .word y2 :: ys.map WordLocW.word))
              (Misc.wordList a (.word x :: .word x2 :: xs.map WordLocW.word))]
            exact sep0
          have r3 : readWord dm m (a + wordSemBytesInWord) = (x2, true) := by
            simpa [wordSemBytesInWord, StackRemove.bytesInWord] using
              readAt a (.word x :: .word x2 :: xs.map WordLocW.word) 1 (by simp) x2 (by simp) _ m dm srcSep
          have r4 : readWord dm m (b + wordSemBytesInWord) = (y2, true) := by
            simpa [wordSemBytesInWord, StackRemove.bytesInWord] using
              readAt b (.word y :: .word y2 :: ys.map WordLocW.word) 1 (by simp) y2 (by simp) _ m dm dstSep
          let m1 : BitVec width → WordLocW width := fun k => if k = b then .word (x ^^^ y) else m k
          let m2 : BitVec width → WordLocW width := fun k => if k = b + wordSemBytesInWord then .word (x2 ^^^ y2) else m1 k
          have sep1 := writeSecondHead a b x y (x ^^^ y) (.word x2 :: xs.map WordLocW.word)
            (.word y2 :: ys.map WordLocW.word) frame m dm sep0
          have sep2 := writeSecondNext a b (.word x :: .word x2 :: xs.map WordLocW.word)
            (x ^^^ y) y2 (x2 ^^^ y2) (ys.map WordLocW.word) frame m1 dm (by simpa [m1] using sep1)
          have srcSplit : Misc.wordList a (.word x :: .word x2 :: xs.map WordLocW.word) =
              SetSep.star (Misc.wordList a [.word x, .word x2])
                (Misc.wordList (a + 2 * wordSemBytesInWord) (xs.map WordLocW.word)) := by
            simpa [wordSemBytesInWord, StackRemove.bytesInWord] using
              wordListAppend [.word x, .word x2] (xs.map WordLocW.word) a
          have dstSplit : Misc.wordList b (.word (x ^^^ y) :: .word (x2 ^^^ y2) :: ys.map WordLocW.word) =
              SetSep.star (Misc.wordList b [.word (x ^^^ y), .word (x2 ^^^ y2)])
                (Misc.wordList (b + 2 * wordSemBytesInWord) (ys.map WordLocW.word)) := by
            simpa [wordSemBytesInWord, StackRemove.bytesInWord] using
              wordListAppend [.word (x ^^^ y), .word (x2 ^^^ y2)] (ys.map WordLocW.word) b
          let tailFrame := SetSep.star (SetSep.star (Misc.wordList a [.word x, .word x2])
            (Misc.wordList b [.word (x ^^^ y), .word (x2 ^^^ y2)])) frame
          have tailSep : SetSep.star (SetSep.star
              (Misc.wordList (a + 2 * wordSemBytesInWord) (xs.map WordLocW.word))
              (Misc.wordList (b + 2 * wordSemBytesInWord) (ys.map WordLocW.word))) tailFrame
              (SetSep.fun2Set (m2, fun k => dm k = true)) := by
            dsimp [m2, tailFrame]
            rw [srcSplit, dstSplit, starPerm] at sep2
            exact sep2
          have tailBound : xs.length < 2 ^ width := by simp at bound; omega
          obtain ⟨mf, finalSep, finalRun⟩ := ih ys rest (a + 2 * wordSemBytesInWord)
            (b + 2 * wordSemBytesInWord) tailFrame m2 hx tailBound tailSep
          refine ⟨mf, ?_, ?_⟩
          · dsimp [tailFrame] at finalSep
            rw [← starPerm] at finalSep
            have finalSplit : Misc.wordList b (.word (x ^^^ y) :: .word (x2 ^^^ y2) :: rest.map WordLocW.word) =
                SetSep.star (Misc.wordList b [.word (x ^^^ y), .word (x2 ^^^ y2)])
                  (Misc.wordList (b + 2 * wordSemBytesInWord) (rest.map WordLocW.word)) := by
              simpa [wordSemBytesInWord, StackRemove.bytesInWord] using
                wordListAppend [.word (x ^^^ y), .word (x2 ^^^ y2)] (rest.map WordLocW.word) b
            simpa [List.map_cons, srcSplit, finalSplit, BitVec.ofNat] using finalSep
          · have countBound : xs.length + 2 < 2 ^ width := by simpa [List.length_cons] using bound
            have countNat : (BitVec.ofNat width (xs.length + 2)).toNat = xs.length + 2 := by
              simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
            have twoNat : (2 : BitVec width).toNat = 2 := by
              rcases good with hw | hw <;> subst width <;> decide
            have notSmall : ¬ ((BitVec.ofNat width (xs.length + 2)).toNat < (2 : BitVec width).toNat ∨ ¬ goodDimindex width) := by
              simp only [not_or, not_not, countNat, twoNat, good, and_true]
              omega
            have countSub : BitVec.ofNat width (xs.length + 2) - 2 = BitVec.ofNat width xs.length := by
              simp only [BitVec.ofNat_add]
              simp
            change wordXorBytes a b (BitVec.ofNat width (xs.length + 2)) dm m = some mf
            rw [wordXorBytes]
            simp only [notSmall, ↓reduceIte, r12.1, r12.2, r3, r4, Bool.true_and]
            simpa only [countSub, m1, m2] using finalRun

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
