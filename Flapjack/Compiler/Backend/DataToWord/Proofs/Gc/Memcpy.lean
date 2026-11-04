import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteStore
import Flapjack.Compiler.Backend.WordGcFunctions

/-! Separation-logic correctness of the collector's word copying loop. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem rearrange {α : Type} (f a x b y : (α → Prop) → Prop) :
    SetSep.star (SetSep.star f (SetSep.star a x)) (SetSep.star b y) =
      SetSep.star b (SetSep.star (SetSep.star (SetSep.star f a) x) y) := by
  rw [← SetSep.starAssoc, ← SetSep.starAssoc, ← SetSep.starAssoc,
    star_swap_first x b, star_swap_first a b, star_swap_first f b,
    SetSep.starAssoc, SetSep.starAssoc]
  simp only [← SetSep.starAssoc]

/-- The collector copy loop preserves both separated lists and its frame,
copies the source values, and advances the destination by the copied length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "memcpy_thm"
  (words_as_type_indexed_bitvec)]
theorem memcpyCorrect {width : Nat} [NeZero width] {β : Type}
    (xs : List β) :
    ∀ (a : BitVec width) (c : Bool) (b : BitVec width)
      (m m1 : BitVec width → β) (dm : BitVec width → Bool)
      (b1 : BitVec width) (ys : List β)
      (frame : ((BitVec width × β) → Prop) → Prop),
      memcpy (BitVec.ofNat width xs.length) a b m dm = (b1, m1, c) →
      ys.length = xs.length → xs.length < 2 ^ width →
      SetSep.star (SetSep.star frame (Misc.wordList a xs)) (Misc.wordList b ys)
        (SetSep.fun2Set (m, fun address => dm address = true)) →
      SetSep.star (SetSep.star frame (Misc.wordList a xs)) (Misc.wordList b xs)
          (SetSep.fun2Set (m1, fun address => dm address = true)) ∧
        b1 = b + BitVec.ofNat width xs.length * wordSemBytesInWord ∧ c = true := by
  classical
  induction xs with
  | nil =>
    intro a c b m m1 dm b1 ys frame run length _ separated
    cases ys with
    | cons y ys => simp at length
    | nil =>
      simp only [List.length_nil, memcpy_zero, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨separated, by simp, rfl⟩
  | cons x xs ih =>
    intro a c b m m1 dm b1 ys frame run length bound separated
    cases ys with
    | nil => simp at length
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at length
      have countBound : xs.length + 1 < 2 ^ width := by simpa using bound
      have nonzero : BitVec.ofNat width (xs.length + 1) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] at h'
      have minus : BitVec.ofNat width (xs.length + 1) - 1 = BitVec.ofNat width xs.length := by
        rw [BitVec.ofNat_add]
        simp
      simp only [Misc.wordList] at separated
      rw [rearrange] at separated
      have sourceGraph : SetSep.fun2Set (m, fun address => dm address = true) (a, x) := by
        rcases separated with ⟨left, right, outer, _, inner⟩
        rcases inner with ⟨faX, yy, part, fa, _⟩
        rcases fa with ⟨fA, xx, part2, fA, _⟩
        rcases fA with ⟨ff, aa, part3, _, aaEq⟩
        rw [← outer.1, ← part.1, ← part2.1, ← part3.1]
        exact Or.inr (Or.inl (Or.inl (Or.inr (by rw [aaEq]))))
      have sourceFacts := (SetSep.fun2SetThm m _ a x).mp sourceGraph
      have destGraph : SetSep.fun2Set (m, fun address => dm address = true) (b, y) := by
        rcases separated with ⟨left, right, outer, one, _⟩
        rw [← outer.1]
        exact Or.inl (by rw [one])
      have destFacts := (SetSep.fun2SetThm m _ b y).mp destGraph
      have written := SetSep.writeFun2Set x b y _ m (fun address => dm address = true) separated
      have written' : SetSep.star (SetSep.star (SetSep.star (SetSep.star frame (SetSep.one (a, x)))
          (Misc.wordList (a + StackRemove.bytesInWord width) xs))
          (SetSep.one (b, x))) (Misc.wordList (b + StackRemove.bytesInWord width) ys)
          (SetSep.fun2Set (gcUpdate b (m a) m, fun address => dm address = true)) := by
        rw [← SetSep.starAssoc, SetSep.starComm (Misc.wordList (b + StackRemove.bytesInWord width) ys),
          SetSep.starAssoc] at written
        have graphEq : SetSep.fun2Set (gcUpdate b (m a) m, fun address => dm address = true) =
            SetSep.fun2Set ((fun key => @ite _ (key = b) (Classical.propDecidable _) x (m key)), fun address => dm address = true) := by
          funext entry
          rcases entry with ⟨key, value⟩
          simp only [SetSep.fun2SetThm, gcUpdate, sourceFacts.1]
          by_cases h : key = b
          · subst key
            simp only [ite_true]
          · have h' : b ≠ key := Ne.symm h
            simp only [h, h', ite_false]
        rw [graphEq]
        exact written
      have tailBound : xs.length < 2 ^ width := by omega
      simp only [List.length_cons] at run
      rw [memcpy_of_ne nonzero, minus] at run
      generalize tailRun : memcpy (BitVec.ofNat width xs.length) (a + wordSemBytesInWord)
          (b + wordSemBytesInWord) (gcUpdate b (m a) m) dm = result at run
      rcases result with ⟨endAddr, endMem, flag⟩
      simp only [sourceFacts.2, destFacts.2, Bool.and_true, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      have result := ih (a + wordSemBytesInWord) flag (b + wordSemBytesInWord)
            (gcUpdate b (m a) m) endMem dm endAddr ys
            (SetSep.star (SetSep.star frame (SetSep.one (a, x))) (SetSep.one (b, x)))
            tailRun length tailBound (by
              simpa [wordSemBytesInWord, StackRemove.bytesInWord, ← SetSep.starAssoc,
                star_swap_first] using written')
      obtain ⟨result, endEq, flagEq⟩ := result
      refine ⟨?_, ?_, flagEq⟩
      · simp only [Misc.wordList]
        simp only [← SetSep.starAssoc] at result ⊢
        rw [star_swap_first (SetSep.one (b, x))
          (Misc.wordList (a + wordSemBytesInWord) xs)
          (Misc.wordList (b + wordSemBytesInWord) xs)] at result
        simpa only [wordSemBytesInWord, StackRemove.bytesInWord] using result
      · simp only [List.length_cons, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
        rw [endEq]
        ac_rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
