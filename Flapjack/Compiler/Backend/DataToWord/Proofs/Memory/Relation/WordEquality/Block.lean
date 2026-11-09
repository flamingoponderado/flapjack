module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.List
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockEquality
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockExplode

@[expose] public section

/-! Block case of the source word-equality simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- An immediate block is empty and therefore cannot be a closure. -/
private theorem immediateBlockNotClosure {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List Value) (w : BitVec width) (vars : List (Value × WordLocW width))
    (rel : memoryRel conf be next refs space store memory domain ((.block stamp tag values, .word w) :: vars))
    (good : goodDimindex width) (low : w.getLsbD 0 = false) : ¬ isClosure tag values := by
  obtain ⟨w', loc, cases⟩ := memoryRel_blockImp conf be next refs space store memory domain
    stamp tag values (.word w) vars ⟨rel, good⟩
  have eq := WordLocW.word.inj loc
  subst w'
  by_cases empty : values = []
  · simp [isClosure, empty]
  · simp only [empty, ↓reduceIte] at cases
    obtain ⟨_, _, set, _⟩ := cases
    rw [low] at set
    contradiction

/-- A successful comparison of distinct blocks with an immediate first word
    returns false in one source step. -/
private theorem differentImmediateBlocks {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp1 tag1 stamp2 tag2 : Nat) (xs ys : List Value) (w1 w2 : BitVec width)
    (vars : List (Value × WordLocW width)) (n : Nat) (b : Bool)
    (rel : memoryRel conf be next refs space store memory domain
      ((.block stamp1 tag1 xs, .word w1) :: (.block stamp2 tag2 ys, .word w2) :: vars))
    (good : goodDimindex width) (different : w1 ≠ w2) (low : w1.getLsbD 0 = false)
    (sized : vbEqSize refs (.block stamp1 tag1 xs) (.block stamp2 tag2 ys) = some (n, b)) :
    n = 1 ∧ b = false := by
  have clos1 := immediateBlockNotClosure conf be next refs space store memory domain
    stamp1 tag1 xs w1 ((.block stamp2 tag2 ys, .word w2) :: vars) rel good low
  have mismatch := memoryRel_blocksDistinctImmediate conf be next refs space store memory domain
    stamp1 tag1 stamp2 tag2 xs ys w1 w2 vars ⟨rel, good, different, low⟩
  have noMatch : ¬ (tag1 = tag2 ∧ xs.length = ys.length) := by
    rintro ⟨tags, lengths⟩
    exact mismatch.elim (fun h => h lengths) (fun h => h tags)
  by_cases clos2 : isClosure tag2 ys
  · simp [vbEqSize, clos1, clos2] at sized
  · simpa [vbEqSize, clos1, clos2, noMatch] using sized.symm

/-- The same immediate-block observation when the second word is immediate. -/
private theorem differentImmediateBlocksRight {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp1 tag1 stamp2 tag2 : Nat) (xs ys : List Value) (w1 w2 : BitVec width)
    (vars : List (Value × WordLocW width)) (n : Nat) (b : Bool)
    (rel : memoryRel conf be next refs space store memory domain
      ((.block stamp1 tag1 xs, .word w1) :: (.block stamp2 tag2 ys, .word w2) :: vars))
    (good : goodDimindex width) (different : w1 ≠ w2) (low : w2.getLsbD 0 = false)
    (sized : vbEqSize refs (.block stamp1 tag1 xs) (.block stamp2 tag2 ys) = some (n, b)) :
    n = 1 ∧ b = false := by
  have tail := memoryRel_tail conf be next refs space store memory domain (.block stamp1 tag1 xs, .word w1)
    ((.block stamp2 tag2 ys, .word w2) :: vars) rel
  have clos2 := immediateBlockNotClosure conf be next refs space store memory domain
    stamp2 tag2 ys w2 vars tail good low
  have swap := memoryRel_swap conf be next refs space store memory domain
    (.block stamp1 tag1 xs, .word w1) (.block stamp2 tag2 ys, .word w2) vars rel
  have mismatch := memoryRel_blocksDistinctImmediate conf be next refs space store memory domain
    stamp2 tag2 stamp1 tag1 ys xs w2 w1 vars ⟨swap, good, Ne.symm different, low⟩
  have noMatch : ¬ (tag1 = tag2 ∧ xs.length = ys.length) := by
    rintro ⟨tags, lengths⟩
    exact mismatch.elim (fun h => h lengths.symm) (fun h => h tags.symm)
  by_cases clos1 : isClosure tag1 xs
  · simp [vbEqSize, clos1, clos2] at sized
  · simpa [vbEqSize, clos1, clos2, noMatch] using sized.symm

/-- Block case of the source equality simulation, assuming the original
    simultaneous induction instance for the field lists. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm0"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm0_block {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp1 tag1 stamp2 tag2 : Nat) (xs ys : List Value) (vars : List (Value × WordLocW width))
    (listIH : ∀ (refs : Spt (BvlSem.Ref Value)) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat),
      memoryRel conf be next refs space store memory domain
        (eqExplode w1 memory domain xs ++ eqExplode w2 memory domain ys ++ vars) ∧
      ys.length = xs.length ∧ xs.length < 2 ^ width ∧
      eqAssum w1 memory domain xs ∧ eqAssum w2 memory domain ys ∧
      vbEqSizeList refs xs ys = some (n, b) ∧
      clock = min (valuesDepth xs) (valuesDepth ys) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
      ∃ result remaining remainingClock,
        wordEqList conf store domain memory limit clock (BitVec.ofNat width xs.length) w1 w2 =
          some (result, remaining, remainingClock) ∧
        (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width)
    (refs : Spt (BvlSem.Ref Value)) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat) :
    memoryRel conf be next refs space store memory domain
        ((.block stamp1 tag1 xs, .word w1) :: (.block stamp2 tag2 ys, .word w2) :: vars) ∧
      vbEqSize refs (.block stamp1 tag1 xs) (.block stamp2 tag2 ys) = some (n, b) ∧
      clock = min (valueDepth (.block stamp1 tag1 xs)) (valueDepth (.block stamp2 tag2 ys)) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock, wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width := by
  rintro ⟨rel, sized, ck, bound, good⟩
  by_cases eq : w1 = w2
  · subst w2
    have erased := eraseValue refs (.block stamp1 tag1 xs) (.block stamp2 tag2 ys)
    rw [sized] at erased
    have doeq : doEq refs (.block stamp1 tag1 xs) (.block stamp2 tag2 ys) = .val b := by
      simpa [eraseCount] using erased.symm
    have truth := memoryRel_ptrEq conf be next refs space store memory domain
      (.block stamp1 tag1 xs) (.block stamp2 tag2 ys) (.word w1) b vars ⟨rel, doeq, good⟩
    refine ⟨1, limit, clock, ?_, ?_, by omega⟩
    · simp [wordEq]
    · simp [truth]
  · by_cases low1 : w1.getLsbD 0 = true
    · by_cases low2 : w2.getLsbD 0 = true
      · have tail := memoryRel_tail conf be next refs space store memory domain (.block stamp1 tag1 xs, .word w1)
          ((.block stamp2 tag2 ys, .word w2) :: vars) rel
        obtain ⟨p1, loc1, cases1⟩ := memoryRel_blockImp conf be next refs space store memory domain
          stamp1 tag1 xs (.word w1) ((.block stamp2 tag2 ys, .word w2) :: vars) ⟨rel, good⟩
        obtain ⟨p2, loc2, cases2⟩ := memoryRel_blockImp conf be next refs space store memory domain
          stamp2 tag2 ys (.word w2) vars ⟨tail, good⟩
        have wp1 := WordLocW.word.inj loc1
        have wp2 := WordLocW.word.inj loc2
        subst p1
        subst p2
        have nonempty1 : xs ≠ [] := by
          intro empty
          simp only [empty, ↓reduceIte] at cases1
          rw [low1] at cases1
          exact Bool.noConfusion cases1.2.1
        have nonempty2 : ys ≠ [] := by
          intro empty
          simp only [empty, ↓reduceIte] at cases2
          rw [low2] at cases2
          exact Bool.noConfusion cases2.2.1
        simp only [nonempty1, ↓reduceIte] at cases1
        simp only [nonempty2, ↓reduceIte] at cases2
        obtain ⟨a1, h1, _, h13, h12, addr1, mem1, dom1, decoded1, lenBound1, encoded1, _⟩ := cases1
        obtain ⟨a2, h2, _, h23, h22, addr2, mem2, dom2, decoded2, lenBound2, encoded2, _⟩ := cases2
        have mask : h1 &&& 12 = 0 := by exact bitAnd12EqZero h1 h12 h13
        have closWord1 := memoryRel_isClos conf be next refs space store memory domain stamp1 tag1 xs w1 a1 h1
          ((.block stamp2 tag2 ys, .word w2) :: vars) ⟨rel, low1, addr1, mem1, good⟩
        have closWord2 := memoryRel_isClos conf be next refs space store memory domain stamp2 tag2 ys w2 a2 h2
          vars ⟨tail, low2, addr2, mem2, good⟩
        by_cases closure1 : isClosure tag1 xs
        · by_cases closure2 : isClosure tag2 ys
          · simp [vbEqSize, closure1, closure2] at sized
            obtain ⟨rfl, rfl⟩ := sized
            have targetClosure := closWord1.mp closure1
            refine ⟨1, limit, clock, ?_, by simp, by simp⟩
            rw [wordEq]
            simp only [eq, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
            simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, targetClosure]
            intro no
            exact (no mask).elim
          · simp [vbEqSize, closure1, closure2] at sized
        · by_cases closure2 : isClosure tag2 ys
          · simp [vbEqSize, closure1, closure2] at sized
          · have targetNotClosure : ¬ wordIsClos conf h1 := fun h => closure1 (closWord1.mpr h)
            by_cases headerEq : h1 = h2
            · have config : conf.lenSize + 2 < width := by
                obtain ⟨heap, heapLimit, heapA, sp, sp1, gens, heapMem, _, _, _⟩ := rel
                have h := heapMem.2.2.2.2.1
                omega
              have parts := (encodeHeader_eq conf (4 * tag1) xs.length (4 * tag2) ys.length h1 h2
                ⟨encoded1, encoded2, config⟩).mp headerEq
              have tags : tag1 = tag2 := by omega
              have lengths : xs.length = ys.length := parts.2
              have closure1' : ¬ isClosure tag2 xs := by simpa [← tags] using closure1
              cases outcome : vbEqSizeList refs xs ys with
              | none => simp [vbEqSize, closure1', closure2, tags, lengths, outcome] at sized
              | some pair =>
                obtain ⟨count, answer⟩ := pair
                simp [vbEqSize, closure1', closure2, tags, lengths, outcome] at sized
                obtain ⟨rfl, rfl⟩ := sized
                obtain ⟨first, assum1⟩ := memoryRel_blockExplode conf be next refs space store memory domain
                  stamp1 tag1 xs w1 a1 ((.block stamp2 tag2 ys, .word w2) :: vars) ⟨rel, low1, addr1, good⟩
                have middle : memoryRel conf be next refs space store memory domain
                    ((.block stamp2 tag2 ys, .word w2) ::
                      (eqExplode (a1 + StackRemove.bytesInWord width) memory domain xs ++ vars)) := by
                  apply memoryRel_rearrange conf be next refs space store memory domain _ _ ?_ first
                  intro pair member
                  simp only [List.mem_append, List.mem_cons] at member ⊢
                  tauto
                obtain ⟨second, assum2⟩ := memoryRel_blockExplode conf be next refs space store memory domain
                  stamp2 tag2 ys w2 a2 (eqExplode (a1 + StackRemove.bytesInWord width) memory domain xs ++ vars)
                  ⟨middle, low2, addr2, good⟩
                have both : memoryRel conf be next refs space store memory domain
                    (eqExplode (a1 + StackRemove.bytesInWord width) memory domain xs ++
                      eqExplode (a2 + StackRemove.bytesInWord width) memory domain ys ++ vars) := by
                  apply memoryRel_rearrange conf be next refs space store memory domain _ _ ?_ second
                  intro pair member
                  simp only [List.mem_append] at member ⊢
                  tauto
                have dimPositive : 0 < 2 ^ width := Nat.two_pow_pos width
                have power : 2 ^ (width - 4) ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
                have lenSmall : xs.length < 2 ^ width := lt_of_lt_of_le lenBound1 power
                have enough : count * 2 ^ width < limit - 1 := by
                  simp only [Nat.add_mul, Nat.one_mul] at bound
                  omega
                have clockEq : clock = min (valuesDepth xs) (valuesDepth ys) := by simpa [valueDepth] using ck
                obtain ⟨result, remaining, remainingClock, eval, correct, remainingBound⟩ :=
                  listIH refs (limit - 1) clock answer (a1 + StackRemove.bytesInWord width)
                    (a2 + StackRemove.bytesInWord width) count
                    ⟨both, lengths.symm, lenSmall, assum1, assum2, outcome, clockEq, enough, good⟩
                rw [← headerEq] at mem2
                refine ⟨result, remaining, remainingClock, ?_, correct, ?_⟩
                · rw [wordEq]
                  simp only [eq, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
                  simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, targetNotClosure,
                    show limit ≠ 0 by omega, decoded1, eval]
                  intro no
                  exact (no mask).elim
                · simp only [Nat.add_mul, Nat.one_mul]
                  omega
            · have noMatch : ¬ (tag1 = tag2 ∧ xs.length = ys.length) := by
                rintro ⟨tags, lengths⟩
                have h : encodeHeader conf (4 * tag1) xs.length = some h2 := by
                  simpa [tags, lengths] using encoded2
                exact headerEq (Option.some.inj (encoded1.symm.trans h))
              simp [vbEqSize, closure1, closure2, noMatch] at sized
              obtain ⟨rfl, rfl⟩ := sized
              refine ⟨0, limit, clock, ?_, ?_, by omega⟩
              · rw [wordEq]
                simp only [eq, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
                simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, targetNotClosure, headerEq]
              · rcases good with hw | hw <;> subst width <;> simp
      · have clear : w2.getLsbD 0 = false := by cases h : w2.getLsbD 0 <;> simp_all
        obtain ⟨rfl, rfl⟩ := differentImmediateBlocksRight conf be next refs space store memory domain
          stamp1 tag1 stamp2 tag2 xs ys w1 w2 vars n b rel good eq clear sized
        refine ⟨0, limit, clock, ?_, ?_, by omega⟩
        · simp [wordEq, eq, clear]
        · rcases good with hw | hw <;> subst width <;> simp
    · have clear : w1.getLsbD 0 = false := by cases h : w1.getLsbD 0 <;> simp_all
      obtain ⟨rfl, rfl⟩ := differentImmediateBlocks conf be next refs space store memory domain
        stamp1 tag1 stamp2 tag2 xs ys w1 w2 vars n b rel good eq clear sized
      refine ⟨0, limit, clock, ?_, ?_, by omega⟩
      · simp [wordEq, eq, clear]
      · rcases good with hw | hw <;> subst width <;> simp

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
