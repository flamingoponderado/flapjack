module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockExplode
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueEquality
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CodePointer

@[expose] public section

/-! List cases of the source word-equality simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- A successful value comparison excludes location-valued roots. -/
private theorem successfulPairWords {width : Nat} [NeZero width]
    (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (x y : Value) (lx ly : WordLocW width) (vars : List (Value × WordLocW width))
    (n : Nat) (b : Bool)
    (related : memoryRel conf be next refs space store memory domain ((x, lx) :: (y, ly) :: vars))
    (sized : vbEqSize refs x y = some (n, b)) :
    (∃ w, lx = .word w) ∧ ∃ w, ly = .word w := by
  have notRefX : ∀ p, x ≠ .refPtr false p := by
    intro p h
    subst x
    cases y <;> simp [vbEqSize] at sized
  have notRefY : ∀ p, y ≠ .refPtr false p := by
    intro p h
    subst y
    cases x <;> simp [vbEqSize] at sized
  have notCodeX : ∀ p, x ≠ .codePtr p := by
    intro p h
    subst x
    cases y <;> simp [vbEqSize] at sized
  have notCodeY : ∀ p, y ≠ .codePtr p := by
    intro p h
    subst y
    cases x <;> simp [vbEqSize] at sized
  constructor
  · cases lx with
    | word w => exact ⟨w, rfl⟩
    | loc label offset =>
      exact (notCodeX label (memoryRel_loc conf be next refs space store memory domain x label offset
        ((y, ly) :: vars) ⟨related, notRefX⟩)).elim
  · cases ly with
    | word w => exact ⟨w, rfl⟩
    | loc label offset =>
      have tail := memoryRel_tail conf be next refs space store memory domain (x, lx) ((y, .loc label offset) :: vars) related
      exact (notCodeY label (memoryRel_loc conf be next refs space store memory domain y label offset
        vars ⟨tail, notRefY⟩)).elim

/-- Empty-list case of the source word-equality simulation. The two unused
    type parameters retain the independently polymorphic HOL binders. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm0"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm0_listNil {width : Nat} [NeZero width] {β γ : Type}
    (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (_t1 : β) (_t2 : γ) (n : Nat)
    (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain
        (eqExplode w1 memory domain [] ++ eqExplode w2 memory domain [] ++ vars) ∧
      ([] : List Value).length = ([] : List Value).length ∧
      ([] : List Value).length < 2 ^ width ∧
      eqAssum w1 memory domain ([] : List Value) ∧ eqAssum w2 memory domain ([] : List Value) ∧
      vbEqSizeList refs [] [] = some (n, b) ∧
      clock = min (valuesDepth []) (valuesDepth []) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock,
      wordEqList conf store domain memory limit clock (BitVec.ofNat width ([] : List Value).length) w1 w2 =
        some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width := by
  rintro ⟨_, _, _, _, _, sized, _, _, _⟩
  simp only [vbEqSizeList, Option.some.injEq, Prod.mk.injEq] at sized
  obtain ⟨rfl, rfl⟩ := sized
  refine ⟨1, limit, clock, ?_, by simp, by simp⟩
  simp [wordEqList_unclamped]

/-- Cons case of the source word-equality simulation, assuming the two
    recursive instances of the simultaneous induction. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm0"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm0_listCons {width : Nat} [NeZero width] {β γ : Type}
    (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (x y : Value) (xs ys : List Value) (vars : List (Value × WordLocW width))
    (headIH : ∀ (refs : Spt (BvlSem.Ref Value)) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat),
      memoryRel conf be next refs space store memory domain ((x, .word w1) :: (y, .word w2) :: vars) ∧
      vbEqSize refs x y = some (n, b) ∧ clock = min (valueDepth x) (valueDepth y) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
      ∃ result remaining remainingClock, wordEq conf store domain memory limit clock w1 w2 =
        some (result, remaining, remainingClock) ∧
        (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width)
    (tailIH : ∀ (refs : Spt (BvlSem.Ref Value)) (limit clock : Nat) (b : Bool)
      (w1 w2 : BitVec width) (_t1 : β) (_t2 : γ) (n : Nat),
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
    (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (_t1 : β) (_t2 : γ) (n : Nat) :
    memoryRel conf be next refs space store memory domain
        (eqExplode w1 memory domain (x :: xs) ++ eqExplode w2 memory domain (y :: ys) ++ vars) ∧
      (y :: ys).length = (x :: xs).length ∧ (x :: xs).length < 2 ^ width ∧
      eqAssum w1 memory domain (x :: xs) ∧ eqAssum w2 memory domain (y :: ys) ∧
      vbEqSizeList refs (x :: xs) (y :: ys) = some (n, b) ∧
      clock = min (valuesDepth (x :: xs)) (valuesDepth (y :: ys)) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock,
      wordEqList conf store domain memory limit clock (BitVec.ofNat width (x :: xs).length) w1 w2 =
        some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width := by
  rintro ⟨rel, lengths, lenBound, ass1, ass2, sized, clockEq, bound, good⟩
  have headRel : memoryRel conf be next refs space store memory domain
      ((x, memory w1) :: (y, memory w2) :: vars) := by
    apply memoryRel_rearrange conf be next refs space store memory domain _ _ ?_ rel
    intro pair member
    simp only [eqExplode, List.cons_append, List.mem_cons, List.mem_append] at member ⊢
    tauto
  have tailRel : memoryRel conf be next refs space store memory domain
      (eqExplode (w1 + StackRemove.bytesInWord width) memory domain xs ++
       eqExplode (w2 + StackRemove.bytesInWord width) memory domain ys ++ vars) := by
    apply memoryRel_rearrange conf be next refs space store memory domain _ _ ?_ rel
    intro pair member
    simp only [eqExplode, List.cons_append, List.mem_cons, List.mem_append] at member ⊢
    tauto
  simp only [eqAssum] at ass1 ass2
  simp only [List.length_cons, Nat.succ.injEq] at lengths
  have small : xs.length < 2 ^ width := by simp only [List.length_cons] at lenBound; omega
  have positive : 0 < clock := by simp only [valuesDepth] at clockEq; omega
  have countNonzero : BitVec.ofNat width (x :: xs).length ≠ 0 := by
    intro zero
    have z := congrArg BitVec.toNat zero
    simp only [BitVec.toNat_ofNat] at z
    rw [Nat.mod_eq_of_lt lenBound] at z
    simp at z
  simp only [List.length_cons] at countNonzero
  cases head : vbEqSize refs x y with
  | none => simp [vbEqSizeList, head] at sized
  | some p =>
    obtain ⟨hn, hb⟩ := p
    obtain ⟨⟨wx, mx⟩, ⟨wy, my⟩⟩ := successfulPairWords conf be next refs space store memory domain
      x y (memory w1) (memory w2) vars hn hb headRel head
    rw [mx, my] at headRel
    cases hb
    · simp [vbEqSizeList, head] at sized
      obtain ⟨rfl, rfl⟩ := sized
      have dimPositive : 0 < 2 ^ width := Nat.two_pow_pos width
      have headBound : hn * 2 ^ width < limit - 1 := by
        simp only [Nat.add_mul, Nat.one_mul] at bound
        omega
      obtain ⟨result, remaining, remainingClock, eval, correct, remainingBound⟩ :=
        headIH refs (limit - 1) (min (valueDepth x) (valueDepth y)) false wx wy hn
          ⟨headRel, head, rfl, headBound, good⟩
      have clockBound : min (valueDepth x) (valueDepth y) ≤ clock - 1 := by
        simp only [valuesDepth] at clockEq
        omega
      have extended := (wordEq_addClockAux conf store domain memory (limit - 1)).1
        (min (valueDepth x) (valueDepth y)) wx wy result remaining remainingClock
        (clock - 1 - min (valueDepth x) (valueDepth y)) eval
      have eval' : wordEq conf store domain memory (limit - 1) (clock - 1) wx wy =
          some (result, remaining, remainingClock + (clock - 1 - min (valueDepth x) (valueDepth y))) := by
        simpa [Nat.add_sub_of_le clockBound] using extended
      have resultNe : result ≠ 1 := by
        intro eq
        have impossible := correct.mpr eq
        cases impossible
      refine ⟨result, remaining, clock, ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        rw [wordEqList_unclamped]
        rw [if_neg countNonzero]
        simp [ass1.1, ass2.1, show limit ≠ 0 by omega,
          show clock ≠ 0 by omega, mx, my, eval']
        intro h
        exact (resultNe h).elim
      · simpa using correct
      · simp only [Nat.add_mul, Nat.one_mul]
        omega
    · cases tail : vbEqSizeList refs xs ys with
      | none => simp [vbEqSizeList, head, tail] at sized
      | some p =>
        obtain ⟨tn, tb⟩ := p
        simp [vbEqSizeList, head, tail] at sized
        obtain ⟨rfl, rfl⟩ := sized
        have dimBig : 2 ≤ 2 ^ width := by rcases good with hw | hw <;> subst width <;> decide
        have headBound : hn * 2 ^ width < limit - 1 := by
          simp only [Nat.add_mul, Nat.one_mul] at bound
          omega
        obtain ⟨headResult, middle, headClock, headEval, headCorrect, headRemaining⟩ :=
          headIH refs (limit - 1) (min (valueDepth x) (valueDepth y)) true wx wy hn
            ⟨headRel, head, rfl, headBound, good⟩
        have headIsOne : headResult = 1 := headCorrect.mp rfl
        have clockBound : min (valueDepth x) (valueDepth y) ≤ clock - 1 := by
          simp only [valuesDepth] at clockEq
          omega
        have extended := (wordEq_addClockAux conf store domain memory (limit - 1)).1
          (min (valueDepth x) (valueDepth y)) wx wy headResult middle headClock
          (clock - 1 - min (valueDepth x) (valueDepth y)) headEval
        have headEval' : wordEq conf store domain memory (limit - 1) (clock - 1) wx wy =
            some (headResult, middle, headClock + (clock - 1 - min (valueDepth x) (valueDepth y))) := by
          simpa [Nat.add_sub_of_le clockBound] using extended
        have tailBound : tn * 2 ^ width < middle - 1 := by
          simp only [Nat.add_mul, Nat.one_mul] at bound
          omega
        obtain ⟨result, remaining, remainingClock, tailEval, tailCorrect, tailRemaining⟩ :=
          tailIH refs (middle - 1) (min (valuesDepth xs) (valuesDepth ys)) tb
            (w1 + StackRemove.bytesInWord width) (w2 + StackRemove.bytesInWord width) _t1 _t2 tn
            ⟨tailRel, lengths, small, ass1.2, ass2.2, tail, rfl, tailBound, good⟩
        have tailClockBound : min (valuesDepth xs) (valuesDepth ys) ≤ clock := by
          simp only [valuesDepth] at clockEq
          omega
        have tailExtended := (wordEq_addClockAux conf store domain memory (middle - 1)).2
          (min (valuesDepth xs) (valuesDepth ys)) (BitVec.ofNat width xs.length)
          (w1 + StackRemove.bytesInWord width) (w2 + StackRemove.bytesInWord width)
          result remaining remainingClock (clock - min (valuesDepth xs) (valuesDepth ys)) tailEval
        have tailEval' : wordEqList conf store domain memory (middle - 1) clock
            (BitVec.ofNat width xs.length) (w1 + StackRemove.bytesInWord width)
            (w2 + StackRemove.bytesInWord width) =
            some (result, remaining, remainingClock + (clock - min (valuesDepth xs) (valuesDepth ys))) := by
          simpa [Nat.add_sub_of_le tailClockBound] using tailExtended
        refine ⟨result, remaining, remainingClock + (clock - min (valuesDepth xs) (valuesDepth ys)), ?_, tailCorrect, ?_⟩
        · simp only [List.length_cons]
          rw [wordEqList_unclamped]
          rw [if_neg countNonzero]
          simp [ass1.1, ass2.1, show limit ≠ 0 by omega,
            show clock ≠ 0 by omega, mx, my, headEval', headIsOne,
            show middle ≠ 0 by omega]
          simpa only [BitVec.ofNat_add, BitVec.add_sub_cancel] using tailEval'
        · simp only [Nat.add_mul, Nat.one_mul] at bound ⊢
          omega

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
