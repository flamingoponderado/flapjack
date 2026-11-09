module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.Number
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.Block
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.Reference

@[expose] public section

/-! Simultaneous word-equality simulation for values and value lists. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- The value-side induction predicate used to assemble the HOL theorem. -/
private def valueGoal {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Value × WordLocW width)) (v1 v2 : Value) : Prop :=
  ∀ (refs : Spt (BvlSem.Ref Value)) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat),
    memoryRel conf be next refs space store memory domain ((v1, .word w1) :: (v2, .word w2) :: vars) ∧
      vbEqSize refs v1 v2 = some (n, b) ∧ clock = min (valueDepth v1) (valueDepth v2) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock, wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width

/-- The list-side induction predicate; the source's unused polymorphic binders
    can be instantiated with unit without affecting this predicate. -/
private def listGoal {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Value × WordLocW width)) (xs ys : List Value) : Prop :=
  ∀ (refs : Spt (BvlSem.Ref Value)) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat),
    memoryRel conf be next refs space store memory domain (eqExplode w1 memory domain xs ++ eqExplode w2 memory domain ys ++ vars) ∧
      ys.length = xs.length ∧ xs.length < 2 ^ width ∧ eqAssum w1 memory domain xs ∧ eqAssum w2 memory domain ys ∧
      vbEqSizeList refs xs ys = some (n, b) ∧ clock = min (valuesDepth xs) (valuesDepth ys) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock,
      wordEqList conf store domain memory limit clock (BitVec.ofNat width xs.length) w1 w2 = some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width

mutual
/-- Value-side simultaneous induction; the case proofs are the HOL cases. -/
private theorem valueCases {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Value × WordLocW width)) (v1 v2 : Value) : valueGoal conf be next space store memory domain vars v1 v2 := by
  intro refs limit clock b w1 w2 n assumptions
  obtain ⟨rel, sized, ck, bound, good⟩ := assumptions
  cases v1 <;> cases v2 <;> try { simp [vbEqSize] at sized }
  case number.number i1 i2 =>
    exact wordEqThm0_number conf be next refs space store memory domain i1 i2 limit clock b w1 w2 n vars
      ⟨rel, sized, ck, bound, good⟩
  case word64.word64 x y =>
    exact wordEqThm0_word64 conf be next refs space store memory domain x y limit clock b w1 w2 n vars
      ⟨rel, sized, ck, bound, good⟩
  case block.block stamp1 tag1 xs stamp2 tag2 ys =>
    exact wordEqThm0_block conf be next space store memory domain stamp1 tag1 stamp2 tag2 xs ys vars
      (listCases conf be next space store memory domain vars xs ys) refs limit clock b w1 w2 n
      ⟨rel, sized, ck, bound, good⟩
  case refPtr.refPtr flag1 index1 flag2 index2 =>
    cases flag1 with
    | false =>
      exact wordEqThm0_refPtrFalseLeft conf be next refs space store memory domain flag2 index1 index2
        limit clock b w1 w2 n vars ⟨rel, sized, ck, bound, good⟩
    | true =>
      cases flag2 with
      | false =>
        exact wordEqThm0_refPtrFalseRight conf be next refs space store memory domain index1 index2
          limit clock b w1 w2 n vars ⟨rel, sized, ck, bound, good⟩
      | true =>
        exact wordEqThm0_refPtrTrue conf be next refs space store memory domain index1 index2
          limit clock b w1 w2 n vars ⟨rel, sized, ck, bound, good⟩
termination_by sizeOf v1

/-- List-side simultaneous induction, using the value and tail instances. -/
private theorem listCases {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Value × WordLocW width)) (xs ys : List Value) : listGoal conf be next space store memory domain vars xs ys := by
  intro refs limit clock b w1 w2 n assumptions
  cases xs with
  | nil =>
    cases ys with
    | nil => exact wordEqThm0_listNil conf be next refs space store memory domain limit clock b w1 w2 () () n vars assumptions
    | cons y ys => simp at assumptions
  | cons x xs =>
    cases ys with
    | nil => simp at assumptions
    | cons y ys =>
      have head := valueCases conf be next space store memory domain vars x y
      have tail := listCases conf be next space store memory domain vars xs ys
      exact wordEqThm0_listCons conf be next refs space store memory domain x y xs ys vars head
        (fun refs limit clock b w1 w2 _ _ n h => tail refs limit clock b w1 w2 n h)
        limit clock b w1 w2 () () n assumptions
termination_by sizeOf xs
end

/-- The complete source word-equality simulation for values and lists. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm0"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm0 {width : Nat} [NeZero width] {β γ : Type} (conf : DataToWord.Config) (be : Bool)
    (next space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Value × WordLocW width)) :
    (∀ (refs : Spt (BvlSem.Ref Value)) (v1 v2 : Value) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat),
      memoryRel conf be next refs space store memory domain ((v1, .word w1) :: (v2, .word w2) :: vars) ∧
        vbEqSize refs v1 v2 = some (n, b) ∧ clock = min (valueDepth v1) (valueDepth v2) ∧
        n * 2 ^ width < limit ∧ goodDimindex width →
      ∃ result remaining remainingClock, wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) ∧
        (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width) ∧
    (∀ (refs : Spt (BvlSem.Ref Value)) (xs ys : List Value) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width)
        (_t1 : β) (_t2 : γ) (n : Nat),
      memoryRel conf be next refs space store memory domain (eqExplode w1 memory domain xs ++ eqExplode w2 memory domain ys ++ vars) ∧
        ys.length = xs.length ∧ xs.length < 2 ^ width ∧ eqAssum w1 memory domain xs ∧ eqAssum w2 memory domain ys ∧
        vbEqSizeList refs xs ys = some (n, b) ∧ clock = min (valuesDepth xs) (valuesDepth ys) ∧
        n * 2 ^ width < limit ∧ goodDimindex width →
      ∃ result remaining remainingClock,
        wordEqList conf store domain memory limit clock (BitVec.ofNat width xs.length) w1 w2 = some (result, remaining, remainingClock) ∧
        (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width) := by
  constructor
  · intro refs v1 v2 limit clock b w1 w2 n h
    exact valueCases conf be next space store memory domain vars v1 v2 refs limit clock b w1 w2 n h
  · intro refs xs ys limit clock b w1 w2 _ _ n h
    exact listCases conf be next space store memory domain vars xs ys refs limit clock b w1 w2 n h

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
