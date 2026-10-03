import Flapjack.Compiler.Backend.StackRemove.Proofs.WordStore

namespace Flapjack.Test.StackRemoveWordStore
open Flapjack Flapjack.Compiler.Backend.StackRemove

private def mixedLookup {width : Nat} [NeZero width] : WordStoreHOL → Option (WordLocW width)
  | .nextFree => some (.word 255)
  | .otherHeap => some (.loc 5 7)
  | .currHeap => some (.word 77)
  | .temp value =>
      if value = 0 then some (.word 1)
      else if value = 31 then some (.loc 9 11) else none
  | _ => none

private def mixedStore {width : Nat} [NeZero width] :
    HolFiniteMapExact WordStoreHOL (WordLocW width) where
  lookup := mixedLookup
  finiteSupport := by
    refine ⟨[.nextFree, .otherHeap, .currHeap, .temp 0, .temp 31], ?_⟩
    intro key present
    cases key <;> simp_all [mixedLookup]
    split at present
    · simp_all
    · split at present <;> simp_all

-- Explicit independently sourced 48-slot expected order: first16 fixed names,
-- then Temp0..31. CurrHeap is deliberately populated but is not a listed slot.
private def expectedSlots {width : Nat} [NeZero width] : List (WordLocW width) :=
  [.word 255, .word 0, .word 0, .loc 5 7,
   .word 0, .word 0, .word 0, .word 0,
   .word 0, .word 0, .word 0, .word 0,
   .word 0, .word 0, .word 0, .word 0, .word 1] ++
  List.replicate 30 (.word 0) ++ [.loc 9 11]

example {width : Nat} [NeZero width] :
    storeList.map (fun name =>
      ((mixedStore (width := width)).lookup
        (StackSemRegisterTransfers.storeOfSyntax name)).getD (.word 0)) =
      expectedSlots (width := width) := rfl
example {addressWidth valueWidth : Nat} [NeZero addressWidth] [NeZero valueWidth]
    (base : BitVec addressWidth) :
    wordStoreHOL base (HolFiniteMapExact.empty : HolFiniteMapExact WordStoreHOL (WordLocW valueWidth)) =
      wordListRev base (List.replicate 48 (.word (0 : BitVec valueWidth))) := rfl
example {addressWidth valueWidth : Nat} [NeZero addressWidth] [NeZero valueWidth]
    (base : BitVec addressWidth) :
    wordStoreHOL base (mixedStore (width := valueWidth)) =
      wordListRev base (expectedSlots (width := valueWidth)) := rfl
example (base : BitVec 64) : wordStoreHOL base (mixedStore (width := 8)) =
    wordListRev base (expectedSlots (width := 8)) := rfl
example (base : BitVec 1) : wordStoreHOL base (mixedStore (width := 80)) =
    wordListRev base (expectedSlots (width := 80)) := rfl
example (base : BitVec 80) : wordStoreHOL base (mixedStore (width := 1)) =
    wordListRev base (expectedSlots (width := 1)) := rfl
example : (mixedStore (width := 8)).lookup .currHeap = some (.word 77) := rfl
example : (expectedSlots (width := 8)).length = 48 := rfl
example : (expectedSlots (width := 8))[3]? = some (.loc 5 7) := rfl
example : (expectedSlots (width := 8))[47]? = some (.loc 9 11) := rfl
example : (expectedSlots (width := 1))[0]? = some (.word 1) := rfl
-- Flapjack-specific extensionality fixture for the actual consumed lookup keys;
-- no map-equality/success assumption is added to the tagged definition.
example {addressWidth valueWidth : Nat} [NeZero addressWidth] [NeZero valueWidth]
    (base : BitVec addressWidth)
    (first second : HolFiniteMapExact WordStoreHOL (WordLocW valueWidth))
    (same : ∀ name ∈ storeList,
      first.lookup (StackSemRegisterTransfers.storeOfSyntax name) =
      second.lookup (StackSemRegisterTransfers.storeOfSyntax name)) :
    wordStoreHOL base first = wordStoreHOL base second := by
  unfold wordStoreHOL
  congr 1
  apply List.map_congr_left
  intro name member
  rw [same name member]

end Flapjack.Test.StackRemoveWordStore
