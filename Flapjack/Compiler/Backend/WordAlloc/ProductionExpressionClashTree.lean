import Flapjack.Compiler.Backend.WordAlloc.ProductionBufferClashTree

namespace Flapjack.WordAlloc

/-! Actual/native producer infrastructure without independent HOL originals.
These equations preserve the entire ordered read list, including duplicates. -/

theorem expressionReads_production {α : Type} (expression : WordExp α) :
    getReadsExpHOL (wordExpToHOL expression) = wordExpReadVars expression := by
  induction expression using wordExpReadVars.induct with
  | case1 value => simp only [wordExpToHOL, getReadsExpHOL, wordExpReadVars]
  | case2 name => simp only [wordExpToHOL, getReadsExpHOL, wordExpReadVars]
  | case3 store => simp only [wordExpToHOL, getReadsExpHOL, wordExpReadVars]
  | case4 address ih => simpa only [wordExpToHOL, getReadsExpHOL, wordExpReadVars] using ih
  | case5 operator arguments ih =>
      simp only [wordExpToHOL, getReadsExpHOL, wordExpReadVars, List.map_map, List.flatMap]
      congr 1
      apply List.map_congr_left
      intro argument member
      exact ih argument member
  | case6 operator left right ihLeft ihRight =>
      simp only [wordExpToHOL, getReadsExpHOL, wordExpReadVars, ihLeft, ihRight]

theorem assignClashTree_production {width : Nat} [NeZero width]
    (name : Nat) (expression : WordExp (BitVec width))
    (context : List (List Nat × List Nat)) :
    RegAlloc.productionClashTreeToNative (wordClashTree (.assign name expression) context) =
      getClashTree (.assign name (wordExpToHOL expression))
        (context.map wordCutsetsToHOL) := by
  simp only [wordClashTree, RegAlloc.productionClashTreeToNative, getClashTree,
    expressionReads_production]

theorem storeClashTree_production {width : Nat} [NeZero width]
    (address : WordExp (BitVec width)) (value : Nat)
    (context : List (List Nat × List Nat)) :
    RegAlloc.productionClashTreeToNative (wordClashTree (.store address value) context) =
      getClashTree (.store (wordExpToHOL address) value)
        (context.map wordCutsetsToHOL) := by
  simp only [wordClashTree, RegAlloc.productionClashTreeToNative, getClashTree,
    expressionReads_production]

theorem setClashTree_production {width : Nat} [NeZero width]
    (store : WordStore (BitVec width)) (expression : WordExp (BitVec width))
    (context : List (List Nat × List Nat)) :
    RegAlloc.productionClashTreeToNative (wordClashTree (.set store expression) context) =
      getClashTree (.set (wordStoreToHOL store) (wordExpToHOL expression))
        (context.map wordCutsetsToHOL) := by
  simp only [wordClashTree, RegAlloc.productionClashTreeToNative, getClashTree,
    expressionReads_production]

theorem shareInstClashTree_production {width : Nat} [NeZero width]
    (operator : WordMemOp) (name : Nat) (address : WordExp (BitVec width))
    (context : List (List Nat × List Nat)) :
    RegAlloc.productionClashTreeToNative (wordClashTree (.shareInst operator name address) context) =
      getClashTree (.shareInst operator name (wordExpToHOL address))
        (context.map wordCutsetsToHOL) := by
  cases operator <;>
    simp [wordClashTree, RegAlloc.productionClashTreeToNative, getClashTree,
      expressionReads_production]

end Flapjack.WordAlloc
