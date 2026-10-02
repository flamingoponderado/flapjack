import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations

/-! Same-input whole-AST and label observations captured from original HOL.
The packets retain all continuation constructors; they are regression evidence,
not a cross-language equivalence proof. -/
namespace Flapjack.Test.WordToStackLoadContinuationsParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackSem
open Flapjack.Compiler.Backend.WordToStack.Native
set_option maxRecDepth 8192

-- lc_packet_1_0_0
example : wStackLoadNative ([] ++ []) (.skip : HolProg 1) = .skip ∧
    wStackLoadNative [] (wStackLoadNative [] (.skip : HolProg 1)) = .skip ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_0_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.skip : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_1_0
example : wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_1_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_2_0
example : wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 1) = (.get 7 .handler) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.get 7 .handler) : HolProg 1)) = (.get 7 .handler) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_2_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.get 7 .handler) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_3_0
example : wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_3_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_4_0
example : wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 1) = (.opCurrHeap .add 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.opCurrHeap .add 3 4) : HolProg 1)) = (.opCurrHeap .add 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_4_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.opCurrHeap .add 3 4) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_5_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_5_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_5_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_6_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_6_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_6_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_7_0
example : wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_7_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_7_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_8_0
example : wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_8_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_8_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_9_0
example : wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) = (.jumpLower 1 2 1180591620717411303424) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) = (.jumpLower 1 2 1180591620717411303424) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_9_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_10_0
example : wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 1) = (.alloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.alloc 7) : HolProg 1)) = (.alloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_10_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.alloc 7) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_11_0
example : wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 1) = (.storeConsts 1 2 (some 3)) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.storeConsts 1 2 (some 3)) : HolProg 1)) = (.storeConsts 1 2 (some 3)) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_11_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.storeConsts 1 2 (some 3)) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_12_0
example : wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 1) = (.raise 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.raise 9) : HolProg 1)) = (.raise 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_12_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.raise 9) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_13_0
example : wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 1) = (.ret 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ret 8) : HolProg 1)) = (.ret 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_13_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ret 8) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_14_0
example : wStackLoadNative ([] ++ []) ((.break 2) : HolProg 1) = (.break 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.break 2) : HolProg 1)) = (.break 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_14_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.break 2) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_15_0
example : wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 1) = (.continue 3) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.continue 3) : HolProg 1)) = (.continue 3) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_15_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.continue 3) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_16_0
example : wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_16_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_17_0
example : wStackLoadNative ([] ++ []) (.tick : HolProg 1) = .tick ∧
    wStackLoadNative [] (wStackLoadNative [] (.tick : HolProg 1)) = .tick ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_17_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.tick : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_18_0
example : wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 1) = (.locValue 1 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.locValue 1 4 5) : HolProg 1)) = (.locValue 1 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_18_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.locValue 1 4 5) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_19_0
example : wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 1) = (.install 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.install 1 2 3 4 5) : HolProg 1)) = (.install 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_19_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.install 1 2 3 4 5) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_20_0
example : wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_20_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_21_0
example : wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 1) = (.codeBufferWrite 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.codeBufferWrite 1 2) : HolProg 1)) = (.codeBufferWrite 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_21_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.codeBufferWrite 1 2) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_22_0
example : wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 1) = (.dataBufferWrite 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.dataBufferWrite 3 4) : HolProg 1)) = (.dataBufferWrite 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_22_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.dataBufferWrite 3 4) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_23_0
example : wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 1) = (.rawCall 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.rawCall 9) : HolProg 1)) = (.rawCall 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_23_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.rawCall 9) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_24_0
example : wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 1) = (.stackAlloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackAlloc 7) : HolProg 1)) = (.stackAlloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_24_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackAlloc 7) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_25_0
example : wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 1) = (.stackFree 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackFree 8) : HolProg 1)) = (.stackFree 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_25_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackFree 8) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_26_0
example : wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 1) = (.stackStore 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStore 1 2) : HolProg 1)) = (.stackStore 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_26_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStore 1 2) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_27_0
example : wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 1) = (.stackStoreAny 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStoreAny 3 4) : HolProg 1)) = (.stackStoreAny 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_27_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStoreAny 3 4) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_28_0
example : wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 1) = (.stackLoad 5 6) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoad 5 6) : HolProg 1)) = (.stackLoad 5 6) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_28_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoad 5 6) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_29_0
example : wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 1) = (.stackLoadAny 7 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoadAny 7 8) : HolProg 1)) = (.stackLoadAny 7 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_29_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoadAny 7 8) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_30_0
example : wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 1) = (.stackGetSize 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackGetSize 9) : HolProg 1)) = (.stackGetSize 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_30_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackGetSize 9) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_31_0
example : wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 1) = (.stackSetSize 10) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackSetSize 10) : HolProg 1)) = (.stackSetSize 10) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_31_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackSetSize 10) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_32_0
example : wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 1) = (.bitmapLoad 11 12) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.bitmapLoad 11 12) : HolProg 1)) = (.bitmapLoad 11 12) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_32_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.bitmapLoad 11 12) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_33_0
example : wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 1) = (.halt 13) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.halt 13) : HolProg 1)) = (.halt 13) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_33_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.halt 13) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_34_0
example : wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_34_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_34_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_35_0
example : wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_35_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_36_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_36_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_37_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_37_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_1_37_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 1) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_0_0
example : wStackLoadNative ([] ++ []) (.skip : HolProg 2) = .skip ∧
    wStackLoadNative [] (wStackLoadNative [] (.skip : HolProg 2)) = .skip ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_0_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.skip : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_1_0
example : wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_1_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_2_0
example : wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 2) = (.get 7 .handler) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.get 7 .handler) : HolProg 2)) = (.get 7 .handler) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_2_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.get 7 .handler) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_3_0
example : wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_3_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_4_0
example : wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 2) = (.opCurrHeap .add 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.opCurrHeap .add 3 4) : HolProg 2)) = (.opCurrHeap .add 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_4_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.opCurrHeap .add 3 4) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_5_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_5_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_5_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_6_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_6_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_6_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_7_0
example : wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_7_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_7_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_8_0
example : wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_8_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_8_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_9_0
example : wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) = (.jumpLower 1 2 1180591620717411303424) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) = (.jumpLower 1 2 1180591620717411303424) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_9_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_10_0
example : wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 2) = (.alloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.alloc 7) : HolProg 2)) = (.alloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_10_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.alloc 7) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_11_0
example : wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 2) = (.storeConsts 1 2 (some 3)) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.storeConsts 1 2 (some 3)) : HolProg 2)) = (.storeConsts 1 2 (some 3)) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_11_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.storeConsts 1 2 (some 3)) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_12_0
example : wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 2) = (.raise 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.raise 9) : HolProg 2)) = (.raise 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_12_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.raise 9) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_13_0
example : wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 2) = (.ret 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ret 8) : HolProg 2)) = (.ret 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_13_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ret 8) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_14_0
example : wStackLoadNative ([] ++ []) ((.break 2) : HolProg 2) = (.break 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.break 2) : HolProg 2)) = (.break 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_14_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.break 2) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_15_0
example : wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 2) = (.continue 3) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.continue 3) : HolProg 2)) = (.continue 3) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_15_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.continue 3) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_16_0
example : wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_16_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_17_0
example : wStackLoadNative ([] ++ []) (.tick : HolProg 2) = .tick ∧
    wStackLoadNative [] (wStackLoadNative [] (.tick : HolProg 2)) = .tick ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_17_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.tick : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_18_0
example : wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 2) = (.locValue 1 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.locValue 1 4 5) : HolProg 2)) = (.locValue 1 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_18_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.locValue 1 4 5) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_19_0
example : wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 2) = (.install 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.install 1 2 3 4 5) : HolProg 2)) = (.install 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_19_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.install 1 2 3 4 5) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_20_0
example : wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_20_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_21_0
example : wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 2) = (.codeBufferWrite 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.codeBufferWrite 1 2) : HolProg 2)) = (.codeBufferWrite 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_21_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.codeBufferWrite 1 2) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_22_0
example : wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 2) = (.dataBufferWrite 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.dataBufferWrite 3 4) : HolProg 2)) = (.dataBufferWrite 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_22_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.dataBufferWrite 3 4) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_23_0
example : wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 2) = (.rawCall 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.rawCall 9) : HolProg 2)) = (.rawCall 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_23_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.rawCall 9) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_24_0
example : wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 2) = (.stackAlloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackAlloc 7) : HolProg 2)) = (.stackAlloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_24_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackAlloc 7) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_25_0
example : wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 2) = (.stackFree 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackFree 8) : HolProg 2)) = (.stackFree 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_25_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackFree 8) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_26_0
example : wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 2) = (.stackStore 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStore 1 2) : HolProg 2)) = (.stackStore 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_26_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStore 1 2) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_27_0
example : wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 2) = (.stackStoreAny 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStoreAny 3 4) : HolProg 2)) = (.stackStoreAny 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_27_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStoreAny 3 4) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_28_0
example : wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 2) = (.stackLoad 5 6) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoad 5 6) : HolProg 2)) = (.stackLoad 5 6) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_28_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoad 5 6) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_29_0
example : wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 2) = (.stackLoadAny 7 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoadAny 7 8) : HolProg 2)) = (.stackLoadAny 7 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_29_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoadAny 7 8) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_30_0
example : wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 2) = (.stackGetSize 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackGetSize 9) : HolProg 2)) = (.stackGetSize 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_30_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackGetSize 9) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_31_0
example : wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 2) = (.stackSetSize 10) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackSetSize 10) : HolProg 2)) = (.stackSetSize 10) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_31_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackSetSize 10) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_32_0
example : wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 2) = (.bitmapLoad 11 12) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.bitmapLoad 11 12) : HolProg 2)) = (.bitmapLoad 11 12) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_32_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.bitmapLoad 11 12) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_33_0
example : wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 2) = (.halt 13) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.halt 13) : HolProg 2)) = (.halt 13) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_33_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.halt 13) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_34_0
example : wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_34_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_34_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_35_0
example : wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_35_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_36_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_36_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_37_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_37_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_2_37_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 2) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_0_0
example : wStackLoadNative ([] ++ []) (.skip : HolProg 8) = .skip ∧
    wStackLoadNative [] (wStackLoadNative [] (.skip : HolProg 8)) = .skip ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_0_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.skip : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_1_0
example : wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_1_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_2_0
example : wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 8) = (.get 7 .handler) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.get 7 .handler) : HolProg 8)) = (.get 7 .handler) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_2_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.get 7 .handler) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_3_0
example : wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_3_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_4_0
example : wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 8) = (.opCurrHeap .add 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.opCurrHeap .add 3 4) : HolProg 8)) = (.opCurrHeap .add 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_4_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.opCurrHeap .add 3 4) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_5_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_5_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_5_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_6_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_6_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_6_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_7_0
example : wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_7_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_7_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_8_0
example : wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_8_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_8_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_9_0
example : wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) = (.jumpLower 1 2 1180591620717411303424) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) = (.jumpLower 1 2 1180591620717411303424) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_9_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_10_0
example : wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 8) = (.alloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.alloc 7) : HolProg 8)) = (.alloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_10_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.alloc 7) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_11_0
example : wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 8) = (.storeConsts 1 2 (some 3)) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.storeConsts 1 2 (some 3)) : HolProg 8)) = (.storeConsts 1 2 (some 3)) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_11_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.storeConsts 1 2 (some 3)) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_12_0
example : wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 8) = (.raise 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.raise 9) : HolProg 8)) = (.raise 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_12_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.raise 9) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_13_0
example : wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 8) = (.ret 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ret 8) : HolProg 8)) = (.ret 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_13_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ret 8) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_14_0
example : wStackLoadNative ([] ++ []) ((.break 2) : HolProg 8) = (.break 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.break 2) : HolProg 8)) = (.break 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_14_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.break 2) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_15_0
example : wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 8) = (.continue 3) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.continue 3) : HolProg 8)) = (.continue 3) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_15_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.continue 3) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_16_0
example : wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_16_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_17_0
example : wStackLoadNative ([] ++ []) (.tick : HolProg 8) = .tick ∧
    wStackLoadNative [] (wStackLoadNative [] (.tick : HolProg 8)) = .tick ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_17_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.tick : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_18_0
example : wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 8) = (.locValue 1 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.locValue 1 4 5) : HolProg 8)) = (.locValue 1 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_18_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.locValue 1 4 5) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_19_0
example : wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 8) = (.install 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.install 1 2 3 4 5) : HolProg 8)) = (.install 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_19_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.install 1 2 3 4 5) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_20_0
example : wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_20_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_21_0
example : wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 8) = (.codeBufferWrite 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.codeBufferWrite 1 2) : HolProg 8)) = (.codeBufferWrite 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_21_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.codeBufferWrite 1 2) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_22_0
example : wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 8) = (.dataBufferWrite 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.dataBufferWrite 3 4) : HolProg 8)) = (.dataBufferWrite 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_22_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.dataBufferWrite 3 4) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_23_0
example : wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 8) = (.rawCall 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.rawCall 9) : HolProg 8)) = (.rawCall 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_23_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.rawCall 9) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_24_0
example : wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 8) = (.stackAlloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackAlloc 7) : HolProg 8)) = (.stackAlloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_24_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackAlloc 7) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_25_0
example : wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 8) = (.stackFree 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackFree 8) : HolProg 8)) = (.stackFree 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_25_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackFree 8) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_26_0
example : wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 8) = (.stackStore 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStore 1 2) : HolProg 8)) = (.stackStore 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_26_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStore 1 2) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_27_0
example : wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 8) = (.stackStoreAny 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStoreAny 3 4) : HolProg 8)) = (.stackStoreAny 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_27_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStoreAny 3 4) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_28_0
example : wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 8) = (.stackLoad 5 6) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoad 5 6) : HolProg 8)) = (.stackLoad 5 6) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_28_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoad 5 6) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_29_0
example : wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 8) = (.stackLoadAny 7 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoadAny 7 8) : HolProg 8)) = (.stackLoadAny 7 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_29_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoadAny 7 8) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_30_0
example : wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 8) = (.stackGetSize 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackGetSize 9) : HolProg 8)) = (.stackGetSize 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_30_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackGetSize 9) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_31_0
example : wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 8) = (.stackSetSize 10) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackSetSize 10) : HolProg 8)) = (.stackSetSize 10) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_31_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackSetSize 10) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_32_0
example : wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 8) = (.bitmapLoad 11 12) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.bitmapLoad 11 12) : HolProg 8)) = (.bitmapLoad 11 12) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_32_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.bitmapLoad 11 12) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_33_0
example : wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 8) = (.halt 13) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.halt 13) : HolProg 8)) = (.halt 13) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_33_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.halt 13) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_34_0
example : wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_34_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_34_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_35_0
example : wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_35_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_36_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_36_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_37_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_37_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_8_37_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 8) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_0_0
example : wStackLoadNative ([] ++ []) (.skip : HolProg 64) = .skip ∧
    wStackLoadNative [] (wStackLoadNative [] (.skip : HolProg 64)) = .skip ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_0_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.skip : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_1_0
example : wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_1_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_2_0
example : wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 64) = (.get 7 .handler) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.get 7 .handler) : HolProg 64)) = (.get 7 .handler) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_2_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.get 7 .handler) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_3_0
example : wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_3_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_4_0
example : wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 64) = (.opCurrHeap .add 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.opCurrHeap .add 3 4) : HolProg 64)) = (.opCurrHeap .add 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_4_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.opCurrHeap .add 3 4) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_5_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_5_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_5_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_6_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_6_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_6_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_7_0
example : wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_7_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_7_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_8_0
example : wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_8_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_8_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_9_0
example : wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) = (.jumpLower 1 2 1180591620717411303424) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) = (.jumpLower 1 2 1180591620717411303424) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_9_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_10_0
example : wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 64) = (.alloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.alloc 7) : HolProg 64)) = (.alloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_10_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.alloc 7) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_11_0
example : wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 64) = (.storeConsts 1 2 (some 3)) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.storeConsts 1 2 (some 3)) : HolProg 64)) = (.storeConsts 1 2 (some 3)) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_11_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.storeConsts 1 2 (some 3)) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_12_0
example : wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 64) = (.raise 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.raise 9) : HolProg 64)) = (.raise 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_12_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.raise 9) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_13_0
example : wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 64) = (.ret 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ret 8) : HolProg 64)) = (.ret 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_13_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ret 8) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_14_0
example : wStackLoadNative ([] ++ []) ((.break 2) : HolProg 64) = (.break 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.break 2) : HolProg 64)) = (.break 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_14_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.break 2) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_15_0
example : wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 64) = (.continue 3) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.continue 3) : HolProg 64)) = (.continue 3) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_15_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.continue 3) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_16_0
example : wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_16_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_17_0
example : wStackLoadNative ([] ++ []) (.tick : HolProg 64) = .tick ∧
    wStackLoadNative [] (wStackLoadNative [] (.tick : HolProg 64)) = .tick ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_17_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.tick : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_18_0
example : wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 64) = (.locValue 1 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.locValue 1 4 5) : HolProg 64)) = (.locValue 1 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_18_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.locValue 1 4 5) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_19_0
example : wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 64) = (.install 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.install 1 2 3 4 5) : HolProg 64)) = (.install 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_19_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.install 1 2 3 4 5) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_20_0
example : wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_20_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_21_0
example : wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 64) = (.codeBufferWrite 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.codeBufferWrite 1 2) : HolProg 64)) = (.codeBufferWrite 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_21_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.codeBufferWrite 1 2) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_22_0
example : wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 64) = (.dataBufferWrite 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.dataBufferWrite 3 4) : HolProg 64)) = (.dataBufferWrite 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_22_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.dataBufferWrite 3 4) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_23_0
example : wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 64) = (.rawCall 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.rawCall 9) : HolProg 64)) = (.rawCall 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_23_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.rawCall 9) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_24_0
example : wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 64) = (.stackAlloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackAlloc 7) : HolProg 64)) = (.stackAlloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_24_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackAlloc 7) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_25_0
example : wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 64) = (.stackFree 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackFree 8) : HolProg 64)) = (.stackFree 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_25_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackFree 8) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_26_0
example : wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 64) = (.stackStore 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStore 1 2) : HolProg 64)) = (.stackStore 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_26_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStore 1 2) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_27_0
example : wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 64) = (.stackStoreAny 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStoreAny 3 4) : HolProg 64)) = (.stackStoreAny 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_27_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStoreAny 3 4) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_28_0
example : wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 64) = (.stackLoad 5 6) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoad 5 6) : HolProg 64)) = (.stackLoad 5 6) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_28_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoad 5 6) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_29_0
example : wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 64) = (.stackLoadAny 7 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoadAny 7 8) : HolProg 64)) = (.stackLoadAny 7 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_29_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoadAny 7 8) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_30_0
example : wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 64) = (.stackGetSize 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackGetSize 9) : HolProg 64)) = (.stackGetSize 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_30_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackGetSize 9) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_31_0
example : wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 64) = (.stackSetSize 10) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackSetSize 10) : HolProg 64)) = (.stackSetSize 10) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_31_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackSetSize 10) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_32_0
example : wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 64) = (.bitmapLoad 11 12) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.bitmapLoad 11 12) : HolProg 64)) = (.bitmapLoad 11 12) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_32_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.bitmapLoad 11 12) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_33_0
example : wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 64) = (.halt 13) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.halt 13) : HolProg 64)) = (.halt 13) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_33_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.halt 13) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_34_0
example : wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_34_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_34_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_35_0
example : wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_35_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_36_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_36_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_37_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_37_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_64_37_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 64) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_0_0
example : wStackLoadNative ([] ++ []) (.skip : HolProg 80) = .skip ∧
    wStackLoadNative [] (wStackLoadNative [] (.skip : HolProg 80)) = .skip ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.skip : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_0_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.skip : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .skip))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.skip : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact (.skip : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_1_0
example : wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) = (.inst (.const 9 (BitVec.ofNat _ 258))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_1_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.inst (.const 9 (BitVec.ofNat _ 258)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.inst (.const 9 (BitVec.ofNat _ 258))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_2_0
example : wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 80) = (.get 7 .handler) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.get 7 .handler) : HolProg 80)) = (.get 7 .handler) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.get 7 .handler) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_2_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.get 7 .handler) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.get 7 .handler)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.get 7 .handler) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.get 7 .handler) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_3_0
example : wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) = (.set (.temp (BitVec.ofNat 5 31)) 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_3_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.set (.temp (BitVec.ofNat 5 31)) 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.set (.temp (BitVec.ofNat 5 31)) 8) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_4_0
example : wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 80) = (.opCurrHeap .add 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.opCurrHeap .add 3 4) : HolProg 80)) = (.opCurrHeap .add 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.opCurrHeap .add 3 4) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_4_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.opCurrHeap .add 3 4) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.opCurrHeap .add 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.opCurrHeap .add 3 4) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.opCurrHeap .add 3 4) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_5_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_5_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_5_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_6_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) = (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_6_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_6_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_7_0
example : wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) = (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_7_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_7_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ite .equal 0 (.imm (BitVec.ofNat _ 259)) (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_8_0
example : wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) = (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_8_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_8_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.loop (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_9_0
example : wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) = (.jumpLower 1 2 1180591620717411303424) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) = (.jumpLower 1 2 1180591620717411303424) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_9_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.jumpLower 1 2 1180591620717411303424)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.jumpLower 1 2 1180591620717411303424) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.jumpLower 1 2 1180591620717411303424) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_10_0
example : wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 80) = (.alloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.alloc 7) : HolProg 80)) = (.alloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.alloc 7) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_10_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.alloc 7) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.alloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.alloc 7) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.alloc 7) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_11_0
example : wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 80) = (.storeConsts 1 2 (some 3)) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.storeConsts 1 2 (some 3)) : HolProg 80)) = (.storeConsts 1 2 (some 3)) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.storeConsts 1 2 (some 3)) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_11_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.storeConsts 1 2 (some 3)) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.storeConsts 1 2 (some 3))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.storeConsts 1 2 (some 3)) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.storeConsts 1 2 (some 3)) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_12_0
example : wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 80) = (.raise 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.raise 9) : HolProg 80)) = (.raise 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.raise 9) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_12_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.raise 9) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.raise 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.raise 9) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.raise 9) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_13_0
example : wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 80) = (.ret 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ret 8) : HolProg 80)) = (.ret 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ret 8) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_13_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ret 8) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ret 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ret 8) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ret 8) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_14_0
example : wStackLoadNative ([] ++ []) ((.break 2) : HolProg 80) = (.break 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.break 2) : HolProg 80)) = (.break 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.break 2) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_14_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.break 2) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.break 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.break 2) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.break 2) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_15_0
example : wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 80) = (.continue 3) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.continue 3) : HolProg 80)) = (.continue 3) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.continue 3) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_15_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.continue 3) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.continue 3)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.continue 3) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.continue 3) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_16_0
example : wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) = (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_16_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.ffi (.implode [BitVec.ofNat 8 0,BitVec.ofNat 8 65,BitVec.ofNat 8 255]) 1 2 3 4 5) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_17_0
example : wStackLoadNative ([] ++ []) (.tick : HolProg 80) = .tick ∧
    wStackLoadNative [] (wStackLoadNative [] (.tick : HolProg 80)) = .tick ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) (.tick : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_17_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] (.tick : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) .tick))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) (.tick : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact (.tick : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_18_0
example : wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 80) = (.locValue 1 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.locValue 1 4 5) : HolProg 80)) = (.locValue 1 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.locValue 1 4 5) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_18_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.locValue 1 4 5) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.locValue 1 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.locValue 1 4 5) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.locValue 1 4 5) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_19_0
example : wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 80) = (.install 1 2 3 4 5) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.install 1 2 3 4 5) : HolProg 80)) = (.install 1 2 3 4 5) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.install 1 2 3 4 5) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_19_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.install 1 2 3 4 5) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.install 1 2 3 4 5)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.install 1 2 3 4 5) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.install 1 2 3 4 5) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_20_0
example : wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) = (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_20_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.shMemOp .load8 9 (.addr 7 (BitVec.ofNat _ 257))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_21_0
example : wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 80) = (.codeBufferWrite 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.codeBufferWrite 1 2) : HolProg 80)) = (.codeBufferWrite 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.codeBufferWrite 1 2) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_21_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.codeBufferWrite 1 2) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.codeBufferWrite 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.codeBufferWrite 1 2) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.codeBufferWrite 1 2) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_22_0
example : wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 80) = (.dataBufferWrite 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.dataBufferWrite 3 4) : HolProg 80)) = (.dataBufferWrite 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.dataBufferWrite 3 4) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_22_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.dataBufferWrite 3 4) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.dataBufferWrite 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.dataBufferWrite 3 4) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.dataBufferWrite 3 4) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_23_0
example : wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 80) = (.rawCall 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.rawCall 9) : HolProg 80)) = (.rawCall 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.rawCall 9) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_23_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.rawCall 9) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.rawCall 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.rawCall 9) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.rawCall 9) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_24_0
example : wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 80) = (.stackAlloc 7) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackAlloc 7) : HolProg 80)) = (.stackAlloc 7) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackAlloc 7) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_24_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackAlloc 7) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackAlloc 7)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackAlloc 7) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackAlloc 7) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_25_0
example : wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 80) = (.stackFree 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackFree 8) : HolProg 80)) = (.stackFree 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackFree 8) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_25_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackFree 8) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackFree 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackFree 8) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackFree 8) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_26_0
example : wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 80) = (.stackStore 1 2) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStore 1 2) : HolProg 80)) = (.stackStore 1 2) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStore 1 2) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_26_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStore 1 2) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStore 1 2)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStore 1 2) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStore 1 2) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_27_0
example : wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 80) = (.stackStoreAny 3 4) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackStoreAny 3 4) : HolProg 80)) = (.stackStoreAny 3 4) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackStoreAny 3 4) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_27_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackStoreAny 3 4) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackStoreAny 3 4)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackStoreAny 3 4) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackStoreAny 3 4) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_28_0
example : wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 80) = (.stackLoad 5 6) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoad 5 6) : HolProg 80)) = (.stackLoad 5 6) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoad 5 6) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_28_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoad 5 6) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoad 5 6)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoad 5 6) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoad 5 6) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_29_0
example : wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 80) = (.stackLoadAny 7 8) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackLoadAny 7 8) : HolProg 80)) = (.stackLoadAny 7 8) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackLoadAny 7 8) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_29_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackLoadAny 7 8) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackLoadAny 7 8)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackLoadAny 7 8) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackLoadAny 7 8) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_30_0
example : wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 80) = (.stackGetSize 9) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackGetSize 9) : HolProg 80)) = (.stackGetSize 9) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackGetSize 9) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_30_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackGetSize 9) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackGetSize 9)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackGetSize 9) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackGetSize 9) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_31_0
example : wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 80) = (.stackSetSize 10) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.stackSetSize 10) : HolProg 80)) = (.stackSetSize 10) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.stackSetSize 10) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_31_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.stackSetSize 10) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.stackSetSize 10)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.stackSetSize 10) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.stackSetSize 10) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_32_0
example : wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 80) = (.bitmapLoad 11 12) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.bitmapLoad 11 12) : HolProg 80)) = (.bitmapLoad 11 12) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.bitmapLoad 11 12) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_32_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.bitmapLoad 11 12) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.bitmapLoad 11 12)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.bitmapLoad 11 12) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.bitmapLoad 11 12) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_33_0
example : wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 80) = (.halt 13) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.halt 13) : HolProg 80)) = (.halt 13) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.halt 13) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_33_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.halt 13) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.halt 13)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.halt 13) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.halt 13) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_34_0
example : wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) = (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_34_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_34_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (4,5) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (4,5) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call none (.inl 0) (some ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))),1180591620717411303424,15))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_35_0
example : wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) = (.call (some (.skip,13,4,5)) (.inl 0) none) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_35_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some (.skip,13,4,5)) (.inl 0) none)))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some (.skip,13,4,5)) (.inl 0) none) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_36_0
example : wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) = (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_36_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5)))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) (11,12) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) (11,12) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) (1180591620717411303424,15) ↔ False) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,4,5)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),4,5))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_37_0
example : wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    wStackLoadNative [] (wStackLoadNative [] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) = (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([] ++ []) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_37_1
example : wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    wStackLoadNative [(9,0),(0,99),(9,0)] (wStackLoadNative [(1180591620717411303424,2),(2,1180591620717411303424)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) = (.seq (.stackLoad 9 0) (.seq (.stackLoad 0 99) (.seq (.stackLoad 9 0) (.seq (.stackLoad 1180591620717411303424 2) (.seq (.stackLoad 2 1180591620717411303424) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15)))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(9,0),(0,99),(9,0)] ++ [(1180591620717411303424,2),(2,1180591620717411303424)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

-- lc_packet_80_37_2
example : wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    wStackLoadNative [(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] (wStackLoadNative [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)] ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) = (.seq (.stackLoad 0 0) (.seq (.stackLoad 1 7) (.seq (.stackLoad 2 14) (.seq (.stackLoad 0 21) (.seq (.stackLoad 1 28) (.seq (.stackLoad 2 35) (.seq (.stackLoad 0 42) (.seq (.stackLoad 1 49) (.seq (.stackLoad 2 56) (.seq (.stackLoad 0 63) (.seq (.stackLoad 1 70) (.seq (.stackLoad 2 77) (.seq (.stackLoad 0 84) (.seq (.stackLoad 1 91) (.seq (.stackLoad 2 98) (.seq (.stackLoad 0 105) (.seq (.stackLoad 1 112) (.seq (.stackLoad 2 119) (.seq (.stackLoad 0 126) (.seq (.stackLoad 1 133) (.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))))))))))))))))))))))) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (4,5) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (4,5) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (11,12) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (11,12) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (1180591620717411303424,15) ↔ True) ∧
    (getLabelsExact (wStackLoadNative ([(0,0),(1,7),(2,14),(0,21),(1,28),(2,35),(0,42),(1,49),(2,56),(0,63)] ++ [(1,70),(2,77),(0,84),(1,91),(2,98),(0,105),(1,112),(2,119),(0,126),(1,133)]) ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80)) (0,0) ↔ False) ∧
    (getLabelsExact ((.seq (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))) (.seq (.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none) (.call (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),13,11,12)) (.inl 0) (some ((.call (some ((.locValue 1 4 5),13,4,5)) (.inl 0) none),1180591620717411303424,15))))) : HolProg 80) (0,0) ↔ False) := by
  simp [wStackLoadNative, getLabelsExact]

end Flapjack.Test.WordToStackLoadContinuationsParity
