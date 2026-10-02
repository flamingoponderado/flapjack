import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedRelations
open Flapjack.Compiler.Backend.WordToStack

-- sr_weaken_0_0
example (hs : adjacentSorted (fun x y : Nat => decide (x > y)) []) (hd : ([] : List Nat).Nodup) (hr : ∀ x y, x ∈ [] → y ∈ [] → x ≠ y → (fun x y : Nat => decide (x > y)) x y = true → (fun x y : Nat => decide (x ≥ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_0_1
example (hs : adjacentSorted (fun _x _y : Nat => true) []) (hd : ([] : List Nat).Nodup) (hr : ∀ x y, x ∈ [] → y ∈ [] → x ≠ y → (fun _x _y : Nat => true) x y = true → (fun x y : Nat => decide (x ≠ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≠ y)) [] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_0_2
example (hs : adjacentSorted (fun x y : Nat => decide (x = y)) []) (hd : ([] : List Nat).Nodup) (hr : ∀ x y, x ∈ [] → y ∈ [] → x ≠ y → (fun x y : Nat => decide (x = y)) x y = true → (fun _x _y : Nat => false) x y = true) : adjacentSorted (fun _x _y : Nat => false) [] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_0_3
example (hs : adjacentSorted (fun x y : Nat => decide (x ≥ y)) []) (hd : ([] : List Nat).Nodup) (hr : ∀ x y, x ∈ [] → y ∈ [] → x ≠ y → (fun x y : Nat => decide (x ≥ y)) x y = true → (fun x y : Nat => decide (x > y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x > y)) [] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_1_0
example (hs : adjacentSorted (fun x y : Nat => decide (x > y)) [0]) (hd : ([0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0] → y ∈ [0] → x ≠ y → (fun x y : Nat => decide (x > y)) x y = true → (fun x y : Nat => decide (x ≥ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_1_1
example (hs : adjacentSorted (fun _x _y : Nat => true) [0]) (hd : ([0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0] → y ∈ [0] → x ≠ y → (fun _x _y : Nat => true) x y = true → (fun x y : Nat => decide (x ≠ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≠ y)) [0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_1_2
example (hs : adjacentSorted (fun x y : Nat => decide (x = y)) [0]) (hd : ([0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0] → y ∈ [0] → x ≠ y → (fun x y : Nat => decide (x = y)) x y = true → (fun _x _y : Nat => false) x y = true) : adjacentSorted (fun _x _y : Nat => false) [0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_1_3
example (hs : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [0]) (hd : ([0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0] → y ∈ [0] → x ≠ y → (fun x y : Nat => decide (x ≥ y)) x y = true → (fun x y : Nat => decide (x > y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x > y)) [0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_2_0
example (hs : adjacentSorted (fun x y : Nat => decide (x > y)) [2,1,0]) (hd : ([2,1,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [2,1,0] → y ∈ [2,1,0] → x ≠ y → (fun x y : Nat => decide (x > y)) x y = true → (fun x y : Nat => decide (x ≥ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [2,1,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_2_1
example (hs : adjacentSorted (fun _x _y : Nat => true) [2,1,0]) (hd : ([2,1,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [2,1,0] → y ∈ [2,1,0] → x ≠ y → (fun _x _y : Nat => true) x y = true → (fun x y : Nat => decide (x ≠ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≠ y)) [2,1,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_2_2
example (hs : adjacentSorted (fun x y : Nat => decide (x = y)) [2,1,0]) (hd : ([2,1,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [2,1,0] → y ∈ [2,1,0] → x ≠ y → (fun x y : Nat => decide (x = y)) x y = true → (fun _x _y : Nat => false) x y = true) : adjacentSorted (fun _x _y : Nat => false) [2,1,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_2_3
example (hs : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [2,1,0]) (hd : ([2,1,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [2,1,0] → y ∈ [2,1,0] → x ≠ y → (fun x y : Nat => decide (x ≥ y)) x y = true → (fun x y : Nat => decide (x > y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x > y)) [2,1,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_3_0
example (hs : adjacentSorted (fun x y : Nat => decide (x > y)) [0,1,2]) (hd : ([0,1,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0,1,2] → y ∈ [0,1,2] → x ≠ y → (fun x y : Nat => decide (x > y)) x y = true → (fun x y : Nat => decide (x ≥ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [0,1,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_3_1
example (hs : adjacentSorted (fun _x _y : Nat => true) [0,1,2]) (hd : ([0,1,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0,1,2] → y ∈ [0,1,2] → x ≠ y → (fun _x _y : Nat => true) x y = true → (fun x y : Nat => decide (x ≠ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≠ y)) [0,1,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_3_2
example (hs : adjacentSorted (fun x y : Nat => decide (x = y)) [0,1,2]) (hd : ([0,1,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0,1,2] → y ∈ [0,1,2] → x ≠ y → (fun x y : Nat => decide (x = y)) x y = true → (fun _x _y : Nat => false) x y = true) : adjacentSorted (fun _x _y : Nat => false) [0,1,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_3_3
example (hs : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [0,1,2]) (hd : ([0,1,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0,1,2] → y ∈ [0,1,2] → x ≠ y → (fun x y : Nat => decide (x ≥ y)) x y = true → (fun x y : Nat => decide (x > y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x > y)) [0,1,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_4_0
example (hs : adjacentSorted (fun x y : Nat => decide (x > y)) [1,1]) (hd : ([1,1] : List Nat).Nodup) (hr : ∀ x y, x ∈ [1,1] → y ∈ [1,1] → x ≠ y → (fun x y : Nat => decide (x > y)) x y = true → (fun x y : Nat => decide (x ≥ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [1,1] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_4_1
example (hs : adjacentSorted (fun _x _y : Nat => true) [1,1]) (hd : ([1,1] : List Nat).Nodup) (hr : ∀ x y, x ∈ [1,1] → y ∈ [1,1] → x ≠ y → (fun _x _y : Nat => true) x y = true → (fun x y : Nat => decide (x ≠ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≠ y)) [1,1] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_4_2
example (hs : adjacentSorted (fun x y : Nat => decide (x = y)) [1,1]) (hd : ([1,1] : List Nat).Nodup) (hr : ∀ x y, x ∈ [1,1] → y ∈ [1,1] → x ≠ y → (fun x y : Nat => decide (x = y)) x y = true → (fun _x _y : Nat => false) x y = true) : adjacentSorted (fun _x _y : Nat => false) [1,1] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_4_3
example (hs : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [1,1]) (hd : ([1,1] : List Nat).Nodup) (hr : ∀ x y, x ∈ [1,1] → y ∈ [1,1] → x ≠ y → (fun x y : Nat => decide (x ≥ y)) x y = true → (fun x y : Nat => decide (x > y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x > y)) [1,1] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_5_0
example (hs : adjacentSorted (fun x y : Nat => decide (x > y)) [2,1,2]) (hd : ([2,1,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [2,1,2] → y ∈ [2,1,2] → x ≠ y → (fun x y : Nat => decide (x > y)) x y = true → (fun x y : Nat => decide (x ≥ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [2,1,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_5_1
example (hs : adjacentSorted (fun _x _y : Nat => true) [2,1,2]) (hd : ([2,1,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [2,1,2] → y ∈ [2,1,2] → x ≠ y → (fun _x _y : Nat => true) x y = true → (fun x y : Nat => decide (x ≠ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≠ y)) [2,1,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_5_2
example (hs : adjacentSorted (fun x y : Nat => decide (x = y)) [2,1,2]) (hd : ([2,1,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [2,1,2] → y ∈ [2,1,2] → x ≠ y → (fun x y : Nat => decide (x = y)) x y = true → (fun _x _y : Nat => false) x y = true) : adjacentSorted (fun _x _y : Nat => false) [2,1,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_5_3
example (hs : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [2,1,2]) (hd : ([2,1,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [2,1,2] → y ∈ [2,1,2] → x ≠ y → (fun x y : Nat => decide (x ≥ y)) x y = true → (fun x y : Nat => decide (x > y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x > y)) [2,1,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_6_0
example (hs : adjacentSorted (fun x y : Nat => decide (x > y)) [1208925819614629174706178,1208925819614629174706176,0]) (hd : ([1208925819614629174706178,1208925819614629174706176,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [1208925819614629174706178,1208925819614629174706176,0] → y ∈ [1208925819614629174706178,1208925819614629174706176,0] → x ≠ y → (fun x y : Nat => decide (x > y)) x y = true → (fun x y : Nat => decide (x ≥ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [1208925819614629174706178,1208925819614629174706176,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_6_1
example (hs : adjacentSorted (fun _x _y : Nat => true) [1208925819614629174706178,1208925819614629174706176,0]) (hd : ([1208925819614629174706178,1208925819614629174706176,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [1208925819614629174706178,1208925819614629174706176,0] → y ∈ [1208925819614629174706178,1208925819614629174706176,0] → x ≠ y → (fun _x _y : Nat => true) x y = true → (fun x y : Nat => decide (x ≠ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≠ y)) [1208925819614629174706178,1208925819614629174706176,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_6_2
example (hs : adjacentSorted (fun x y : Nat => decide (x = y)) [1208925819614629174706178,1208925819614629174706176,0]) (hd : ([1208925819614629174706178,1208925819614629174706176,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [1208925819614629174706178,1208925819614629174706176,0] → y ∈ [1208925819614629174706178,1208925819614629174706176,0] → x ≠ y → (fun x y : Nat => decide (x = y)) x y = true → (fun _x _y : Nat => false) x y = true) : adjacentSorted (fun _x _y : Nat => false) [1208925819614629174706178,1208925819614629174706176,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_6_3
example (hs : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [1208925819614629174706178,1208925819614629174706176,0]) (hd : ([1208925819614629174706178,1208925819614629174706176,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [1208925819614629174706178,1208925819614629174706176,0] → y ∈ [1208925819614629174706178,1208925819614629174706176,0] → x ≠ y → (fun x y : Nat => decide (x ≥ y)) x y = true → (fun x y : Nat => decide (x > y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x > y)) [1208925819614629174706178,1208925819614629174706176,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_7_0
example (hs : adjacentSorted (fun x y : Nat => decide (x > y)) [0,0,0]) (hd : ([0,0,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0,0,0] → y ∈ [0,0,0] → x ≠ y → (fun x y : Nat => decide (x > y)) x y = true → (fun x y : Nat => decide (x ≥ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [0,0,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_7_1
example (hs : adjacentSorted (fun _x _y : Nat => true) [0,0,0]) (hd : ([0,0,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0,0,0] → y ∈ [0,0,0] → x ≠ y → (fun _x _y : Nat => true) x y = true → (fun x y : Nat => decide (x ≠ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≠ y)) [0,0,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_7_2
example (hs : adjacentSorted (fun x y : Nat => decide (x = y)) [0,0,0]) (hd : ([0,0,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0,0,0] → y ∈ [0,0,0] → x ≠ y → (fun x y : Nat => decide (x = y)) x y = true → (fun _x _y : Nat => false) x y = true) : adjacentSorted (fun _x _y : Nat => false) [0,0,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_7_3
example (hs : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [0,0,0]) (hd : ([0,0,0] : List Nat).Nodup) (hr : ∀ x y, x ∈ [0,0,0] → y ∈ [0,0,0] → x ≠ y → (fun x y : Nat => decide (x ≥ y)) x y = true → (fun x y : Nat => decide (x > y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x > y)) [0,0,0] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_8_0
example (hs : adjacentSorted (fun x y : Nat => decide (x > y)) [7,2]) (hd : ([7,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [7,2] → y ∈ [7,2] → x ≠ y → (fun x y : Nat => decide (x > y)) x y = true → (fun x y : Nat => decide (x ≥ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [7,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_8_1
example (hs : adjacentSorted (fun _x _y : Nat => true) [7,2]) (hd : ([7,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [7,2] → y ∈ [7,2] → x ≠ y → (fun _x _y : Nat => true) x y = true → (fun x y : Nat => decide (x ≠ y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x ≠ y)) [7,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_8_2
example (hs : adjacentSorted (fun x y : Nat => decide (x = y)) [7,2]) (hd : ([7,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [7,2] → y ∈ [7,2] → x ≠ y → (fun x y : Nat => decide (x = y)) x y = true → (fun _x _y : Nat => false) x y = true) : adjacentSorted (fun _x _y : Nat => false) [7,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_weaken_8_3
example (hs : adjacentSorted (fun x y : Nat => decide (x ≥ y)) [7,2]) (hd : ([7,2] : List Nat).Nodup) (hr : ∀ x y, x ∈ [7,2] → y ∈ [7,2] → x ≠ y → (fun x y : Nat => decide (x ≥ y)) x y = true → (fun x y : Nat => decide (x > y)) x y = true) : adjacentSorted (fun x y : Nat => decide (x > y)) [7,2] := sortedWeaken2 _ _ _ hs hd hr

-- sr_even_0_0
example (ha : 0%2=0) (hb : 0%2=0) (hg : 0>0) : 0/2>0/2 := evenGt _ _ ha hb hg

-- sr_even_0_1
example (ha : 0%2=0) (hb : 1%2=0) (hg : 0>1) : 0/2>1/2 := evenGt _ _ ha hb hg

-- sr_even_0_2
example (ha : 0%2=0) (hb : 2%2=0) (hg : 0>2) : 0/2>2/2 := evenGt _ _ ha hb hg

-- sr_even_0_3
example (ha : 0%2=0) (hb : 6%2=0) (hg : 0>6) : 0/2>6/2 := evenGt _ _ ha hb hg

-- sr_even_0_4
example (ha : 0%2=0) (hb : 1208925819614629174706176%2=0) (hg : 0>1208925819614629174706176) : 0/2>1208925819614629174706176/2 := evenGt _ _ ha hb hg

-- sr_even_0_5
example (ha : 0%2=0) (hb : 1208925819614629174706178%2=0) (hg : 0>1208925819614629174706178) : 0/2>1208925819614629174706178/2 := evenGt _ _ ha hb hg

-- sr_even_1_0
example (ha : 1%2=0) (hb : 0%2=0) (hg : 1>0) : 1/2>0/2 := evenGt _ _ ha hb hg

-- sr_even_1_1
example (ha : 1%2=0) (hb : 1%2=0) (hg : 1>1) : 1/2>1/2 := evenGt _ _ ha hb hg

-- sr_even_1_2
example (ha : 1%2=0) (hb : 2%2=0) (hg : 1>2) : 1/2>2/2 := evenGt _ _ ha hb hg

-- sr_even_1_3
example (ha : 1%2=0) (hb : 6%2=0) (hg : 1>6) : 1/2>6/2 := evenGt _ _ ha hb hg

-- sr_even_1_4
example (ha : 1%2=0) (hb : 1208925819614629174706176%2=0) (hg : 1>1208925819614629174706176) : 1/2>1208925819614629174706176/2 := evenGt _ _ ha hb hg

-- sr_even_1_5
example (ha : 1%2=0) (hb : 1208925819614629174706178%2=0) (hg : 1>1208925819614629174706178) : 1/2>1208925819614629174706178/2 := evenGt _ _ ha hb hg

-- sr_even_2_0
example (ha : 2%2=0) (hb : 0%2=0) (hg : 2>0) : 2/2>0/2 := evenGt _ _ ha hb hg

-- sr_even_2_1
example (ha : 2%2=0) (hb : 1%2=0) (hg : 2>1) : 2/2>1/2 := evenGt _ _ ha hb hg

-- sr_even_2_2
example (ha : 2%2=0) (hb : 2%2=0) (hg : 2>2) : 2/2>2/2 := evenGt _ _ ha hb hg

-- sr_even_2_3
example (ha : 2%2=0) (hb : 6%2=0) (hg : 2>6) : 2/2>6/2 := evenGt _ _ ha hb hg

-- sr_even_2_4
example (ha : 2%2=0) (hb : 1208925819614629174706176%2=0) (hg : 2>1208925819614629174706176) : 2/2>1208925819614629174706176/2 := evenGt _ _ ha hb hg

-- sr_even_2_5
example (ha : 2%2=0) (hb : 1208925819614629174706178%2=0) (hg : 2>1208925819614629174706178) : 2/2>1208925819614629174706178/2 := evenGt _ _ ha hb hg

-- sr_even_3_0
example (ha : 6%2=0) (hb : 0%2=0) (hg : 6>0) : 6/2>0/2 := evenGt _ _ ha hb hg

-- sr_even_3_1
example (ha : 6%2=0) (hb : 1%2=0) (hg : 6>1) : 6/2>1/2 := evenGt _ _ ha hb hg

-- sr_even_3_2
example (ha : 6%2=0) (hb : 2%2=0) (hg : 6>2) : 6/2>2/2 := evenGt _ _ ha hb hg

-- sr_even_3_3
example (ha : 6%2=0) (hb : 6%2=0) (hg : 6>6) : 6/2>6/2 := evenGt _ _ ha hb hg

-- sr_even_3_4
example (ha : 6%2=0) (hb : 1208925819614629174706176%2=0) (hg : 6>1208925819614629174706176) : 6/2>1208925819614629174706176/2 := evenGt _ _ ha hb hg

-- sr_even_3_5
example (ha : 6%2=0) (hb : 1208925819614629174706178%2=0) (hg : 6>1208925819614629174706178) : 6/2>1208925819614629174706178/2 := evenGt _ _ ha hb hg

-- sr_even_4_0
example (ha : 1208925819614629174706176%2=0) (hb : 0%2=0) (hg : 1208925819614629174706176>0) : 1208925819614629174706176/2>0/2 := evenGt _ _ ha hb hg

-- sr_even_4_1
example (ha : 1208925819614629174706176%2=0) (hb : 1%2=0) (hg : 1208925819614629174706176>1) : 1208925819614629174706176/2>1/2 := evenGt _ _ ha hb hg

-- sr_even_4_2
example (ha : 1208925819614629174706176%2=0) (hb : 2%2=0) (hg : 1208925819614629174706176>2) : 1208925819614629174706176/2>2/2 := evenGt _ _ ha hb hg

-- sr_even_4_3
example (ha : 1208925819614629174706176%2=0) (hb : 6%2=0) (hg : 1208925819614629174706176>6) : 1208925819614629174706176/2>6/2 := evenGt _ _ ha hb hg

-- sr_even_4_4
example (ha : 1208925819614629174706176%2=0) (hb : 1208925819614629174706176%2=0) (hg : 1208925819614629174706176>1208925819614629174706176) : 1208925819614629174706176/2>1208925819614629174706176/2 := evenGt _ _ ha hb hg

-- sr_even_4_5
example (ha : 1208925819614629174706176%2=0) (hb : 1208925819614629174706178%2=0) (hg : 1208925819614629174706176>1208925819614629174706178) : 1208925819614629174706176/2>1208925819614629174706178/2 := evenGt _ _ ha hb hg

-- sr_even_5_0
example (ha : 1208925819614629174706178%2=0) (hb : 0%2=0) (hg : 1208925819614629174706178>0) : 1208925819614629174706178/2>0/2 := evenGt _ _ ha hb hg

-- sr_even_5_1
example (ha : 1208925819614629174706178%2=0) (hb : 1%2=0) (hg : 1208925819614629174706178>1) : 1208925819614629174706178/2>1/2 := evenGt _ _ ha hb hg

-- sr_even_5_2
example (ha : 1208925819614629174706178%2=0) (hb : 2%2=0) (hg : 1208925819614629174706178>2) : 1208925819614629174706178/2>2/2 := evenGt _ _ ha hb hg

-- sr_even_5_3
example (ha : 1208925819614629174706178%2=0) (hb : 6%2=0) (hg : 1208925819614629174706178>6) : 1208925819614629174706178/2>6/2 := evenGt _ _ ha hb hg

-- sr_even_5_4
example (ha : 1208925819614629174706178%2=0) (hb : 1208925819614629174706176%2=0) (hg : 1208925819614629174706178>1208925819614629174706176) : 1208925819614629174706178/2>1208925819614629174706176/2 := evenGt _ _ ha hb hg

-- sr_even_5_5
example (ha : 1208925819614629174706178%2=0) (hb : 1208925819614629174706178%2=0) (hg : 1208925819614629174706178>1208925819614629174706178) : 1208925819614629174706178/2>1208925819614629174706178/2 := evenGt _ _ ha hb hg

-- sr_transit_0_0_0
example (hab : 0>0) (hbc : 0>0) : 0>0 := transitiveGt _ _ _ hab hbc

-- sr_transit_0_0_1
example (hab : 0>0) (hbc : 0>1) : 0>1 := transitiveGt _ _ _ hab hbc

-- sr_transit_0_0_2
example (hab : 0>0) (hbc : 0>1208925819614629174706176) : 0>1208925819614629174706176 := transitiveGt _ _ _ hab hbc

-- sr_transit_0_1_0
example (hab : 0>2) (hbc : 2>0) : 0>0 := transitiveGt _ _ _ hab hbc

-- sr_transit_0_1_1
example (hab : 0>2) (hbc : 2>1) : 0>1 := transitiveGt _ _ _ hab hbc

-- sr_transit_0_1_2
example (hab : 0>2) (hbc : 2>1208925819614629174706176) : 0>1208925819614629174706176 := transitiveGt _ _ _ hab hbc

-- sr_transit_0_2_0
example (hab : 0>1208925819614629174706176) (hbc : 1208925819614629174706176>0) : 0>0 := transitiveGt _ _ _ hab hbc

-- sr_transit_0_2_1
example (hab : 0>1208925819614629174706176) (hbc : 1208925819614629174706176>1) : 0>1 := transitiveGt _ _ _ hab hbc

-- sr_transit_0_2_2
example (hab : 0>1208925819614629174706176) (hbc : 1208925819614629174706176>1208925819614629174706176) : 0>1208925819614629174706176 := transitiveGt _ _ _ hab hbc

-- sr_transit_1_0_0
example (hab : 6>0) (hbc : 0>0) : 6>0 := transitiveGt _ _ _ hab hbc

-- sr_transit_1_0_1
example (hab : 6>0) (hbc : 0>1) : 6>1 := transitiveGt _ _ _ hab hbc

-- sr_transit_1_0_2
example (hab : 6>0) (hbc : 0>1208925819614629174706176) : 6>1208925819614629174706176 := transitiveGt _ _ _ hab hbc

-- sr_transit_1_1_0
example (hab : 6>2) (hbc : 2>0) : 6>0 := transitiveGt _ _ _ hab hbc

-- sr_transit_1_1_1
example (hab : 6>2) (hbc : 2>1) : 6>1 := transitiveGt _ _ _ hab hbc

-- sr_transit_1_1_2
example (hab : 6>2) (hbc : 2>1208925819614629174706176) : 6>1208925819614629174706176 := transitiveGt _ _ _ hab hbc

-- sr_transit_1_2_0
example (hab : 6>1208925819614629174706176) (hbc : 1208925819614629174706176>0) : 6>0 := transitiveGt _ _ _ hab hbc

-- sr_transit_1_2_1
example (hab : 6>1208925819614629174706176) (hbc : 1208925819614629174706176>1) : 6>1 := transitiveGt _ _ _ hab hbc

-- sr_transit_1_2_2
example (hab : 6>1208925819614629174706176) (hbc : 1208925819614629174706176>1208925819614629174706176) : 6>1208925819614629174706176 := transitiveGt _ _ _ hab hbc

-- sr_transit_2_0_0
example (hab : 1208925819614629174706176>0) (hbc : 0>0) : 1208925819614629174706176>0 := transitiveGt _ _ _ hab hbc

-- sr_transit_2_0_1
example (hab : 1208925819614629174706176>0) (hbc : 0>1) : 1208925819614629174706176>1 := transitiveGt _ _ _ hab hbc

-- sr_transit_2_0_2
example (hab : 1208925819614629174706176>0) (hbc : 0>1208925819614629174706176) : 1208925819614629174706176>1208925819614629174706176 := transitiveGt _ _ _ hab hbc

-- sr_transit_2_1_0
example (hab : 1208925819614629174706176>2) (hbc : 2>0) : 1208925819614629174706176>0 := transitiveGt _ _ _ hab hbc

-- sr_transit_2_1_1
example (hab : 1208925819614629174706176>2) (hbc : 2>1) : 1208925819614629174706176>1 := transitiveGt _ _ _ hab hbc

-- sr_transit_2_1_2
example (hab : 1208925819614629174706176>2) (hbc : 2>1208925819614629174706176) : 1208925819614629174706176>1208925819614629174706176 := transitiveGt _ _ _ hab hbc

-- sr_transit_2_2_0
example (hab : 1208925819614629174706176>1208925819614629174706176) (hbc : 1208925819614629174706176>0) : 1208925819614629174706176>0 := transitiveGt _ _ _ hab hbc

-- sr_transit_2_2_1
example (hab : 1208925819614629174706176>1208925819614629174706176) (hbc : 1208925819614629174706176>1) : 1208925819614629174706176>1 := transitiveGt _ _ _ hab hbc

-- sr_transit_2_2_2
example (hab : 1208925819614629174706176>1208925819614629174706176) (hbc : 1208925819614629174706176>1208925819614629174706176) : 1208925819614629174706176>1208925819614629174706176 := transitiveGt _ _ _ hab hbc

example {α : Type} (r q : α → α → Bool) (xs : List α) (hs : adjacentSorted r xs) (hd : xs.Nodup) (h : ∀ x y, x ∈ xs → y ∈ xs → x ≠ y → r x y = true → q x y = true) := sortedWeaken2 r q xs hs hd h
