import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedKeys
open Flapjack.Compiler.Backend.WordToStack

-- sk_sorted_0
example : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat)) ↔ True := by simp only [descendingKeys]; decide

-- sk_head_0_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ ([] : List (Nat × Nat)) : List (Nat × Nat))) : descendingKeys (α := Nat) ([] : List (Nat × Nat)) ∧ (0,0) ∉ ([] : List (Nat × Nat)) ∧ ∀ (y : Nat × Nat), y ∈ ([] : List (Nat × Nat)) → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_0_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ ([] : List (Nat × Nat)) : List (Nat × Nat))) : descendingKeys (α := Nat) ([] : List (Nat × Nat)) ∧ (4,9) ∉ ([] : List (Nat × Nat)) ∧ ∀ (y : Nat × Nat), y ∈ ([] : List (Nat × Nat)) → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_0_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ ([] : List (Nat × Nat)) : List (Nat × Nat))) : descendingKeys (α := Nat) ([] : List (Nat × Nat)) ∧ (3,7) ∉ ([] : List (Nat × Nat)) ∧ ∀ (y : Nat × Nat), y ∈ ([] : List (Nat × Nat)) → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_0_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ ([] : List (Nat × Nat)) : List (Nat × Nat))) : descendingKeys (α := Nat) ([] : List (Nat × Nat)) ∧ (1208925819614629174706177,0) ∉ ([] : List (Nat × Nat)) ∧ ∀ (y : Nat × Nat), y ∈ ([] : List (Nat × Nat)) → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_0_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_0_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_0_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_0_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_0_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_0_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_0_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_0_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_0_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_0_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) ([] : List (Nat × Nat))) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ ([] : List (Nat × Nat))) : ([] : List (Nat × Nat)) = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_sorted_1
example : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat)) ↔ True := by simp only [descendingKeys]; decide

-- sk_head_1_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ [(0,0)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(0,0)] ∧ (0,0) ∉ [(0,0)] ∧ ∀ (y : Nat × Nat), y ∈ [(0,0)] → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_1_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ [(0,0)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(0,0)] ∧ (4,9) ∉ [(0,0)] ∧ ∀ (y : Nat × Nat), y ∈ [(0,0)] → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_1_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ [(0,0)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(0,0)] ∧ (3,7) ∉ [(0,0)] ∧ ∀ (y : Nat × Nat), y ∈ [(0,0)] → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_1_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ [(0,0)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(0,0)] ∧ (1208925819614629174706177,0) ∉ [(0,0)] ∧ ∀ (y : Nat × Nat), y ∈ [(0,0)] → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_1_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ [(0,0)]) : [(0,0)] = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_1_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ [(0,0)]) : [(0,0)] = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_1_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ [(0,0)]) : [(0,0)] = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_1_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ [(0,0)]) : [(0,0)] = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_1_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ [(0,0)]) : [(0,0)] = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_1_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ [(0,0)]) : [(0,0)] = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_1_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ [(0,0)]) : [(0,0)] = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_1_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ [(0,0)]) : [(0,0)] = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_1_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ [(0,0)]) : [(0,0)] = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_1_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,0)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ [(0,0)]) : [(0,0)] = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_sorted_2
example : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat)) ↔ True := by simp only [descendingKeys]; decide

-- sk_head_2_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ [(3,7),(2,8),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)] ∧ (0,0) ∉ [(3,7),(2,8),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(2,8),(0,9)] → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_2_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ [(3,7),(2,8),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)] ∧ (4,9) ∉ [(3,7),(2,8),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(2,8),(0,9)] → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_2_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ [(3,7),(2,8),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)] ∧ (3,7) ∉ [(3,7),(2,8),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(2,8),(0,9)] → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_2_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ [(3,7),(2,8),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)] ∧ (1208925819614629174706177,0) ∉ [(3,7),(2,8),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(2,8),(0,9)] → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_2_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_2_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_2_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_2_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_2_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_2_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_2_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_2_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_2_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_2_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ [(3,7),(2,8),(0,9)]) : [(3,7),(2,8),(0,9)] = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_sorted_3
example : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat)) ↔ False := by simp only [descendingKeys]; decide

-- sk_head_3_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ [(2,8),(3,7),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)] ∧ (0,0) ∉ [(2,8),(3,7),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(2,8),(3,7),(0,9)] → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_3_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ [(2,8),(3,7),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)] ∧ (4,9) ∉ [(2,8),(3,7),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(2,8),(3,7),(0,9)] → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_3_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ [(2,8),(3,7),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)] ∧ (3,7) ∉ [(2,8),(3,7),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(2,8),(3,7),(0,9)] → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_3_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ [(2,8),(3,7),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)] ∧ (1208925819614629174706177,0) ∉ [(2,8),(3,7),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(2,8),(3,7),(0,9)] → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_3_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_3_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_3_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_3_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_3_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_3_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_3_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_3_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_3_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_3_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(2,8),(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ [(2,8),(3,7),(0,9)]) : [(2,8),(3,7),(0,9)] = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_sorted_4
example : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat)) ↔ False := by simp only [descendingKeys]; decide

-- sk_head_4_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ [(3,7),(3,7)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(3,7)] ∧ (0,0) ∉ [(3,7),(3,7)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(3,7)] → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_4_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ [(3,7),(3,7)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(3,7)] ∧ (4,9) ∉ [(3,7),(3,7)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(3,7)] → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_4_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ [(3,7),(3,7)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(3,7)] ∧ (3,7) ∉ [(3,7),(3,7)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(3,7)] → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_4_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ [(3,7),(3,7)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(3,7)] ∧ (1208925819614629174706177,0) ∉ [(3,7),(3,7)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(3,7)] → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_4_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_4_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_4_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_4_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_4_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_4_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_4_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_4_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_4_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_4_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ [(3,7),(3,7)]) : [(3,7),(3,7)] = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_sorted_5
example : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat)) ↔ False := by simp only [descendingKeys]; decide

-- sk_head_5_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ [(3,7),(3,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(3,9)] ∧ (0,0) ∉ [(3,7),(3,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(3,9)] → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_5_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ [(3,7),(3,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(3,9)] ∧ (4,9) ∉ [(3,7),(3,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(3,9)] → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_5_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ [(3,7),(3,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(3,9)] ∧ (3,7) ∉ [(3,7),(3,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(3,9)] → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_5_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ [(3,7),(3,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(3,9)] ∧ (1208925819614629174706177,0) ∉ [(3,7),(3,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(3,9)] → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_5_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_5_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_5_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_5_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_5_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_5_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_5_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_5_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_5_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_5_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(3,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ [(3,7),(3,9)]) : [(3,7),(3,9)] = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_sorted_6
example : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat)) ↔ False := by simp only [descendingKeys]; decide

-- sk_head_6_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ [(0,9),(2,8),(3,7)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)] ∧ (0,0) ∉ [(0,9),(2,8),(3,7)] ∧ ∀ (y : Nat × Nat), y ∈ [(0,9),(2,8),(3,7)] → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_6_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ [(0,9),(2,8),(3,7)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)] ∧ (4,9) ∉ [(0,9),(2,8),(3,7)] ∧ ∀ (y : Nat × Nat), y ∈ [(0,9),(2,8),(3,7)] → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_6_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ [(0,9),(2,8),(3,7)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)] ∧ (3,7) ∉ [(0,9),(2,8),(3,7)] ∧ ∀ (y : Nat × Nat), y ∈ [(0,9),(2,8),(3,7)] → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_6_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ [(0,9),(2,8),(3,7)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)] ∧ (1208925819614629174706177,0) ∉ [(0,9),(2,8),(3,7)] ∧ ∀ (y : Nat × Nat), y ∈ [(0,9),(2,8),(3,7)] → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_6_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_6_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_6_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_6_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_6_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_6_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_6_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_6_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_6_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_6_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(0,9),(2,8),(3,7)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ [(0,9),(2,8),(3,7)]) : [(0,9),(2,8),(3,7)] = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_sorted_7
example : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat)) ↔ True := by simp only [descendingKeys]; decide

-- sk_head_7_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ∧ (0,0) ∉ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ∧ ∀ (y : Nat × Nat), y ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_7_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ∧ (4,9) ∉ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ∧ ∀ (y : Nat × Nat), y ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_7_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ∧ (3,7) ∉ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ∧ ∀ (y : Nat × Nat), y ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_7_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ∧ (1208925819614629174706177,0) ∉ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ∧ ∀ (y : Nat × Nat), y ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_7_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_7_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_7_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_7_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_7_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_7_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_7_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_7_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_7_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_7_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)]) : [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_sorted_8
example : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat)) ↔ True := by simp only [descendingKeys]; decide

-- sk_head_8_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ [(3,99),(2,8),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)] ∧ (0,0) ∉ [(3,99),(2,8),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,99),(2,8),(0,9)] → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_8_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ [(3,99),(2,8),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)] ∧ (4,9) ∉ [(3,99),(2,8),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,99),(2,8),(0,9)] → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_8_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ [(3,99),(2,8),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)] ∧ (3,7) ∉ [(3,99),(2,8),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,99),(2,8),(0,9)] → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_8_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ [(3,99),(2,8),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)] ∧ (1208925819614629174706177,0) ∉ [(3,99),(2,8),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,99),(2,8),(0,9)] → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_8_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_8_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_8_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_8_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_8_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_8_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_8_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_8_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_8_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_8_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,99),(2,8),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ [(3,99),(2,8),(0,9)]) : [(3,99),(2,8),(0,9)] = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_sorted_9
example : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat)) ↔ True := by simp only [descendingKeys]; decide

-- sk_head_9_0
example (h : descendingKeys (α := Nat) ([(0,0)] ++ [(3,7),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(0,9)] ∧ (0,0) ∉ [(3,7),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(0,9)] → 0 > y.1 := sortedFstLessImp _ _ h

-- sk_head_9_1
example (h : descendingKeys (α := Nat) ([(4,9)] ++ [(3,7),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(0,9)] ∧ (4,9) ∉ [(3,7),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(0,9)] → 4 > y.1 := sortedFstLessImp _ _ h

-- sk_head_9_2
example (h : descendingKeys (α := Nat) ([(3,7)] ++ [(3,7),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(0,9)] ∧ (3,7) ∉ [(3,7),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(0,9)] → 3 > y.1 := sortedFstLessImp _ _ h

-- sk_head_9_3
example (h : descendingKeys (α := Nat) ([(1208925819614629174706177,0)] ++ [(3,7),(0,9)] : List (Nat × Nat))) : descendingKeys (α := Nat) [(3,7),(0,9)] ∧ (1208925819614629174706177,0) ∉ [(3,7),(0,9)] ∧ ∀ (y : Nat × Nat), y ∈ [(3,7),(0,9)] → 1208925819614629174706177 > y.1 := sortedFstLessImp _ _ h

-- sk_equal_9_0
example (hy : descendingKeys (α := Nat) (([] : List (Nat × Nat)) : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ ([] : List (Nat × Nat)) ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = ([] : List (Nat × Nat)) := sortedImpEqLists _ _ hy hx hm

-- sk_equal_9_1
example (hy : descendingKeys (α := Nat) ([(0,0)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,0)] ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = [(0,0)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_9_2
example (hy : descendingKeys (α := Nat) ([(3,7),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(2,8),(0,9)] ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = [(3,7),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_9_3
example (hy : descendingKeys (α := Nat) ([(2,8),(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(2,8),(3,7),(0,9)] ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = [(2,8),(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_9_4
example (hy : descendingKeys (α := Nat) ([(3,7),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,7)] ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = [(3,7),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_9_5
example (hy : descendingKeys (α := Nat) ([(3,7),(3,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(3,9)] ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = [(3,7),(3,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_9_6
example (hy : descendingKeys (α := Nat) ([(0,9),(2,8),(3,7)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(0,9),(2,8),(3,7)] ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = [(0,9),(2,8),(3,7)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_9_7
example (hy : descendingKeys (α := Nat) ([(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = [(1208925819614629174706176,3),(18446744073709551616,8),(1,1)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_9_8
example (hy : descendingKeys (α := Nat) ([(3,99),(2,8),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,99),(2,8),(0,9)] ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = [(3,99),(2,8),(0,9)] := sortedImpEqLists _ _ hy hx hm

-- sk_equal_9_9
example (hy : descendingKeys (α := Nat) ([(3,7),(0,9)] : List (Nat × Nat))) (hx : descendingKeys (α := Nat) [(3,7),(0,9)]) (hm : ∀ (x : Nat × Nat), x ∈ [(3,7),(0,9)] ↔ x ∈ [(3,7),(0,9)]) : [(3,7),(0,9)] = [(3,7),(0,9)] := sortedImpEqLists _ _ hy hx hm

example {α : Type} (xs ys : List (Nat × α)) (hy : descendingKeys ys) (hx : descendingKeys xs) (hm : ∀ x, x ∈ ys ↔ x ∈ xs) := sortedImpEqLists xs ys hy hx hm
