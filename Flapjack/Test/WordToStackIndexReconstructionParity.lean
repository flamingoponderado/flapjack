import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexReconstruction
open Flapjack Flapjack.WordToStackProofs
set_option maxRecDepth 8192

-- ir_output_0_0
example : indexList ([] : List Nat) 0 = [] := by decide +kernel

-- ir_recover_0_0
example : (indexList ([] : List Nat) 0).map (fun p => (p.1,p.2,([] : List Nat)[0-(p.1-0+1)]?)) = [] := by decide +kernel

-- ir_lookup_0_0_0
example : (sptAListLookup 0 (indexList ([] : List Nat) 0), ([] : List Nat)[(0+0)-(0+1)]?, decide (0 < 0+0)) = (none, none, false) := by decide +kernel

-- ir_lookup_0_0_1
example : (sptAListLookup 1 (indexList ([] : List Nat) 0), ([] : List Nat)[(0+0)-(1+1)]?, decide (1 < 0+0)) = (none, none, false) := by decide +kernel

-- ir_lookup_0_0_2
example : (sptAListLookup 2 (indexList ([] : List Nat) 0), ([] : List Nat)[(0+0)-(2+1)]?, decide (2 < 0+0)) = (none, none, false) := by decide +kernel

-- ir_lookup_0_0_900
example : (sptAListLookup 900 (indexList ([] : List Nat) 0), ([] : List Nat)[(0+0)-(900+1)]?, decide (900 < 0+0)) = (none, none, false) := by decide +kernel

-- ir_output_0_1
example : indexList ([] : List Nat) 1 = [] := by decide +kernel

-- ir_recover_0_1
example : (indexList ([] : List Nat) 1).map (fun p => (p.1,p.2,([] : List Nat)[0-(p.1-1+1)]?)) = [] := by decide +kernel

-- ir_lookup_0_1_0
example : (sptAListLookup 0 (indexList ([] : List Nat) 1), ([] : List Nat)[(0+1)-(0+1)]?, decide (0 < 0+1)) = (none, none, true) := by decide +kernel

-- ir_lookup_0_1_1
example : (sptAListLookup 1 (indexList ([] : List Nat) 1), ([] : List Nat)[(0+1)-(1+1)]?, decide (1 < 0+1)) = (none, none, false) := by decide +kernel

-- ir_lookup_0_1_2
example : (sptAListLookup 2 (indexList ([] : List Nat) 1), ([] : List Nat)[(0+1)-(2+1)]?, decide (2 < 0+1)) = (none, none, false) := by decide +kernel

-- ir_lookup_0_1_900
example : (sptAListLookup 900 (indexList ([] : List Nat) 1), ([] : List Nat)[(0+1)-(900+1)]?, decide (900 < 0+1)) = (none, none, false) := by decide +kernel

-- ir_output_0_4
example : indexList ([] : List Nat) 4 = [] := by decide +kernel

-- ir_recover_0_4
example : (indexList ([] : List Nat) 4).map (fun p => (p.1,p.2,([] : List Nat)[0-(p.1-4+1)]?)) = [] := by decide +kernel

-- ir_lookup_0_4_0
example : (sptAListLookup 0 (indexList ([] : List Nat) 4), ([] : List Nat)[(0+4)-(0+1)]?, decide (0 < 0+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_0_4_1
example : (sptAListLookup 1 (indexList ([] : List Nat) 4), ([] : List Nat)[(0+4)-(1+1)]?, decide (1 < 0+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_0_4_2
example : (sptAListLookup 2 (indexList ([] : List Nat) 4), ([] : List Nat)[(0+4)-(2+1)]?, decide (2 < 0+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_0_4_3
example : (sptAListLookup 3 (indexList ([] : List Nat) 4), ([] : List Nat)[(0+4)-(3+1)]?, decide (3 < 0+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_0_4_4
example : (sptAListLookup 4 (indexList ([] : List Nat) 4), ([] : List Nat)[(0+4)-(4+1)]?, decide (4 < 0+4)) = (none, none, false) := by decide +kernel

-- ir_lookup_0_4_5
example : (sptAListLookup 5 (indexList ([] : List Nat) 4), ([] : List Nat)[(0+4)-(5+1)]?, decide (5 < 0+4)) = (none, none, false) := by decide +kernel

-- ir_lookup_0_4_900
example : (sptAListLookup 900 (indexList ([] : List Nat) 4), ([] : List Nat)[(0+4)-(900+1)]?, decide (900 < 0+4)) = (none, none, false) := by decide +kernel

-- ir_output_0_99
example : indexList ([] : List Nat) 99 = [] := by decide +kernel

-- ir_recover_0_99
example : (indexList ([] : List Nat) 99).map (fun p => (p.1,p.2,([] : List Nat)[0-(p.1-99+1)]?)) = [] := by decide +kernel

-- ir_lookup_0_99_0
example : (sptAListLookup 0 (indexList ([] : List Nat) 99), ([] : List Nat)[(0+99)-(0+1)]?, decide (0 < 0+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_0_99_1
example : (sptAListLookup 1 (indexList ([] : List Nat) 99), ([] : List Nat)[(0+99)-(1+1)]?, decide (1 < 0+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_0_99_2
example : (sptAListLookup 2 (indexList ([] : List Nat) 99), ([] : List Nat)[(0+99)-(2+1)]?, decide (2 < 0+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_0_99_98
example : (sptAListLookup 98 (indexList ([] : List Nat) 99), ([] : List Nat)[(0+99)-(98+1)]?, decide (98 < 0+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_0_99_99
example : (sptAListLookup 99 (indexList ([] : List Nat) 99), ([] : List Nat)[(0+99)-(99+1)]?, decide (99 < 0+99)) = (none, none, false) := by decide +kernel

-- ir_lookup_0_99_100
example : (sptAListLookup 100 (indexList ([] : List Nat) 99), ([] : List Nat)[(0+99)-(100+1)]?, decide (100 < 0+99)) = (none, none, false) := by decide +kernel

-- ir_lookup_0_99_900
example : (sptAListLookup 900 (indexList ([] : List Nat) 99), ([] : List Nat)[(0+99)-(900+1)]?, decide (900 < 0+99)) = (none, none, false) := by decide +kernel

-- ir_output_1_0
example : indexList ([0] : List Nat) 0 = [(0,0)] := by decide +kernel

-- ir_recover_1_0
example : (indexList ([0] : List Nat) 0).map (fun p => (p.1,p.2,([0] : List Nat)[1-(p.1-0+1)]?)) = [(0,0,some 0)] := by decide +kernel

-- ir_lookup_1_0_0
example : (sptAListLookup 0 (indexList ([0] : List Nat) 0), ([0] : List Nat)[(1+0)-(0+1)]?, decide (0 < 1+0)) = (some 0, some 0, true) := by decide +kernel

-- ir_lookup_1_0_1
example : (sptAListLookup 1 (indexList ([0] : List Nat) 0), ([0] : List Nat)[(1+0)-(1+1)]?, decide (1 < 1+0)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_1_0_2
example : (sptAListLookup 2 (indexList ([0] : List Nat) 0), ([0] : List Nat)[(1+0)-(2+1)]?, decide (2 < 1+0)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_1_0_900
example : (sptAListLookup 900 (indexList ([0] : List Nat) 0), ([0] : List Nat)[(1+0)-(900+1)]?, decide (900 < 1+0)) = (none, some 0, false) := by decide +kernel

-- ir_output_1_1
example : indexList ([0] : List Nat) 1 = [(1,0)] := by decide +kernel

-- ir_recover_1_1
example : (indexList ([0] : List Nat) 1).map (fun p => (p.1,p.2,([0] : List Nat)[1-(p.1-1+1)]?)) = [(1,0,some 0)] := by decide +kernel

-- ir_lookup_1_1_0
example : (sptAListLookup 0 (indexList ([0] : List Nat) 1), ([0] : List Nat)[(1+1)-(0+1)]?, decide (0 < 1+1)) = (none, none, true) := by decide +kernel

-- ir_lookup_1_1_1
example : (sptAListLookup 1 (indexList ([0] : List Nat) 1), ([0] : List Nat)[(1+1)-(1+1)]?, decide (1 < 1+1)) = (some 0, some 0, true) := by decide +kernel

-- ir_lookup_1_1_2
example : (sptAListLookup 2 (indexList ([0] : List Nat) 1), ([0] : List Nat)[(1+1)-(2+1)]?, decide (2 < 1+1)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_1_1_3
example : (sptAListLookup 3 (indexList ([0] : List Nat) 1), ([0] : List Nat)[(1+1)-(3+1)]?, decide (3 < 1+1)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_1_1_900
example : (sptAListLookup 900 (indexList ([0] : List Nat) 1), ([0] : List Nat)[(1+1)-(900+1)]?, decide (900 < 1+1)) = (none, some 0, false) := by decide +kernel

-- ir_output_1_4
example : indexList ([0] : List Nat) 4 = [(4,0)] := by decide +kernel

-- ir_recover_1_4
example : (indexList ([0] : List Nat) 4).map (fun p => (p.1,p.2,([0] : List Nat)[1-(p.1-4+1)]?)) = [(4,0,some 0)] := by decide +kernel

-- ir_lookup_1_4_0
example : (sptAListLookup 0 (indexList ([0] : List Nat) 4), ([0] : List Nat)[(1+4)-(0+1)]?, decide (0 < 1+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_1_4_1
example : (sptAListLookup 1 (indexList ([0] : List Nat) 4), ([0] : List Nat)[(1+4)-(1+1)]?, decide (1 < 1+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_1_4_2
example : (sptAListLookup 2 (indexList ([0] : List Nat) 4), ([0] : List Nat)[(1+4)-(2+1)]?, decide (2 < 1+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_1_4_3
example : (sptAListLookup 3 (indexList ([0] : List Nat) 4), ([0] : List Nat)[(1+4)-(3+1)]?, decide (3 < 1+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_1_4_4
example : (sptAListLookup 4 (indexList ([0] : List Nat) 4), ([0] : List Nat)[(1+4)-(4+1)]?, decide (4 < 1+4)) = (some 0, some 0, true) := by decide +kernel

-- ir_lookup_1_4_5
example : (sptAListLookup 5 (indexList ([0] : List Nat) 4), ([0] : List Nat)[(1+4)-(5+1)]?, decide (5 < 1+4)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_1_4_6
example : (sptAListLookup 6 (indexList ([0] : List Nat) 4), ([0] : List Nat)[(1+4)-(6+1)]?, decide (6 < 1+4)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_1_4_900
example : (sptAListLookup 900 (indexList ([0] : List Nat) 4), ([0] : List Nat)[(1+4)-(900+1)]?, decide (900 < 1+4)) = (none, some 0, false) := by decide +kernel

-- ir_output_1_99
example : indexList ([0] : List Nat) 99 = [(99,0)] := by decide +kernel

-- ir_recover_1_99
example : (indexList ([0] : List Nat) 99).map (fun p => (p.1,p.2,([0] : List Nat)[1-(p.1-99+1)]?)) = [(99,0,some 0)] := by decide +kernel

-- ir_lookup_1_99_0
example : (sptAListLookup 0 (indexList ([0] : List Nat) 99), ([0] : List Nat)[(1+99)-(0+1)]?, decide (0 < 1+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_1_99_1
example : (sptAListLookup 1 (indexList ([0] : List Nat) 99), ([0] : List Nat)[(1+99)-(1+1)]?, decide (1 < 1+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_1_99_2
example : (sptAListLookup 2 (indexList ([0] : List Nat) 99), ([0] : List Nat)[(1+99)-(2+1)]?, decide (2 < 1+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_1_99_98
example : (sptAListLookup 98 (indexList ([0] : List Nat) 99), ([0] : List Nat)[(1+99)-(98+1)]?, decide (98 < 1+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_1_99_99
example : (sptAListLookup 99 (indexList ([0] : List Nat) 99), ([0] : List Nat)[(1+99)-(99+1)]?, decide (99 < 1+99)) = (some 0, some 0, true) := by decide +kernel

-- ir_lookup_1_99_100
example : (sptAListLookup 100 (indexList ([0] : List Nat) 99), ([0] : List Nat)[(1+99)-(100+1)]?, decide (100 < 1+99)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_1_99_101
example : (sptAListLookup 101 (indexList ([0] : List Nat) 99), ([0] : List Nat)[(1+99)-(101+1)]?, decide (101 < 1+99)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_1_99_900
example : (sptAListLookup 900 (indexList ([0] : List Nat) 99), ([0] : List Nat)[(1+99)-(900+1)]?, decide (900 < 1+99)) = (none, some 0, false) := by decide +kernel

-- ir_output_2_0
example : indexList ([9] : List Nat) 0 = [(0,9)] := by decide +kernel

-- ir_recover_2_0
example : (indexList ([9] : List Nat) 0).map (fun p => (p.1,p.2,([9] : List Nat)[1-(p.1-0+1)]?)) = [(0,9,some 9)] := by decide +kernel

-- ir_lookup_2_0_0
example : (sptAListLookup 0 (indexList ([9] : List Nat) 0), ([9] : List Nat)[(1+0)-(0+1)]?, decide (0 < 1+0)) = (some 9, some 9, true) := by decide +kernel

-- ir_lookup_2_0_1
example : (sptAListLookup 1 (indexList ([9] : List Nat) 0), ([9] : List Nat)[(1+0)-(1+1)]?, decide (1 < 1+0)) = (none, some 9, false) := by decide +kernel

-- ir_lookup_2_0_2
example : (sptAListLookup 2 (indexList ([9] : List Nat) 0), ([9] : List Nat)[(1+0)-(2+1)]?, decide (2 < 1+0)) = (none, some 9, false) := by decide +kernel

-- ir_lookup_2_0_900
example : (sptAListLookup 900 (indexList ([9] : List Nat) 0), ([9] : List Nat)[(1+0)-(900+1)]?, decide (900 < 1+0)) = (none, some 9, false) := by decide +kernel

-- ir_output_2_1
example : indexList ([9] : List Nat) 1 = [(1,9)] := by decide +kernel

-- ir_recover_2_1
example : (indexList ([9] : List Nat) 1).map (fun p => (p.1,p.2,([9] : List Nat)[1-(p.1-1+1)]?)) = [(1,9,some 9)] := by decide +kernel

-- ir_lookup_2_1_0
example : (sptAListLookup 0 (indexList ([9] : List Nat) 1), ([9] : List Nat)[(1+1)-(0+1)]?, decide (0 < 1+1)) = (none, none, true) := by decide +kernel

-- ir_lookup_2_1_1
example : (sptAListLookup 1 (indexList ([9] : List Nat) 1), ([9] : List Nat)[(1+1)-(1+1)]?, decide (1 < 1+1)) = (some 9, some 9, true) := by decide +kernel

-- ir_lookup_2_1_2
example : (sptAListLookup 2 (indexList ([9] : List Nat) 1), ([9] : List Nat)[(1+1)-(2+1)]?, decide (2 < 1+1)) = (none, some 9, false) := by decide +kernel

-- ir_lookup_2_1_3
example : (sptAListLookup 3 (indexList ([9] : List Nat) 1), ([9] : List Nat)[(1+1)-(3+1)]?, decide (3 < 1+1)) = (none, some 9, false) := by decide +kernel

-- ir_lookup_2_1_900
example : (sptAListLookup 900 (indexList ([9] : List Nat) 1), ([9] : List Nat)[(1+1)-(900+1)]?, decide (900 < 1+1)) = (none, some 9, false) := by decide +kernel

-- ir_output_2_4
example : indexList ([9] : List Nat) 4 = [(4,9)] := by decide +kernel

-- ir_recover_2_4
example : (indexList ([9] : List Nat) 4).map (fun p => (p.1,p.2,([9] : List Nat)[1-(p.1-4+1)]?)) = [(4,9,some 9)] := by decide +kernel

-- ir_lookup_2_4_0
example : (sptAListLookup 0 (indexList ([9] : List Nat) 4), ([9] : List Nat)[(1+4)-(0+1)]?, decide (0 < 1+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_2_4_1
example : (sptAListLookup 1 (indexList ([9] : List Nat) 4), ([9] : List Nat)[(1+4)-(1+1)]?, decide (1 < 1+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_2_4_2
example : (sptAListLookup 2 (indexList ([9] : List Nat) 4), ([9] : List Nat)[(1+4)-(2+1)]?, decide (2 < 1+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_2_4_3
example : (sptAListLookup 3 (indexList ([9] : List Nat) 4), ([9] : List Nat)[(1+4)-(3+1)]?, decide (3 < 1+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_2_4_4
example : (sptAListLookup 4 (indexList ([9] : List Nat) 4), ([9] : List Nat)[(1+4)-(4+1)]?, decide (4 < 1+4)) = (some 9, some 9, true) := by decide +kernel

-- ir_lookup_2_4_5
example : (sptAListLookup 5 (indexList ([9] : List Nat) 4), ([9] : List Nat)[(1+4)-(5+1)]?, decide (5 < 1+4)) = (none, some 9, false) := by decide +kernel

-- ir_lookup_2_4_6
example : (sptAListLookup 6 (indexList ([9] : List Nat) 4), ([9] : List Nat)[(1+4)-(6+1)]?, decide (6 < 1+4)) = (none, some 9, false) := by decide +kernel

-- ir_lookup_2_4_900
example : (sptAListLookup 900 (indexList ([9] : List Nat) 4), ([9] : List Nat)[(1+4)-(900+1)]?, decide (900 < 1+4)) = (none, some 9, false) := by decide +kernel

-- ir_output_2_99
example : indexList ([9] : List Nat) 99 = [(99,9)] := by decide +kernel

-- ir_recover_2_99
example : (indexList ([9] : List Nat) 99).map (fun p => (p.1,p.2,([9] : List Nat)[1-(p.1-99+1)]?)) = [(99,9,some 9)] := by decide +kernel

-- ir_lookup_2_99_0
example : (sptAListLookup 0 (indexList ([9] : List Nat) 99), ([9] : List Nat)[(1+99)-(0+1)]?, decide (0 < 1+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_2_99_1
example : (sptAListLookup 1 (indexList ([9] : List Nat) 99), ([9] : List Nat)[(1+99)-(1+1)]?, decide (1 < 1+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_2_99_2
example : (sptAListLookup 2 (indexList ([9] : List Nat) 99), ([9] : List Nat)[(1+99)-(2+1)]?, decide (2 < 1+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_2_99_98
example : (sptAListLookup 98 (indexList ([9] : List Nat) 99), ([9] : List Nat)[(1+99)-(98+1)]?, decide (98 < 1+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_2_99_99
example : (sptAListLookup 99 (indexList ([9] : List Nat) 99), ([9] : List Nat)[(1+99)-(99+1)]?, decide (99 < 1+99)) = (some 9, some 9, true) := by decide +kernel

-- ir_lookup_2_99_100
example : (sptAListLookup 100 (indexList ([9] : List Nat) 99), ([9] : List Nat)[(1+99)-(100+1)]?, decide (100 < 1+99)) = (none, some 9, false) := by decide +kernel

-- ir_lookup_2_99_101
example : (sptAListLookup 101 (indexList ([9] : List Nat) 99), ([9] : List Nat)[(1+99)-(101+1)]?, decide (101 < 1+99)) = (none, some 9, false) := by decide +kernel

-- ir_lookup_2_99_900
example : (sptAListLookup 900 (indexList ([9] : List Nat) 99), ([9] : List Nat)[(1+99)-(900+1)]?, decide (900 < 1+99)) = (none, some 9, false) := by decide +kernel

-- ir_output_3_0
example : indexList ([10, 20] : List Nat) 0 = [(1,10), (0,20)] := by decide +kernel

-- ir_recover_3_0
example : (indexList ([10, 20] : List Nat) 0).map (fun p => (p.1,p.2,([10, 20] : List Nat)[2-(p.1-0+1)]?)) = [(1,10,some 10), (0,20,some 20)] := by decide +kernel

-- ir_lookup_3_0_0
example : (sptAListLookup 0 (indexList ([10, 20] : List Nat) 0), ([10, 20] : List Nat)[(2+0)-(0+1)]?, decide (0 < 2+0)) = (some 20, some 20, true) := by decide +kernel

-- ir_lookup_3_0_1
example : (sptAListLookup 1 (indexList ([10, 20] : List Nat) 0), ([10, 20] : List Nat)[(2+0)-(1+1)]?, decide (1 < 2+0)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_3_0_2
example : (sptAListLookup 2 (indexList ([10, 20] : List Nat) 0), ([10, 20] : List Nat)[(2+0)-(2+1)]?, decide (2 < 2+0)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_3_0_3
example : (sptAListLookup 3 (indexList ([10, 20] : List Nat) 0), ([10, 20] : List Nat)[(2+0)-(3+1)]?, decide (3 < 2+0)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_3_0_900
example : (sptAListLookup 900 (indexList ([10, 20] : List Nat) 0), ([10, 20] : List Nat)[(2+0)-(900+1)]?, decide (900 < 2+0)) = (none, some 10, false) := by decide +kernel

-- ir_output_3_1
example : indexList ([10, 20] : List Nat) 1 = [(2,10), (1,20)] := by decide +kernel

-- ir_recover_3_1
example : (indexList ([10, 20] : List Nat) 1).map (fun p => (p.1,p.2,([10, 20] : List Nat)[2-(p.1-1+1)]?)) = [(2,10,some 10), (1,20,some 20)] := by decide +kernel

-- ir_lookup_3_1_0
example : (sptAListLookup 0 (indexList ([10, 20] : List Nat) 1), ([10, 20] : List Nat)[(2+1)-(0+1)]?, decide (0 < 2+1)) = (none, none, true) := by decide +kernel

-- ir_lookup_3_1_1
example : (sptAListLookup 1 (indexList ([10, 20] : List Nat) 1), ([10, 20] : List Nat)[(2+1)-(1+1)]?, decide (1 < 2+1)) = (some 20, some 20, true) := by decide +kernel

-- ir_lookup_3_1_2
example : (sptAListLookup 2 (indexList ([10, 20] : List Nat) 1), ([10, 20] : List Nat)[(2+1)-(2+1)]?, decide (2 < 2+1)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_3_1_3
example : (sptAListLookup 3 (indexList ([10, 20] : List Nat) 1), ([10, 20] : List Nat)[(2+1)-(3+1)]?, decide (3 < 2+1)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_3_1_4
example : (sptAListLookup 4 (indexList ([10, 20] : List Nat) 1), ([10, 20] : List Nat)[(2+1)-(4+1)]?, decide (4 < 2+1)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_3_1_900
example : (sptAListLookup 900 (indexList ([10, 20] : List Nat) 1), ([10, 20] : List Nat)[(2+1)-(900+1)]?, decide (900 < 2+1)) = (none, some 10, false) := by decide +kernel

-- ir_output_3_4
example : indexList ([10, 20] : List Nat) 4 = [(5,10), (4,20)] := by decide +kernel

-- ir_recover_3_4
example : (indexList ([10, 20] : List Nat) 4).map (fun p => (p.1,p.2,([10, 20] : List Nat)[2-(p.1-4+1)]?)) = [(5,10,some 10), (4,20,some 20)] := by decide +kernel

-- ir_lookup_3_4_0
example : (sptAListLookup 0 (indexList ([10, 20] : List Nat) 4), ([10, 20] : List Nat)[(2+4)-(0+1)]?, decide (0 < 2+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_3_4_1
example : (sptAListLookup 1 (indexList ([10, 20] : List Nat) 4), ([10, 20] : List Nat)[(2+4)-(1+1)]?, decide (1 < 2+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_3_4_2
example : (sptAListLookup 2 (indexList ([10, 20] : List Nat) 4), ([10, 20] : List Nat)[(2+4)-(2+1)]?, decide (2 < 2+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_3_4_3
example : (sptAListLookup 3 (indexList ([10, 20] : List Nat) 4), ([10, 20] : List Nat)[(2+4)-(3+1)]?, decide (3 < 2+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_3_4_4
example : (sptAListLookup 4 (indexList ([10, 20] : List Nat) 4), ([10, 20] : List Nat)[(2+4)-(4+1)]?, decide (4 < 2+4)) = (some 20, some 20, true) := by decide +kernel

-- ir_lookup_3_4_5
example : (sptAListLookup 5 (indexList ([10, 20] : List Nat) 4), ([10, 20] : List Nat)[(2+4)-(5+1)]?, decide (5 < 2+4)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_3_4_6
example : (sptAListLookup 6 (indexList ([10, 20] : List Nat) 4), ([10, 20] : List Nat)[(2+4)-(6+1)]?, decide (6 < 2+4)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_3_4_7
example : (sptAListLookup 7 (indexList ([10, 20] : List Nat) 4), ([10, 20] : List Nat)[(2+4)-(7+1)]?, decide (7 < 2+4)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_3_4_900
example : (sptAListLookup 900 (indexList ([10, 20] : List Nat) 4), ([10, 20] : List Nat)[(2+4)-(900+1)]?, decide (900 < 2+4)) = (none, some 10, false) := by decide +kernel

-- ir_output_3_99
example : indexList ([10, 20] : List Nat) 99 = [(100,10), (99,20)] := by decide +kernel

-- ir_recover_3_99
example : (indexList ([10, 20] : List Nat) 99).map (fun p => (p.1,p.2,([10, 20] : List Nat)[2-(p.1-99+1)]?)) = [(100,10,some 10), (99,20,some 20)] := by decide +kernel

-- ir_lookup_3_99_0
example : (sptAListLookup 0 (indexList ([10, 20] : List Nat) 99), ([10, 20] : List Nat)[(2+99)-(0+1)]?, decide (0 < 2+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_3_99_1
example : (sptAListLookup 1 (indexList ([10, 20] : List Nat) 99), ([10, 20] : List Nat)[(2+99)-(1+1)]?, decide (1 < 2+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_3_99_2
example : (sptAListLookup 2 (indexList ([10, 20] : List Nat) 99), ([10, 20] : List Nat)[(2+99)-(2+1)]?, decide (2 < 2+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_3_99_98
example : (sptAListLookup 98 (indexList ([10, 20] : List Nat) 99), ([10, 20] : List Nat)[(2+99)-(98+1)]?, decide (98 < 2+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_3_99_99
example : (sptAListLookup 99 (indexList ([10, 20] : List Nat) 99), ([10, 20] : List Nat)[(2+99)-(99+1)]?, decide (99 < 2+99)) = (some 20, some 20, true) := by decide +kernel

-- ir_lookup_3_99_100
example : (sptAListLookup 100 (indexList ([10, 20] : List Nat) 99), ([10, 20] : List Nat)[(2+99)-(100+1)]?, decide (100 < 2+99)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_3_99_101
example : (sptAListLookup 101 (indexList ([10, 20] : List Nat) 99), ([10, 20] : List Nat)[(2+99)-(101+1)]?, decide (101 < 2+99)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_3_99_102
example : (sptAListLookup 102 (indexList ([10, 20] : List Nat) 99), ([10, 20] : List Nat)[(2+99)-(102+1)]?, decide (102 < 2+99)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_3_99_900
example : (sptAListLookup 900 (indexList ([10, 20] : List Nat) 99), ([10, 20] : List Nat)[(2+99)-(900+1)]?, decide (900 < 2+99)) = (none, some 10, false) := by decide +kernel

-- ir_output_4_0
example : indexList ([10, 10] : List Nat) 0 = [(1,10), (0,10)] := by decide +kernel

-- ir_recover_4_0
example : (indexList ([10, 10] : List Nat) 0).map (fun p => (p.1,p.2,([10, 10] : List Nat)[2-(p.1-0+1)]?)) = [(1,10,some 10), (0,10,some 10)] := by decide +kernel

-- ir_lookup_4_0_0
example : (sptAListLookup 0 (indexList ([10, 10] : List Nat) 0), ([10, 10] : List Nat)[(2+0)-(0+1)]?, decide (0 < 2+0)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_4_0_1
example : (sptAListLookup 1 (indexList ([10, 10] : List Nat) 0), ([10, 10] : List Nat)[(2+0)-(1+1)]?, decide (1 < 2+0)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_4_0_2
example : (sptAListLookup 2 (indexList ([10, 10] : List Nat) 0), ([10, 10] : List Nat)[(2+0)-(2+1)]?, decide (2 < 2+0)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_4_0_3
example : (sptAListLookup 3 (indexList ([10, 10] : List Nat) 0), ([10, 10] : List Nat)[(2+0)-(3+1)]?, decide (3 < 2+0)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_4_0_900
example : (sptAListLookup 900 (indexList ([10, 10] : List Nat) 0), ([10, 10] : List Nat)[(2+0)-(900+1)]?, decide (900 < 2+0)) = (none, some 10, false) := by decide +kernel

-- ir_output_4_1
example : indexList ([10, 10] : List Nat) 1 = [(2,10), (1,10)] := by decide +kernel

-- ir_recover_4_1
example : (indexList ([10, 10] : List Nat) 1).map (fun p => (p.1,p.2,([10, 10] : List Nat)[2-(p.1-1+1)]?)) = [(2,10,some 10), (1,10,some 10)] := by decide +kernel

-- ir_lookup_4_1_0
example : (sptAListLookup 0 (indexList ([10, 10] : List Nat) 1), ([10, 10] : List Nat)[(2+1)-(0+1)]?, decide (0 < 2+1)) = (none, none, true) := by decide +kernel

-- ir_lookup_4_1_1
example : (sptAListLookup 1 (indexList ([10, 10] : List Nat) 1), ([10, 10] : List Nat)[(2+1)-(1+1)]?, decide (1 < 2+1)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_4_1_2
example : (sptAListLookup 2 (indexList ([10, 10] : List Nat) 1), ([10, 10] : List Nat)[(2+1)-(2+1)]?, decide (2 < 2+1)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_4_1_3
example : (sptAListLookup 3 (indexList ([10, 10] : List Nat) 1), ([10, 10] : List Nat)[(2+1)-(3+1)]?, decide (3 < 2+1)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_4_1_4
example : (sptAListLookup 4 (indexList ([10, 10] : List Nat) 1), ([10, 10] : List Nat)[(2+1)-(4+1)]?, decide (4 < 2+1)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_4_1_900
example : (sptAListLookup 900 (indexList ([10, 10] : List Nat) 1), ([10, 10] : List Nat)[(2+1)-(900+1)]?, decide (900 < 2+1)) = (none, some 10, false) := by decide +kernel

-- ir_output_4_4
example : indexList ([10, 10] : List Nat) 4 = [(5,10), (4,10)] := by decide +kernel

-- ir_recover_4_4
example : (indexList ([10, 10] : List Nat) 4).map (fun p => (p.1,p.2,([10, 10] : List Nat)[2-(p.1-4+1)]?)) = [(5,10,some 10), (4,10,some 10)] := by decide +kernel

-- ir_lookup_4_4_0
example : (sptAListLookup 0 (indexList ([10, 10] : List Nat) 4), ([10, 10] : List Nat)[(2+4)-(0+1)]?, decide (0 < 2+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_4_4_1
example : (sptAListLookup 1 (indexList ([10, 10] : List Nat) 4), ([10, 10] : List Nat)[(2+4)-(1+1)]?, decide (1 < 2+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_4_4_2
example : (sptAListLookup 2 (indexList ([10, 10] : List Nat) 4), ([10, 10] : List Nat)[(2+4)-(2+1)]?, decide (2 < 2+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_4_4_3
example : (sptAListLookup 3 (indexList ([10, 10] : List Nat) 4), ([10, 10] : List Nat)[(2+4)-(3+1)]?, decide (3 < 2+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_4_4_4
example : (sptAListLookup 4 (indexList ([10, 10] : List Nat) 4), ([10, 10] : List Nat)[(2+4)-(4+1)]?, decide (4 < 2+4)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_4_4_5
example : (sptAListLookup 5 (indexList ([10, 10] : List Nat) 4), ([10, 10] : List Nat)[(2+4)-(5+1)]?, decide (5 < 2+4)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_4_4_6
example : (sptAListLookup 6 (indexList ([10, 10] : List Nat) 4), ([10, 10] : List Nat)[(2+4)-(6+1)]?, decide (6 < 2+4)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_4_4_7
example : (sptAListLookup 7 (indexList ([10, 10] : List Nat) 4), ([10, 10] : List Nat)[(2+4)-(7+1)]?, decide (7 < 2+4)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_4_4_900
example : (sptAListLookup 900 (indexList ([10, 10] : List Nat) 4), ([10, 10] : List Nat)[(2+4)-(900+1)]?, decide (900 < 2+4)) = (none, some 10, false) := by decide +kernel

-- ir_output_4_99
example : indexList ([10, 10] : List Nat) 99 = [(100,10), (99,10)] := by decide +kernel

-- ir_recover_4_99
example : (indexList ([10, 10] : List Nat) 99).map (fun p => (p.1,p.2,([10, 10] : List Nat)[2-(p.1-99+1)]?)) = [(100,10,some 10), (99,10,some 10)] := by decide +kernel

-- ir_lookup_4_99_0
example : (sptAListLookup 0 (indexList ([10, 10] : List Nat) 99), ([10, 10] : List Nat)[(2+99)-(0+1)]?, decide (0 < 2+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_4_99_1
example : (sptAListLookup 1 (indexList ([10, 10] : List Nat) 99), ([10, 10] : List Nat)[(2+99)-(1+1)]?, decide (1 < 2+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_4_99_2
example : (sptAListLookup 2 (indexList ([10, 10] : List Nat) 99), ([10, 10] : List Nat)[(2+99)-(2+1)]?, decide (2 < 2+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_4_99_98
example : (sptAListLookup 98 (indexList ([10, 10] : List Nat) 99), ([10, 10] : List Nat)[(2+99)-(98+1)]?, decide (98 < 2+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_4_99_99
example : (sptAListLookup 99 (indexList ([10, 10] : List Nat) 99), ([10, 10] : List Nat)[(2+99)-(99+1)]?, decide (99 < 2+99)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_4_99_100
example : (sptAListLookup 100 (indexList ([10, 10] : List Nat) 99), ([10, 10] : List Nat)[(2+99)-(100+1)]?, decide (100 < 2+99)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_4_99_101
example : (sptAListLookup 101 (indexList ([10, 10] : List Nat) 99), ([10, 10] : List Nat)[(2+99)-(101+1)]?, decide (101 < 2+99)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_4_99_102
example : (sptAListLookup 102 (indexList ([10, 10] : List Nat) 99), ([10, 10] : List Nat)[(2+99)-(102+1)]?, decide (102 < 2+99)) = (none, some 10, false) := by decide +kernel

-- ir_lookup_4_99_900
example : (sptAListLookup 900 (indexList ([10, 10] : List Nat) 99), ([10, 10] : List Nat)[(2+99)-(900+1)]?, decide (900 < 2+99)) = (none, some 10, false) := by decide +kernel

-- ir_output_5_0
example : indexList ([30, 20, 10] : List Nat) 0 = [(2,30), (1,20), (0,10)] := by decide +kernel

-- ir_recover_5_0
example : (indexList ([30, 20, 10] : List Nat) 0).map (fun p => (p.1,p.2,([30, 20, 10] : List Nat)[3-(p.1-0+1)]?)) = [(2,30,some 30), (1,20,some 20), (0,10,some 10)] := by decide +kernel

-- ir_lookup_5_0_0
example : (sptAListLookup 0 (indexList ([30, 20, 10] : List Nat) 0), ([30, 20, 10] : List Nat)[(3+0)-(0+1)]?, decide (0 < 3+0)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_5_0_1
example : (sptAListLookup 1 (indexList ([30, 20, 10] : List Nat) 0), ([30, 20, 10] : List Nat)[(3+0)-(1+1)]?, decide (1 < 3+0)) = (some 20, some 20, true) := by decide +kernel

-- ir_lookup_5_0_2
example : (sptAListLookup 2 (indexList ([30, 20, 10] : List Nat) 0), ([30, 20, 10] : List Nat)[(3+0)-(2+1)]?, decide (2 < 3+0)) = (some 30, some 30, true) := by decide +kernel

-- ir_lookup_5_0_3
example : (sptAListLookup 3 (indexList ([30, 20, 10] : List Nat) 0), ([30, 20, 10] : List Nat)[(3+0)-(3+1)]?, decide (3 < 3+0)) = (none, some 30, false) := by decide +kernel

-- ir_lookup_5_0_4
example : (sptAListLookup 4 (indexList ([30, 20, 10] : List Nat) 0), ([30, 20, 10] : List Nat)[(3+0)-(4+1)]?, decide (4 < 3+0)) = (none, some 30, false) := by decide +kernel

-- ir_lookup_5_0_900
example : (sptAListLookup 900 (indexList ([30, 20, 10] : List Nat) 0), ([30, 20, 10] : List Nat)[(3+0)-(900+1)]?, decide (900 < 3+0)) = (none, some 30, false) := by decide +kernel

-- ir_output_5_1
example : indexList ([30, 20, 10] : List Nat) 1 = [(3,30), (2,20), (1,10)] := by decide +kernel

-- ir_recover_5_1
example : (indexList ([30, 20, 10] : List Nat) 1).map (fun p => (p.1,p.2,([30, 20, 10] : List Nat)[3-(p.1-1+1)]?)) = [(3,30,some 30), (2,20,some 20), (1,10,some 10)] := by decide +kernel

-- ir_lookup_5_1_0
example : (sptAListLookup 0 (indexList ([30, 20, 10] : List Nat) 1), ([30, 20, 10] : List Nat)[(3+1)-(0+1)]?, decide (0 < 3+1)) = (none, none, true) := by decide +kernel

-- ir_lookup_5_1_1
example : (sptAListLookup 1 (indexList ([30, 20, 10] : List Nat) 1), ([30, 20, 10] : List Nat)[(3+1)-(1+1)]?, decide (1 < 3+1)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_5_1_2
example : (sptAListLookup 2 (indexList ([30, 20, 10] : List Nat) 1), ([30, 20, 10] : List Nat)[(3+1)-(2+1)]?, decide (2 < 3+1)) = (some 20, some 20, true) := by decide +kernel

-- ir_lookup_5_1_3
example : (sptAListLookup 3 (indexList ([30, 20, 10] : List Nat) 1), ([30, 20, 10] : List Nat)[(3+1)-(3+1)]?, decide (3 < 3+1)) = (some 30, some 30, true) := by decide +kernel

-- ir_lookup_5_1_4
example : (sptAListLookup 4 (indexList ([30, 20, 10] : List Nat) 1), ([30, 20, 10] : List Nat)[(3+1)-(4+1)]?, decide (4 < 3+1)) = (none, some 30, false) := by decide +kernel

-- ir_lookup_5_1_5
example : (sptAListLookup 5 (indexList ([30, 20, 10] : List Nat) 1), ([30, 20, 10] : List Nat)[(3+1)-(5+1)]?, decide (5 < 3+1)) = (none, some 30, false) := by decide +kernel

-- ir_lookup_5_1_900
example : (sptAListLookup 900 (indexList ([30, 20, 10] : List Nat) 1), ([30, 20, 10] : List Nat)[(3+1)-(900+1)]?, decide (900 < 3+1)) = (none, some 30, false) := by decide +kernel

-- ir_output_5_4
example : indexList ([30, 20, 10] : List Nat) 4 = [(6,30), (5,20), (4,10)] := by decide +kernel

-- ir_recover_5_4
example : (indexList ([30, 20, 10] : List Nat) 4).map (fun p => (p.1,p.2,([30, 20, 10] : List Nat)[3-(p.1-4+1)]?)) = [(6,30,some 30), (5,20,some 20), (4,10,some 10)] := by decide +kernel

-- ir_lookup_5_4_0
example : (sptAListLookup 0 (indexList ([30, 20, 10] : List Nat) 4), ([30, 20, 10] : List Nat)[(3+4)-(0+1)]?, decide (0 < 3+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_5_4_1
example : (sptAListLookup 1 (indexList ([30, 20, 10] : List Nat) 4), ([30, 20, 10] : List Nat)[(3+4)-(1+1)]?, decide (1 < 3+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_5_4_2
example : (sptAListLookup 2 (indexList ([30, 20, 10] : List Nat) 4), ([30, 20, 10] : List Nat)[(3+4)-(2+1)]?, decide (2 < 3+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_5_4_3
example : (sptAListLookup 3 (indexList ([30, 20, 10] : List Nat) 4), ([30, 20, 10] : List Nat)[(3+4)-(3+1)]?, decide (3 < 3+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_5_4_4
example : (sptAListLookup 4 (indexList ([30, 20, 10] : List Nat) 4), ([30, 20, 10] : List Nat)[(3+4)-(4+1)]?, decide (4 < 3+4)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_5_4_6
example : (sptAListLookup 6 (indexList ([30, 20, 10] : List Nat) 4), ([30, 20, 10] : List Nat)[(3+4)-(6+1)]?, decide (6 < 3+4)) = (some 30, some 30, true) := by decide +kernel

-- ir_lookup_5_4_7
example : (sptAListLookup 7 (indexList ([30, 20, 10] : List Nat) 4), ([30, 20, 10] : List Nat)[(3+4)-(7+1)]?, decide (7 < 3+4)) = (none, some 30, false) := by decide +kernel

-- ir_lookup_5_4_8
example : (sptAListLookup 8 (indexList ([30, 20, 10] : List Nat) 4), ([30, 20, 10] : List Nat)[(3+4)-(8+1)]?, decide (8 < 3+4)) = (none, some 30, false) := by decide +kernel

-- ir_lookup_5_4_900
example : (sptAListLookup 900 (indexList ([30, 20, 10] : List Nat) 4), ([30, 20, 10] : List Nat)[(3+4)-(900+1)]?, decide (900 < 3+4)) = (none, some 30, false) := by decide +kernel

-- ir_output_5_99
example : indexList ([30, 20, 10] : List Nat) 99 = [(101,30), (100,20), (99,10)] := by decide +kernel

-- ir_recover_5_99
example : (indexList ([30, 20, 10] : List Nat) 99).map (fun p => (p.1,p.2,([30, 20, 10] : List Nat)[3-(p.1-99+1)]?)) = [(101,30,some 30), (100,20,some 20), (99,10,some 10)] := by decide +kernel

-- ir_lookup_5_99_0
example : (sptAListLookup 0 (indexList ([30, 20, 10] : List Nat) 99), ([30, 20, 10] : List Nat)[(3+99)-(0+1)]?, decide (0 < 3+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_5_99_1
example : (sptAListLookup 1 (indexList ([30, 20, 10] : List Nat) 99), ([30, 20, 10] : List Nat)[(3+99)-(1+1)]?, decide (1 < 3+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_5_99_2
example : (sptAListLookup 2 (indexList ([30, 20, 10] : List Nat) 99), ([30, 20, 10] : List Nat)[(3+99)-(2+1)]?, decide (2 < 3+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_5_99_98
example : (sptAListLookup 98 (indexList ([30, 20, 10] : List Nat) 99), ([30, 20, 10] : List Nat)[(3+99)-(98+1)]?, decide (98 < 3+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_5_99_99
example : (sptAListLookup 99 (indexList ([30, 20, 10] : List Nat) 99), ([30, 20, 10] : List Nat)[(3+99)-(99+1)]?, decide (99 < 3+99)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_5_99_101
example : (sptAListLookup 101 (indexList ([30, 20, 10] : List Nat) 99), ([30, 20, 10] : List Nat)[(3+99)-(101+1)]?, decide (101 < 3+99)) = (some 30, some 30, true) := by decide +kernel

-- ir_lookup_5_99_102
example : (sptAListLookup 102 (indexList ([30, 20, 10] : List Nat) 99), ([30, 20, 10] : List Nat)[(3+99)-(102+1)]?, decide (102 < 3+99)) = (none, some 30, false) := by decide +kernel

-- ir_lookup_5_99_103
example : (sptAListLookup 103 (indexList ([30, 20, 10] : List Nat) 99), ([30, 20, 10] : List Nat)[(3+99)-(103+1)]?, decide (103 < 3+99)) = (none, some 30, false) := by decide +kernel

-- ir_lookup_5_99_900
example : (sptAListLookup 900 (indexList ([30, 20, 10] : List Nat) 99), ([30, 20, 10] : List Nat)[(3+99)-(900+1)]?, decide (900 < 3+99)) = (none, some 30, false) := by decide +kernel

-- ir_output_6_0
example : indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 0 = [(11,0), (10,1), (9,2), (8,3), (7,4), (6,5), (5,6), (4,7), (3,8), (2,9), (1,10), (0,11)] := by decide +kernel

-- ir_recover_6_0
example : (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 0).map (fun p => (p.1,p.2,([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[12-(p.1-0+1)]?)) = [(11,0,some 0), (10,1,some 1), (9,2,some 2), (8,3,some 3), (7,4,some 4), (6,5,some 5), (5,6,some 6), (4,7,some 7), (3,8,some 8), (2,9,some 9), (1,10,some 10), (0,11,some 11)] := by decide +kernel

-- ir_lookup_6_0_0
example : (sptAListLookup 0 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 0), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+0)-(0+1)]?, decide (0 < 12+0)) = (some 11, some 11, true) := by decide +kernel

-- ir_lookup_6_0_1
example : (sptAListLookup 1 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 0), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+0)-(1+1)]?, decide (1 < 12+0)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_6_0_2
example : (sptAListLookup 2 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 0), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+0)-(2+1)]?, decide (2 < 12+0)) = (some 9, some 9, true) := by decide +kernel

-- ir_lookup_6_0_11
example : (sptAListLookup 11 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 0), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+0)-(11+1)]?, decide (11 < 12+0)) = (some 0, some 0, true) := by decide +kernel

-- ir_lookup_6_0_12
example : (sptAListLookup 12 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 0), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+0)-(12+1)]?, decide (12 < 12+0)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_6_0_13
example : (sptAListLookup 13 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 0), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+0)-(13+1)]?, decide (13 < 12+0)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_6_0_900
example : (sptAListLookup 900 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 0), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+0)-(900+1)]?, decide (900 < 12+0)) = (none, some 0, false) := by decide +kernel

-- ir_output_6_1
example : indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 1 = [(12,0), (11,1), (10,2), (9,3), (8,4), (7,5), (6,6), (5,7), (4,8), (3,9), (2,10), (1,11)] := by decide +kernel

-- ir_recover_6_1
example : (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 1).map (fun p => (p.1,p.2,([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[12-(p.1-1+1)]?)) = [(12,0,some 0), (11,1,some 1), (10,2,some 2), (9,3,some 3), (8,4,some 4), (7,5,some 5), (6,6,some 6), (5,7,some 7), (4,8,some 8), (3,9,some 9), (2,10,some 10), (1,11,some 11)] := by decide +kernel

-- ir_lookup_6_1_0
example : (sptAListLookup 0 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 1), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+1)-(0+1)]?, decide (0 < 12+1)) = (none, none, true) := by decide +kernel

-- ir_lookup_6_1_1
example : (sptAListLookup 1 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 1), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+1)-(1+1)]?, decide (1 < 12+1)) = (some 11, some 11, true) := by decide +kernel

-- ir_lookup_6_1_2
example : (sptAListLookup 2 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 1), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+1)-(2+1)]?, decide (2 < 12+1)) = (some 10, some 10, true) := by decide +kernel

-- ir_lookup_6_1_12
example : (sptAListLookup 12 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 1), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+1)-(12+1)]?, decide (12 < 12+1)) = (some 0, some 0, true) := by decide +kernel

-- ir_lookup_6_1_13
example : (sptAListLookup 13 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 1), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+1)-(13+1)]?, decide (13 < 12+1)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_6_1_14
example : (sptAListLookup 14 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 1), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+1)-(14+1)]?, decide (14 < 12+1)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_6_1_900
example : (sptAListLookup 900 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 1), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+1)-(900+1)]?, decide (900 < 12+1)) = (none, some 0, false) := by decide +kernel

-- ir_output_6_4
example : indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4 = [(15,0), (14,1), (13,2), (12,3), (11,4), (10,5), (9,6), (8,7), (7,8), (6,9), (5,10), (4,11)] := by decide +kernel

-- ir_recover_6_4
example : (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4).map (fun p => (p.1,p.2,([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[12-(p.1-4+1)]?)) = [(15,0,some 0), (14,1,some 1), (13,2,some 2), (12,3,some 3), (11,4,some 4), (10,5,some 5), (9,6,some 6), (8,7,some 7), (7,8,some 8), (6,9,some 9), (5,10,some 10), (4,11,some 11)] := by decide +kernel

-- ir_lookup_6_4_0
example : (sptAListLookup 0 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+4)-(0+1)]?, decide (0 < 12+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_6_4_1
example : (sptAListLookup 1 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+4)-(1+1)]?, decide (1 < 12+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_6_4_2
example : (sptAListLookup 2 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+4)-(2+1)]?, decide (2 < 12+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_6_4_3
example : (sptAListLookup 3 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+4)-(3+1)]?, decide (3 < 12+4)) = (none, none, true) := by decide +kernel

-- ir_lookup_6_4_4
example : (sptAListLookup 4 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+4)-(4+1)]?, decide (4 < 12+4)) = (some 11, some 11, true) := by decide +kernel

-- ir_lookup_6_4_15
example : (sptAListLookup 15 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+4)-(15+1)]?, decide (15 < 12+4)) = (some 0, some 0, true) := by decide +kernel

-- ir_lookup_6_4_16
example : (sptAListLookup 16 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+4)-(16+1)]?, decide (16 < 12+4)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_6_4_17
example : (sptAListLookup 17 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+4)-(17+1)]?, decide (17 < 12+4)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_6_4_900
example : (sptAListLookup 900 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 4), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+4)-(900+1)]?, decide (900 < 12+4)) = (none, some 0, false) := by decide +kernel

-- ir_output_6_99
example : indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99 = [(110,0), (109,1), (108,2), (107,3), (106,4), (105,5), (104,6), (103,7), (102,8), (101,9), (100,10), (99,11)] := by decide +kernel

-- ir_recover_6_99
example : (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99).map (fun p => (p.1,p.2,([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[12-(p.1-99+1)]?)) = [(110,0,some 0), (109,1,some 1), (108,2,some 2), (107,3,some 3), (106,4,some 4), (105,5,some 5), (104,6,some 6), (103,7,some 7), (102,8,some 8), (101,9,some 9), (100,10,some 10), (99,11,some 11)] := by decide +kernel

-- ir_lookup_6_99_0
example : (sptAListLookup 0 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+99)-(0+1)]?, decide (0 < 12+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_6_99_1
example : (sptAListLookup 1 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+99)-(1+1)]?, decide (1 < 12+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_6_99_2
example : (sptAListLookup 2 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+99)-(2+1)]?, decide (2 < 12+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_6_99_98
example : (sptAListLookup 98 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+99)-(98+1)]?, decide (98 < 12+99)) = (none, none, true) := by decide +kernel

-- ir_lookup_6_99_99
example : (sptAListLookup 99 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+99)-(99+1)]?, decide (99 < 12+99)) = (some 11, some 11, true) := by decide +kernel

-- ir_lookup_6_99_110
example : (sptAListLookup 110 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+99)-(110+1)]?, decide (110 < 12+99)) = (some 0, some 0, true) := by decide +kernel

-- ir_lookup_6_99_111
example : (sptAListLookup 111 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+99)-(111+1)]?, decide (111 < 12+99)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_6_99_112
example : (sptAListLookup 112 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+99)-(112+1)]?, decide (112 < 12+99)) = (none, some 0, false) := by decide +kernel

-- ir_lookup_6_99_900
example : (sptAListLookup 900 (indexList ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat) 99), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)[(12+99)-(900+1)]?, decide (900 < 12+99)) = (none, some 0, false) := by decide +kernel

