import Flapjack.Compiler.Backend.WordToStack.Proofs.ALookupMap
open Flapjack Flapjack.WordAlloc Flapjack.WordToStackProofs
-- am_any_nat_0_0_0
example : (keyLookup ([]:List (Nat × Nat)) 0, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 0), (keyLookup ([]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 0)), ([0]:List Nat).all (fun p => ([0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_0_0
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 0), keyLookup (([]:List Nat).map (fun p => (p,p))) 0, ([0]:List Nat).all (fun p => ([0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_0_1
example : (keyLookup ([]:List (Nat × Nat)) 0, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 0), (keyLookup ([]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 0)), ([0]:List Nat).all (fun p => ([0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_0_1
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 0), keyLookup (([]:List Nat).map (fun p => (p,p))) 0, ([0]:List Nat).all (fun p => ([0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_0_2
example : (keyLookup ([]:List (Nat × Nat)) 0, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 0), (keyLookup ([]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 0)), ([0]:List Nat).all (fun p => ([0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_0_2
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 0), keyLookup (([]:List Nat).map (fun p => (p,p))) 0, ([0]:List Nat).all (fun p => ([0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_0_0
example : keyLookup (([]:List Nat).map (fun p => (p,p))) 0 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_0_1_0
example : (keyLookup ([]:List (Nat × Nat)) 1, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1), (keyLookup ([]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1)), ([1]:List Nat).all (fun p => ([1]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_1_0
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1), keyLookup (([]:List Nat).map (fun p => (p,p))) 1, ([1]:List Nat).all (fun p => ([1]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_1_1
example : (keyLookup ([]:List (Nat × Nat)) 1, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1), (keyLookup ([]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1)), ([1]:List Nat).all (fun p => ([1]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_1_1
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1), keyLookup (([]:List Nat).map (fun p => (p,p))) 1, ([1]:List Nat).all (fun p => ([1]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_1_2
example : (keyLookup ([]:List (Nat × Nat)) 1, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1), (keyLookup ([]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1)), ([1]:List Nat).all (fun p => ([1]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_1_2
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1), keyLookup (([]:List Nat).map (fun p => (p,p))) 1, ([1]:List Nat).all (fun p => ([1]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_0_1
example : keyLookup (([]:List Nat).map (fun p => (p,p))) 1 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_0_2_0
example : (keyLookup ([]:List (Nat × Nat)) 2, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 2), (keyLookup ([]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 2)), ([2]:List Nat).all (fun p => ([2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_2_0
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 2), keyLookup (([]:List Nat).map (fun p => (p,p))) 2, ([2]:List Nat).all (fun p => ([2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_2_1
example : (keyLookup ([]:List (Nat × Nat)) 2, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 2), (keyLookup ([]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 2)), ([2]:List Nat).all (fun p => ([2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_2_1
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 2), keyLookup (([]:List Nat).map (fun p => (p,p))) 2, ([2]:List Nat).all (fun p => ([2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_2_2
example : (keyLookup ([]:List (Nat × Nat)) 2, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 2), (keyLookup ([]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 2)), ([2]:List Nat).all (fun p => ([2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_2_2
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 2), keyLookup (([]:List Nat).map (fun p => (p,p))) 2, ([2]:List Nat).all (fun p => ([2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_0_2
example : keyLookup (([]:List Nat).map (fun p => (p,p))) 2 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_0_3_0
example : (keyLookup ([]:List (Nat × Nat)) 5, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 5), (keyLookup ([]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 5)), ([5]:List Nat).all (fun p => ([5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_3_0
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 5), keyLookup (([]:List Nat).map (fun p => (p,p))) 5, ([5]:List Nat).all (fun p => ([5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_3_1
example : (keyLookup ([]:List (Nat × Nat)) 5, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 5), (keyLookup ([]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 5)), ([5]:List Nat).all (fun p => ([5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_3_1
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 5), keyLookup (([]:List Nat).map (fun p => (p,p))) 5, ([5]:List Nat).all (fun p => ([5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_3_2
example : (keyLookup ([]:List (Nat × Nat)) 5, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 5), (keyLookup ([]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 5)), ([5]:List Nat).all (fun p => ([5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_3_2
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 5), keyLookup (([]:List Nat).map (fun p => (p,p))) 5, ([5]:List Nat).all (fun p => ([5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_0_3
example : keyLookup (([]:List Nat).map (fun p => (p,p))) 5 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_0_4_0
example : (keyLookup ([]:List (Nat × Nat)) 9, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 9), (keyLookup ([]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 9)), ([9]:List Nat).all (fun p => ([9]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_4_0
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 9), keyLookup (([]:List Nat).map (fun p => (p,p))) 9, ([9]:List Nat).all (fun p => ([9]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_4_1
example : (keyLookup ([]:List (Nat × Nat)) 9, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 9), (keyLookup ([]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 9)), ([9]:List Nat).all (fun p => ([9]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_4_1
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 9), keyLookup (([]:List Nat).map (fun p => (p,p))) 9, ([9]:List Nat).all (fun p => ([9]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_4_2
example : (keyLookup ([]:List (Nat × Nat)) 9, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 9), (keyLookup ([]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 9)), ([9]:List Nat).all (fun p => ([9]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_4_2
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 9), keyLookup (([]:List Nat).map (fun p => (p,p))) 9, ([9]:List Nat).all (fun p => ([9]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_0_4
example : keyLookup (([]:List Nat).map (fun p => (p,p))) 9 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_0_5_0
example : (keyLookup ([]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1180591620717411303424), (keyLookup ([]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1180591620717411303424)), ([1180591620717411303424]:List Nat).all (fun p => ([1180591620717411303424]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_5_0
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1180591620717411303424), keyLookup (([]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424]:List Nat).all (fun p => ([1180591620717411303424]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_5_1
example : (keyLookup ([]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1180591620717411303424), (keyLookup ([]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1180591620717411303424)), ([1180591620717411303424]:List Nat).all (fun p => ([1180591620717411303424]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_5_1
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1180591620717411303424), keyLookup (([]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424]:List Nat).all (fun p => ([1180591620717411303424]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_0_5_2
example : (keyLookup ([]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1180591620717411303424), (keyLookup ([]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1180591620717411303424)), ([1180591620717411303424]:List Nat).all (fun p => ([1180591620717411303424]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_0_5_2
example : (keyLookup (([]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1180591620717411303424), keyLookup (([]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424]:List Nat).all (fun p => ([1180591620717411303424]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_0_5
example : keyLookup (([]:List Nat).map (fun p => (p,p))) 1180591620717411303424 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_1_0_0
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 0, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 0), (keyLookup ([(0,7)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 0)), ([0,0]:List Nat).all (fun p => ([0,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 7, some 14, some 14, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_0_0
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 0), keyLookup (([0]:List Nat).map (fun p => (p,p))) 0, ([0,0]:List Nat).all (fun p => ([0,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 0, some 0, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_0_1
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 0, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 0), (keyLookup ([(0,7)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 0)), ([0,0]:List Nat).all (fun p => ([0,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 7, some 17, some 17, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_0_1
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 0), keyLookup (([0]:List Nat).map (fun p => (p,p))) 0, ([0,0]:List Nat).all (fun p => ([0,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 0, some 0, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_0_2
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 0, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 0), (keyLookup ([(0,7)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 0)), ([0,0]:List Nat).all (fun p => ([0,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 7, some 14, some 14, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_0_2
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 0), keyLookup (([0]:List Nat).map (fun p => (p,p))) 0, ([0,0]:List Nat).all (fun p => ([0,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 0, some 0, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_1_0
example : keyLookup (([0]:List Nat).map (fun p => (p,p))) 0 = some 0 := by simp [keyLookup, holAlookup]

-- am_any_nat_1_1_0
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 1, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1), (keyLookup ([(0,7)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1)), ([1,0]:List Nat).all (fun p => ([1,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_1_0
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1), keyLookup (([0]:List Nat).map (fun p => (p,p))) 1, ([1,0]:List Nat).all (fun p => ([1,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_1_1
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 1, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1), (keyLookup ([(0,7)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1)), ([1,0]:List Nat).all (fun p => ([1,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_1_1
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1), keyLookup (([0]:List Nat).map (fun p => (p,p))) 1, ([1,0]:List Nat).all (fun p => ([1,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_1_2
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 1, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1), (keyLookup ([(0,7)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1)), ([1,0]:List Nat).all (fun p => ([1,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_1_2
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1), keyLookup (([0]:List Nat).map (fun p => (p,p))) 1, ([1,0]:List Nat).all (fun p => ([1,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_1_1
example : keyLookup (([0]:List Nat).map (fun p => (p,p))) 1 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_1_2_0
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 2, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 2), (keyLookup ([(0,7)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 2)), ([2,0]:List Nat).all (fun p => ([2,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_2_0
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 2), keyLookup (([0]:List Nat).map (fun p => (p,p))) 2, ([2,0]:List Nat).all (fun p => ([2,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_2_1
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 2, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 2), (keyLookup ([(0,7)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 2)), ([2,0]:List Nat).all (fun p => ([2,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_2_1
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 2), keyLookup (([0]:List Nat).map (fun p => (p,p))) 2, ([2,0]:List Nat).all (fun p => ([2,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_2_2
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 2, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 2), (keyLookup ([(0,7)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 2)), ([2,0]:List Nat).all (fun p => ([2,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_2_2
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 2), keyLookup (([0]:List Nat).map (fun p => (p,p))) 2, ([2,0]:List Nat).all (fun p => ([2,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_1_2
example : keyLookup (([0]:List Nat).map (fun p => (p,p))) 2 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_1_3_0
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 5, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 5), (keyLookup ([(0,7)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 5)), ([5,0]:List Nat).all (fun p => ([5,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_3_0
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 5), keyLookup (([0]:List Nat).map (fun p => (p,p))) 5, ([5,0]:List Nat).all (fun p => ([5,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_3_1
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 5, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 5), (keyLookup ([(0,7)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 5)), ([5,0]:List Nat).all (fun p => ([5,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_3_1
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 5), keyLookup (([0]:List Nat).map (fun p => (p,p))) 5, ([5,0]:List Nat).all (fun p => ([5,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_3_2
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 5, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 5), (keyLookup ([(0,7)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 5)), ([5,0]:List Nat).all (fun p => ([5,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_3_2
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 5), keyLookup (([0]:List Nat).map (fun p => (p,p))) 5, ([5,0]:List Nat).all (fun p => ([5,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_1_3
example : keyLookup (([0]:List Nat).map (fun p => (p,p))) 5 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_1_4_0
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 9, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 9), (keyLookup ([(0,7)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 9)), ([9,0]:List Nat).all (fun p => ([9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_4_0
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 9), keyLookup (([0]:List Nat).map (fun p => (p,p))) 9, ([9,0]:List Nat).all (fun p => ([9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_4_1
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 9, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 9), (keyLookup ([(0,7)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 9)), ([9,0]:List Nat).all (fun p => ([9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_4_1
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 9), keyLookup (([0]:List Nat).map (fun p => (p,p))) 9, ([9,0]:List Nat).all (fun p => ([9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_4_2
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 9, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 9), (keyLookup ([(0,7)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 9)), ([9,0]:List Nat).all (fun p => ([9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_4_2
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 9), keyLookup (([0]:List Nat).map (fun p => (p,p))) 9, ([9,0]:List Nat).all (fun p => ([9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_1_4
example : keyLookup (([0]:List Nat).map (fun p => (p,p))) 9 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_1_5_0
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1180591620717411303424), (keyLookup ([(0,7)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1180591620717411303424)), ([1180591620717411303424,0]:List Nat).all (fun p => ([1180591620717411303424,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_5_0
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1180591620717411303424), keyLookup (([0]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,0]:List Nat).all (fun p => ([1180591620717411303424,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_5_1
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1180591620717411303424), (keyLookup ([(0,7)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1180591620717411303424)), ([1180591620717411303424,0]:List Nat).all (fun p => ([1180591620717411303424,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_5_1
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1180591620717411303424), keyLookup (([0]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,0]:List Nat).all (fun p => ([1180591620717411303424,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_1_5_2
example : (keyLookup ([(0,7)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(0,7)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1180591620717411303424), (keyLookup ([(0,7)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1180591620717411303424)), ([1180591620717411303424,0]:List Nat).all (fun p => ([1180591620717411303424,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, some 14, none, false) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_1_5_2
example : (keyLookup (([0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1180591620717411303424), keyLookup (([0]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,0]:List Nat).all (fun p => ([1180591620717411303424,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 0, none, false) := by simp [keyLookup, holAlookup]

-- am_id_nat_1_5
example : keyLookup (([0]:List Nat).map (fun p => (p,p))) 1180591620717411303424 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_2_0_0
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 0, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 0), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 0)), ([0,0,0,2]:List Nat).all (fun p => ([0,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 7, some 14, some 14, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_0_0
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 0), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 0, ([0,0,0,2]:List Nat).all (fun p => ([0,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 0, some 0, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_0_1
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 0, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 0), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 0)), ([0,0,0,2]:List Nat).all (fun p => ([0,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 7, some 17, some 17, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_0_1
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 0), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 0, ([0,0,0,2]:List Nat).all (fun p => ([0,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 0, some 0, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_0_2
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 0, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 0), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 0)), ([0,0,0,2]:List Nat).all (fun p => ([0,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 7, some 14, some 14, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_0_2
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 0), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 0, ([0,0,0,2]:List Nat).all (fun p => ([0,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 0, some 0, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_2_0
example : keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 0 = some 0 := by simp [keyLookup, holAlookup]

-- am_any_nat_2_1_0
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1)), ([1,0,0,2]:List Nat).all (fun p => ([1,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_1_0
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 1, ([1,0,0,2]:List Nat).all (fun p => ([1,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_1_1
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1)), ([1,0,0,2]:List Nat).all (fun p => ([1,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_1_1
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 1, ([1,0,0,2]:List Nat).all (fun p => ([1,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_1_2
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1)), ([1,0,0,2]:List Nat).all (fun p => ([1,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_1_2
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 1, ([1,0,0,2]:List Nat).all (fun p => ([1,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_2_1
example : keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 1 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_2_2_0
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 2, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 2), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 2)), ([2,0,0,2]:List Nat).all (fun p => ([2,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 11, some 24, some 24, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_2_0
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 2), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 2, ([2,0,0,2]:List Nat).all (fun p => ([2,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_2_1
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 2, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 2), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 2)), ([2,0,0,2]:List Nat).all (fun p => ([2,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 11, some 27, some 27, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_2_1
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 2), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 2, ([2,0,0,2]:List Nat).all (fun p => ([2,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_2_2
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 2, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 2), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 2)), ([2,0,0,2]:List Nat).all (fun p => ([2,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 11, some 24, some 24, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_2_2
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 2), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 2, ([2,0,0,2]:List Nat).all (fun p => ([2,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_2_2
example : keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 2 = some 2 := by simp [keyLookup, holAlookup]

-- am_any_nat_2_3_0
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 5, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 5), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 5)), ([5,0,0,2]:List Nat).all (fun p => ([5,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_3_0
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 5), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 5, ([5,0,0,2]:List Nat).all (fun p => ([5,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_3_1
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 5, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 5), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 5)), ([5,0,0,2]:List Nat).all (fun p => ([5,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_3_1
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 5), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 5, ([5,0,0,2]:List Nat).all (fun p => ([5,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_3_2
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 5, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 5), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 5)), ([5,0,0,2]:List Nat).all (fun p => ([5,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_3_2
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 5), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 5, ([5,0,0,2]:List Nat).all (fun p => ([5,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_2_3
example : keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 5 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_2_4_0
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 9, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 9), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 9)), ([9,0,0,2]:List Nat).all (fun p => ([9,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_4_0
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 9), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 9, ([9,0,0,2]:List Nat).all (fun p => ([9,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_4_1
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 9, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 9), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 9)), ([9,0,0,2]:List Nat).all (fun p => ([9,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_4_1
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 9), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 9, ([9,0,0,2]:List Nat).all (fun p => ([9,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_4_2
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 9, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 9), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 9)), ([9,0,0,2]:List Nat).all (fun p => ([9,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_4_2
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 9), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 9, ([9,0,0,2]:List Nat).all (fun p => ([9,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_2_4
example : keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 9 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_2_5_0
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1180591620717411303424), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1180591620717411303424)), ([1180591620717411303424,0,0,2]:List Nat).all (fun p => ([1180591620717411303424,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_5_0
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1180591620717411303424), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,0,0,2]:List Nat).all (fun p => ([1180591620717411303424,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_5_1
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1180591620717411303424), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1180591620717411303424)), ([1180591620717411303424,0,0,2]:List Nat).all (fun p => ([1180591620717411303424,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_5_1
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1180591620717411303424), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,0,0,2]:List Nat).all (fun p => ([1180591620717411303424,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_2_5_2
example : (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(0,7),(0,9),(2,11)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1180591620717411303424), (keyLookup ([(0,7),(0,9),(2,11)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1180591620717411303424)), ([1180591620717411303424,0,0,2]:List Nat).all (fun p => ([1180591620717411303424,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, some 14, none, false) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_2_5_2
example : (keyLookup (([0,0,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1180591620717411303424), keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,0,0,2]:List Nat).all (fun p => ([1180591620717411303424,0,0,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 0, none, false) := by simp [keyLookup, holAlookup]

-- am_id_nat_2_5
example : keyLookup (([0,0,2]:List Nat).map (fun p => (p,p))) 1180591620717411303424 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_3_0_0
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 0, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 0), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 0)), ([0,2,1,5]:List Nat).all (fun p => ([0,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_0_0
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 0), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 0, ([0,2,1,5]:List Nat).all (fun p => ([0,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_0_1
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 0, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 0), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 0)), ([0,2,1,5]:List Nat).all (fun p => ([0,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_0_1
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 0), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 0, ([0,2,1,5]:List Nat).all (fun p => ([0,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_0_2
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 0, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 0), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 0)), ([0,2,1,5]:List Nat).all (fun p => ([0,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_0_2
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 0), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 0, ([0,2,1,5]:List Nat).all (fun p => ([0,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_3_0
example : keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 0 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_3_1_0
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1)), ([1,2,1,5]:List Nat).all (fun p => ([1,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 9, some 19, some 19, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_1_0
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 1, ([1,2,1,5]:List Nat).all (fun p => ([1,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 1, some 1, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_1_1
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1)), ([1,2,1,5]:List Nat).all (fun p => ([1,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 9, some 22, some 22, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_1_1
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 1, ([1,2,1,5]:List Nat).all (fun p => ([1,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 1, some 1, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_1_2
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1)), ([1,2,1,5]:List Nat).all (fun p => ([1,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 9, some 19, some 19, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_1_2
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 1, ([1,2,1,5]:List Nat).all (fun p => ([1,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 1, some 1, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_3_1
example : keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 1 = some 1 := by simp [keyLookup, holAlookup]

-- am_any_nat_3_2_0
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 2, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 2), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 2)), ([2,2,1,5]:List Nat).all (fun p => ([2,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 3, some 8, some 8, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_2_0
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 2), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 2, ([2,2,1,5]:List Nat).all (fun p => ([2,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_2_1
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 2, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 2), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 2)), ([2,2,1,5]:List Nat).all (fun p => ([2,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 3, some 11, some 11, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_2_1
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 2), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 2, ([2,2,1,5]:List Nat).all (fun p => ([2,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_2_2
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 2, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 2), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 2)), ([2,2,1,5]:List Nat).all (fun p => ([2,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 3, some 8, some 8, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_2_2
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 2), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 2, ([2,2,1,5]:List Nat).all (fun p => ([2,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_3_2
example : keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 2 = some 2 := by simp [keyLookup, holAlookup]

-- am_any_nat_3_3_0
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 5, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 5), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 5)), ([5,2,1,5]:List Nat).all (fun p => ([5,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 0, some 5, some 5, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_3_0
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 5), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 5, ([5,2,1,5]:List Nat).all (fun p => ([5,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 5, some 5, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_3_1
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 5, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 5), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 5)), ([5,2,1,5]:List Nat).all (fun p => ([5,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 0, some 8, some 8, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_3_1
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 5), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 5, ([5,2,1,5]:List Nat).all (fun p => ([5,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 5, some 5, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_3_2
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 5, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 5), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 5)), ([5,2,1,5]:List Nat).all (fun p => ([5,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 0, some 5, some 5, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_3_2
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 5), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 5, ([5,2,1,5]:List Nat).all (fun p => ([5,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 5, some 5, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_3_3
example : keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 5 = some 5 := by simp [keyLookup, holAlookup]

-- am_any_nat_3_4_0
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 9, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 9), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 9)), ([9,2,1,5]:List Nat).all (fun p => ([9,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_4_0
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 9), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 9, ([9,2,1,5]:List Nat).all (fun p => ([9,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_4_1
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 9, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 9), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 9)), ([9,2,1,5]:List Nat).all (fun p => ([9,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_4_1
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 9), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 9, ([9,2,1,5]:List Nat).all (fun p => ([9,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_4_2
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 9, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 9), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 9)), ([9,2,1,5]:List Nat).all (fun p => ([9,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, some 19, none, false) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_4_2
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 9), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 9, ([9,2,1,5]:List Nat).all (fun p => ([9,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 1, none, false) := by simp [keyLookup, holAlookup]

-- am_id_nat_3_4
example : keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 9 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_3_5_0
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1180591620717411303424), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1180591620717411303424)), ([1180591620717411303424,2,1,5]:List Nat).all (fun p => ([1180591620717411303424,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_5_0
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1180591620717411303424), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,2,1,5]:List Nat).all (fun p => ([1180591620717411303424,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_5_1
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1180591620717411303424), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1180591620717411303424)), ([1180591620717411303424,2,1,5]:List Nat).all (fun p => ([1180591620717411303424,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_5_1
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1180591620717411303424), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,2,1,5]:List Nat).all (fun p => ([1180591620717411303424,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_3_5_2
example : (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(2,3),(1,9),(5,0)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1180591620717411303424), (keyLookup ([(2,3),(1,9),(5,0)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1180591620717411303424)), ([1180591620717411303424,2,1,5]:List Nat).all (fun p => ([1180591620717411303424,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_3_5_2
example : (keyLookup (([2,1,5]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1180591620717411303424), keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,2,1,5]:List Nat).all (fun p => ([1180591620717411303424,2,1,5]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_3_5
example : keyLookup (([2,1,5]:List Nat).map (fun p => (p,p))) 1180591620717411303424 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_4_0_0
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 0, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 0), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 0)), ([0,9,0]:List Nat).all (fun p => ([0,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 1, some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_0_0
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 0), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 0, ([0,9,0]:List Nat).all (fun p => ([0,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 0, some 0, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_0_1
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 0, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 0), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 0)), ([0,9,0]:List Nat).all (fun p => ([0,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 1, some 5, some 5, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_0_1
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 0), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 0, ([0,9,0]:List Nat).all (fun p => ([0,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 0, some 0, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_0_2
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 0, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 0), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 0)), ([0,9,0]:List Nat).all (fun p => ([0,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 1, some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_0_2
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 0), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 0, ([0,9,0]:List Nat).all (fun p => ([0,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 0, some 0, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_4_0
example : keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 0 = some 0 := by simp [keyLookup, holAlookup]

-- am_any_nat_4_1_0
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1)), ([1,9,0]:List Nat).all (fun p => ([1,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_1_0
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 1, ([1,9,0]:List Nat).all (fun p => ([1,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_1_1
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1)), ([1,9,0]:List Nat).all (fun p => ([1,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_1_1
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 1, ([1,9,0]:List Nat).all (fun p => ([1,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_1_2
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1)), ([1,9,0]:List Nat).all (fun p => ([1,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, some 5, none, false) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_1_2
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 1, ([1,9,0]:List Nat).all (fun p => ([1,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 9, none, false) := by simp [keyLookup, holAlookup]

-- am_id_nat_4_1
example : keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 1 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_4_2_0
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 2, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 2), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 2)), ([2,9,0]:List Nat).all (fun p => ([2,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_2_0
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 2), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 2, ([2,9,0]:List Nat).all (fun p => ([2,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_2_1
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 2, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 2), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 2)), ([2,9,0]:List Nat).all (fun p => ([2,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_2_1
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 2), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 2, ([2,9,0]:List Nat).all (fun p => ([2,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_2_2
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 2, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 2), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 2)), ([2,9,0]:List Nat).all (fun p => ([2,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_2_2
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 2), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 2, ([2,9,0]:List Nat).all (fun p => ([2,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_4_2
example : keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 2 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_4_3_0
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 5, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 5), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 5)), ([5,9,0]:List Nat).all (fun p => ([5,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_3_0
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 5), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 5, ([5,9,0]:List Nat).all (fun p => ([5,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_3_1
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 5, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 5), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 5)), ([5,9,0]:List Nat).all (fun p => ([5,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_3_1
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 5), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 5, ([5,9,0]:List Nat).all (fun p => ([5,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_3_2
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 5, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 5), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 5)), ([5,9,0]:List Nat).all (fun p => ([5,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_3_2
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 5), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 5, ([5,9,0]:List Nat).all (fun p => ([5,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_4_3
example : keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 5 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_4_4_0
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 9, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 9), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 9)), ([9,9,0]:List Nat).all (fun p => ([9,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 2, some 13, some 13, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_4_0
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 9), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 9, ([9,9,0]:List Nat).all (fun p => ([9,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 9, some 9, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_4_1
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 9, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 9), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 9)), ([9,9,0]:List Nat).all (fun p => ([9,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 2, some 16, some 16, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_4_1
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 9), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 9, ([9,9,0]:List Nat).all (fun p => ([9,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 9, some 9, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_4_2
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 9, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 9), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 9)), ([9,9,0]:List Nat).all (fun p => ([9,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 2, some 5, some 5, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_4_2
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 9), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 9, ([9,9,0]:List Nat).all (fun p => ([9,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 9, some 9, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_4_4
example : keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 9 = some 9 := by simp [keyLookup, holAlookup]

-- am_any_nat_4_5_0
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1180591620717411303424), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1180591620717411303424)), ([1180591620717411303424,9,0]:List Nat).all (fun p => ([1180591620717411303424,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_5_0
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1180591620717411303424), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,9,0]:List Nat).all (fun p => ([1180591620717411303424,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_5_1
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1180591620717411303424), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1180591620717411303424)), ([1180591620717411303424,9,0]:List Nat).all (fun p => ([1180591620717411303424,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_5_1
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1180591620717411303424), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,9,0]:List Nat).all (fun p => ([1180591620717411303424,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_4_5_2
example : (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(9,2),(0,1)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1180591620717411303424), (keyLookup ([(9,2),(0,1)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1180591620717411303424)), ([1180591620717411303424,9,0]:List Nat).all (fun p => ([1180591620717411303424,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, some 2, none, false) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_4_5_2
example : (keyLookup (([9,0]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1180591620717411303424), keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,9,0]:List Nat).all (fun p => ([1180591620717411303424,9,0]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 0, none, false) := by simp [keyLookup, holAlookup]

-- am_id_nat_4_5
example : keyLookup (([9,0]:List Nat).map (fun p => (p,p))) 1180591620717411303424 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_5_0_0
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 0, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 0), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 0)), ([0,1180591620717411303424,2]:List Nat).all (fun p => ([0,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_0_0
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 0), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 0, ([0,1180591620717411303424,2]:List Nat).all (fun p => ([0,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_0_1
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 0, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 0), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 0)), ([0,1180591620717411303424,2]:List Nat).all (fun p => ([0,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_0_1
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 0), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 0, ([0,1180591620717411303424,2]:List Nat).all (fun p => ([0,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_0_2
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 0, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 0), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 0).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 0)), ([0,1180591620717411303424,2]:List Nat).all (fun p => ([0,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, some 2361183241434822606854, none, false) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_0_2
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 0), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 0, ([0,1180591620717411303424,2]:List Nat).all (fun p => ([0,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 1180591620717411303424, none, false) := by simp [keyLookup, holAlookup]

-- am_id_nat_5_0
example : keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 0 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_5_1_0
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1)), ([1,1180591620717411303424,2]:List Nat).all (fun p => ([1,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_1_0
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 1, ([1,1180591620717411303424,2]:List Nat).all (fun p => ([1,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_1_1
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1)), ([1,1180591620717411303424,2]:List Nat).all (fun p => ([1,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_1_1
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 1, ([1,1180591620717411303424,2]:List Nat).all (fun p => ([1,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_1_2
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1)), ([1,1180591620717411303424,2]:List Nat).all (fun p => ([1,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_1_2
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 1, ([1,1180591620717411303424,2]:List Nat).all (fun p => ([1,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_5_1
example : keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 1 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_5_2_0
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 2, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 2), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 2)), ([2,1180591620717411303424,2]:List Nat).all (fun p => ([2,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 17, some 36, some 36, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_2_0
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 2), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 2, ([2,1180591620717411303424,2]:List Nat).all (fun p => ([2,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_2_1
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 2, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 2), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 2)), ([2,1180591620717411303424,2]:List Nat).all (fun p => ([2,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 17, some 39, some 39, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_2_1
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 2), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 2, ([2,1180591620717411303424,2]:List Nat).all (fun p => ([2,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_2_2
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 2, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 2), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 2).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 2)), ([2,1180591620717411303424,2]:List Nat).all (fun p => ([2,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 17, some 36, some 36, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_2_2
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 2), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 2, ([2,1180591620717411303424,2]:List Nat).all (fun p => ([2,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 2, some 2, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_5_2
example : keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 2 = some 2 := by simp [keyLookup, holAlookup]

-- am_any_nat_5_3_0
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 5, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 5), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 5)), ([5,1180591620717411303424,2]:List Nat).all (fun p => ([5,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_3_0
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 5), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 5, ([5,1180591620717411303424,2]:List Nat).all (fun p => ([5,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_3_1
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 5, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 5), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 5)), ([5,1180591620717411303424,2]:List Nat).all (fun p => ([5,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_3_1
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 5), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 5, ([5,1180591620717411303424,2]:List Nat).all (fun p => ([5,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_3_2
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 5, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 5), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 5).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 5)), ([5,1180591620717411303424,2]:List Nat).all (fun p => ([5,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_3_2
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 5), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 5, ([5,1180591620717411303424,2]:List Nat).all (fun p => ([5,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_5_3
example : keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 5 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_5_4_0
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 9, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 9), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 9)), ([9,1180591620717411303424,2]:List Nat).all (fun p => ([9,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_4_0
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 9), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 9, ([9,1180591620717411303424,2]:List Nat).all (fun p => ([9,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_4_1
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 9, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 9), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 9)), ([9,1180591620717411303424,2]:List Nat).all (fun p => ([9,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_4_1
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 9), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 9, ([9,1180591620717411303424,2]:List Nat).all (fun p => ([9,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_4_2
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 9, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 9), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 9).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 9)), ([9,1180591620717411303424,2]:List Nat).all (fun p => ([9,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_4_2
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 9), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 9, ([9,1180591620717411303424,2]:List Nat).all (fun p => ([9,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_5_4
example : keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 9 = none := by simp [keyLookup, holAlookup]

-- am_any_nat_5_5_0
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) p.1) p.2))) ((fun x:Nat => x) 1180591620717411303424), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x) 1180591620717411303424)), ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun p => ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 1180591620717411303427, some 3541774862152233910278, some 3541774862152233910278, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_5_0
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x) p,p))) ((fun x:Nat => x) 1180591620717411303424), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun p => ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x) p = (fun x:Nat => x) q → p=q)))) = (some 1180591620717411303424, some 1180591620717411303424, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_5_1
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x+3) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) p.1) p.2))) ((fun x:Nat => x+3) 1180591620717411303424), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x+3) 1180591620717411303424)), ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun p => ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 1180591620717411303427, some 3541774862152233910281, some 3541774862152233910281, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_5_1
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x+3) p,p))) ((fun x:Nat => x+3) 1180591620717411303424), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun p => ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x+3) p = (fun x:Nat => x+3) q → p=q)))) = (some 1180591620717411303424, some 1180591620717411303424, true) := by simp [keyLookup, holAlookup]

-- am_any_nat_5_5_2
example : (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1180591620717411303424, keyLookup (([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)).map (fun p:Nat × Nat => ((fun x:Nat => x%8) p.1, (fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) p.1) p.2))) ((fun x:Nat => x%8) 1180591620717411303424), (keyLookup ([(1180591620717411303424,1180591620717411303427),(2,17)]:List (Nat × Nat)) 1180591620717411303424).map ((fun k:Nat => fun y:Nat => k+2*y) ((fun x:Nat => x%8) 1180591620717411303424)), ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun p => ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 1180591620717411303427, some 2361183241434822606854, some 2361183241434822606854, true) := by simp [keyLookup, holAlookup]

-- am_injfst_nat_5_5_2
example : (keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => ((fun x:Nat => x%8) p,p))) ((fun x:Nat => x%8) 1180591620717411303424), keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 1180591620717411303424, ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun p => ([1180591620717411303424,1180591620717411303424,2]:List Nat).all (fun q => decide ((fun x:Nat => x%8) p = (fun x:Nat => x%8) q → p=q)))) = (some 1180591620717411303424, some 1180591620717411303424, true) := by simp [keyLookup, holAlookup]

-- am_id_nat_5_5
example : keyLookup (([1180591620717411303424,2]:List Nat).map (fun p => (p,p))) 1180591620717411303424 = some 1180591620717411303424 := by simp [keyLookup, holAlookup]

-- am_any_bool_0_0_0
example : (keyLookup ([]:List (Bool × Nat)) false, keyLookup (([]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) false), (keyLookup ([]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) false)), ([false]:List Bool).all (fun p => ([false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_0_0_0
example : (keyLookup (([]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) false), keyLookup (([]:List Bool).map (fun p => (p,p))) false, ([false]:List Bool).all (fun p => ([false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_0_0_1
example : (keyLookup ([]:List (Bool × Nat)) false, keyLookup (([]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) false), (keyLookup ([]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) false)), ([false]:List Bool).all (fun p => ([false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_0_0_1
example : (keyLookup (([]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) false), keyLookup (([]:List Bool).map (fun p => (p,p))) false, ([false]:List Bool).all (fun p => ([false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_bool_0_0
example : keyLookup (([]:List Bool).map (fun p => (p,p))) false = none := by simp [keyLookup, holAlookup]

-- am_any_bool_0_1_0
example : (keyLookup ([]:List (Bool × Nat)) true, keyLookup (([]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) true), (keyLookup ([]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) true)), ([true]:List Bool).all (fun p => ([true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_0_1_0
example : (keyLookup (([]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) true), keyLookup (([]:List Bool).map (fun p => (p,p))) true, ([true]:List Bool).all (fun p => ([true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_0_1_1
example : (keyLookup ([]:List (Bool × Nat)) true, keyLookup (([]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) true), (keyLookup ([]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) true)), ([true]:List Bool).all (fun p => ([true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_0_1_1
example : (keyLookup (([]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) true), keyLookup (([]:List Bool).map (fun p => (p,p))) true, ([true]:List Bool).all (fun p => ([true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_id_bool_0_1
example : keyLookup (([]:List Bool).map (fun p => (p,p))) true = none := by simp [keyLookup, holAlookup]

-- am_any_bool_1_0_0
example : (keyLookup ([(false,7)]:List (Bool × Nat)) false, keyLookup (([(false,7)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) false), (keyLookup ([(false,7)]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) false)), ([false,false]:List Bool).all (fun p => ([false,false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some 7, some false, some false, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_1_0_0
example : (keyLookup (([false]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) false), keyLookup (([false]:List Bool).map (fun p => (p,p))) false, ([false,false]:List Bool).all (fun p => ([false,false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some false, some false, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_1_0_1
example : (keyLookup ([(false,7)]:List (Bool × Nat)) false, keyLookup (([(false,7)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) false), (keyLookup ([(false,7)]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) false)), ([false,false]:List Bool).all (fun p => ([false,false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some 7, some false, some false, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_1_0_1
example : (keyLookup (([false]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) false), keyLookup (([false]:List Bool).map (fun p => (p,p))) false, ([false,false]:List Bool).all (fun p => ([false,false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some false, some false, true) := by simp [keyLookup, holAlookup]

-- am_id_bool_1_0
example : keyLookup (([false]:List Bool).map (fun p => (p,p))) false = some false := by simp [keyLookup, holAlookup]

-- am_any_bool_1_1_0
example : (keyLookup ([(false,7)]:List (Bool × Nat)) true, keyLookup (([(false,7)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) true), (keyLookup ([(false,7)]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) true)), ([true,false]:List Bool).all (fun p => ([true,false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_1_1_0
example : (keyLookup (([false]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) true), keyLookup (([false]:List Bool).map (fun p => (p,p))) true, ([true,false]:List Bool).all (fun p => ([true,false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_1_1_1
example : (keyLookup ([(false,7)]:List (Bool × Nat)) true, keyLookup (([(false,7)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) true), (keyLookup ([(false,7)]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) true)), ([true,false]:List Bool).all (fun p => ([true,false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (none, some false, none, false) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_1_1_1
example : (keyLookup (([false]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) true), keyLookup (([false]:List Bool).map (fun p => (p,p))) true, ([true,false]:List Bool).all (fun p => ([true,false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some false, none, false) := by simp [keyLookup, holAlookup]

-- am_id_bool_1_1
example : keyLookup (([false]:List Bool).map (fun p => (p,p))) true = none := by simp [keyLookup, holAlookup]

-- am_any_bool_2_0_0
example : (keyLookup ([(true,9)]:List (Bool × Nat)) false, keyLookup (([(true,9)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) false), (keyLookup ([(true,9)]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) false)), ([false,true]:List Bool).all (fun p => ([false,true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (none, none, none, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_2_0_0
example : (keyLookup (([true]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) false), keyLookup (([true]:List Bool).map (fun p => (p,p))) false, ([false,true]:List Bool).all (fun p => ([false,true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (none, none, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_2_0_1
example : (keyLookup ([(true,9)]:List (Bool × Nat)) false, keyLookup (([(true,9)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) false), (keyLookup ([(true,9)]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) false)), ([false,true]:List Bool).all (fun p => ([false,true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (none, some false, none, false) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_2_0_1
example : (keyLookup (([true]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) false), keyLookup (([true]:List Bool).map (fun p => (p,p))) false, ([false,true]:List Bool).all (fun p => ([false,true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some true, none, false) := by simp [keyLookup, holAlookup]

-- am_id_bool_2_0
example : keyLookup (([true]:List Bool).map (fun p => (p,p))) false = none := by simp [keyLookup, holAlookup]

-- am_any_bool_2_1_0
example : (keyLookup ([(true,9)]:List (Bool × Nat)) true, keyLookup (([(true,9)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) true), (keyLookup ([(true,9)]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) true)), ([true,true]:List Bool).all (fun p => ([true,true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some 9, some true, some true, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_2_1_0
example : (keyLookup (([true]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) true), keyLookup (([true]:List Bool).map (fun p => (p,p))) true, ([true,true]:List Bool).all (fun p => ([true,true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some true, some true, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_2_1_1
example : (keyLookup ([(true,9)]:List (Bool × Nat)) true, keyLookup (([(true,9)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) true), (keyLookup ([(true,9)]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) true)), ([true,true]:List Bool).all (fun p => ([true,true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some 9, some false, some false, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_2_1_1
example : (keyLookup (([true]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) true), keyLookup (([true]:List Bool).map (fun p => (p,p))) true, ([true,true]:List Bool).all (fun p => ([true,true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some true, some true, true) := by simp [keyLookup, holAlookup]

-- am_id_bool_2_1
example : keyLookup (([true]:List Bool).map (fun p => (p,p))) true = some true := by simp [keyLookup, holAlookup]

-- am_any_bool_3_0_0
example : (keyLookup ([(true,3),(false,2)]:List (Bool × Nat)) false, keyLookup (([(true,3),(false,2)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) false), (keyLookup ([(true,3),(false,2)]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) false)), ([false,true,false]:List Bool).all (fun p => ([false,true,false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some 2, some true, some true, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_3_0_0
example : (keyLookup (([true,false]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) false), keyLookup (([true,false]:List Bool).map (fun p => (p,p))) false, ([false,true,false]:List Bool).all (fun p => ([false,true,false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some false, some false, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_3_0_1
example : (keyLookup ([(true,3),(false,2)]:List (Bool × Nat)) false, keyLookup (([(true,3),(false,2)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) false), (keyLookup ([(true,3),(false,2)]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) false)), ([false,true,false]:List Bool).all (fun p => ([false,true,false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some 2, some false, some true, false) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_3_0_1
example : (keyLookup (([true,false]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) false), keyLookup (([true,false]:List Bool).map (fun p => (p,p))) false, ([false,true,false]:List Bool).all (fun p => ([false,true,false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some true, some false, false) := by simp [keyLookup, holAlookup]

-- am_id_bool_3_0
example : keyLookup (([true,false]:List Bool).map (fun p => (p,p))) false = some false := by simp [keyLookup, holAlookup]

-- am_any_bool_3_1_0
example : (keyLookup ([(true,3),(false,2)]:List (Bool × Nat)) true, keyLookup (([(true,3),(false,2)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) true), (keyLookup ([(true,3),(false,2)]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) true)), ([true,true,false]:List Bool).all (fun p => ([true,true,false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some 3, some true, some true, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_3_1_0
example : (keyLookup (([true,false]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) true), keyLookup (([true,false]:List Bool).map (fun p => (p,p))) true, ([true,true,false]:List Bool).all (fun p => ([true,true,false]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some true, some true, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_3_1_1
example : (keyLookup ([(true,3),(false,2)]:List (Bool × Nat)) true, keyLookup (([(true,3),(false,2)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) true), (keyLookup ([(true,3),(false,2)]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) true)), ([true,true,false]:List Bool).all (fun p => ([true,true,false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some 3, some false, some false, false) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_3_1_1
example : (keyLookup (([true,false]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) true), keyLookup (([true,false]:List Bool).map (fun p => (p,p))) true, ([true,true,false]:List Bool).all (fun p => ([true,true,false]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some true, some true, false) := by simp [keyLookup, holAlookup]

-- am_id_bool_3_1
example : keyLookup (([true,false]:List Bool).map (fun p => (p,p))) true = some true := by simp [keyLookup, holAlookup]

-- am_any_bool_4_0_0
example : (keyLookup ([(false,5),(false,9),(true,1)]:List (Bool × Nat)) false, keyLookup (([(false,5),(false,9),(true,1)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) false), (keyLookup ([(false,5),(false,9),(true,1)]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) false)), ([false,false,false,true]:List Bool).all (fun p => ([false,false,false,true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some 5, some false, some false, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_4_0_0
example : (keyLookup (([false,false,true]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) false), keyLookup (([false,false,true]:List Bool).map (fun p => (p,p))) false, ([false,false,false,true]:List Bool).all (fun p => ([false,false,false,true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some false, some false, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_4_0_1
example : (keyLookup ([(false,5),(false,9),(true,1)]:List (Bool × Nat)) false, keyLookup (([(false,5),(false,9),(true,1)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) false), (keyLookup ([(false,5),(false,9),(true,1)]:List (Bool × Nat)) false).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) false)), ([false,false,false,true]:List Bool).all (fun p => ([false,false,false,true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some 5, some false, some false, false) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_4_0_1
example : (keyLookup (([false,false,true]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) false), keyLookup (([false,false,true]:List Bool).map (fun p => (p,p))) false, ([false,false,false,true]:List Bool).all (fun p => ([false,false,false,true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some false, some false, false) := by simp [keyLookup, holAlookup]

-- am_id_bool_4_0
example : keyLookup (([false,false,true]:List Bool).map (fun p => (p,p))) false = some false := by simp [keyLookup, holAlookup]

-- am_any_bool_4_1_0
example : (keyLookup ([(false,5),(false,9),(true,1)]:List (Bool × Nat)) true, keyLookup (([(false,5),(false,9),(true,1)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun x:Bool => if x then 5 else 2) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) p.1) p.2))) ((fun x:Bool => if x then 5 else 2) true), (keyLookup ([(false,5),(false,9),(true,1)]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun x:Bool => if x then 5 else 2) true)), ([true,false,false,true]:List Bool).all (fun p => ([true,false,false,true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some 1, some true, some true, true) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_4_1_0
example : (keyLookup (([false,false,true]:List Bool).map (fun p => ((fun x:Bool => if x then 5 else 2) p,p))) ((fun x:Bool => if x then 5 else 2) true), keyLookup (([false,false,true]:List Bool).map (fun p => (p,p))) true, ([true,false,false,true]:List Bool).all (fun p => ([true,false,false,true]:List Bool).all (fun q => decide ((fun x:Bool => if x then 5 else 2) p = (fun x:Bool => if x then 5 else 2) q → p=q)))) = (some true, some true, true) := by simp [keyLookup, holAlookup]

-- am_any_bool_4_1_1
example : (keyLookup ([(false,5),(false,9),(true,1)]:List (Bool × Nat)) true, keyLookup (([(false,5),(false,9),(true,1)]:List (Bool × Nat)).map (fun p:Bool × Nat => ((fun _:Bool => 0) p.1, (fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) p.1) p.2))) ((fun _:Bool => 0) true), (keyLookup ([(false,5),(false,9),(true,1)]:List (Bool × Nat)) true).map ((fun k:Nat => fun y:Nat => decide ((k+y)%2=0)) ((fun _:Bool => 0) true)), ([true,false,false,true]:List Bool).all (fun p => ([true,false,false,true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some 1, some false, some false, false) := by simp [keyLookup, holAlookup]

-- am_injfst_bool_4_1_1
example : (keyLookup (([false,false,true]:List Bool).map (fun p => ((fun _:Bool => 0) p,p))) ((fun _:Bool => 0) true), keyLookup (([false,false,true]:List Bool).map (fun p => (p,p))) true, ([true,false,false,true]:List Bool).all (fun p => ([true,false,false,true]:List Bool).all (fun q => decide ((fun _:Bool => 0) p = (fun _:Bool => 0) q → p=q)))) = (some false, some true, false) := by simp [keyLookup, holAlookup]

-- am_id_bool_4_1
example : keyLookup (([false,false,true]:List Bool).map (fun p => (p,p))) true = some true := by simp [keyLookup, holAlookup]
