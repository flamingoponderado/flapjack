import Flapjack.Compiler.Backend.RegAlloc.Proofs.MkBij
namespace Flapjack.Test.RegAllocMkBijLemmasParity
open Flapjack Flapjack.RegAlloc

/-! Kernel replay of `scripts/hol-probes/reg_alloc_mk_bij_lemmas_probe.out`:
original HOL `list_remap`/`mk_bij` instances observed through `toAList`, with
the ported domain, bijection and well-formedness lemmas applied to them. -/

private def keys (r : Spt Nat × Spt Nat × Nat) : List Nat × List Nat × Nat :=
  ((sptToAList r.1).map Prod.fst, (sptToAList r.2.1).map Prod.fst, r.2.2)
private def assoc (r : Spt Nat × Spt Nat × Nat) : List (Nat × Nat) × List (Nat × Nat) × Nat :=
  (sptToAList r.1, sptToAList r.2.1, r.2.2)
private def tree : ClashTree :=
  .seq (.delta [4] [2, 4]) (.branch (some (sptInsert 9 () .ln)) (.delta [] [1])
    (.set (sptInsert 2 () .ln)))

-- mbl_remap_keys=([3; 5],[7; 8],9)
example : keys (listRemap [5, 3, 5] (sptInsert 3 7 .ln, sptInsert 7 3 .ln, 8)) =
    ([3, 5], [7, 8], 9) := by
  simp [keys, listRemap, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]
-- mbl_remap_wf=(T,T)
example : (sptWf (listRemap [5, 3, 5] (sptInsert 3 7 .ln, sptInsert 7 3 .ln, 8)).1,
    sptWf (listRemap [5, 3, 5] (sptInsert 3 7 .ln, sptInsert 7 3 .ln, 8)).2.1) = (true, true) := by
  simp [listRemap, sptInsert, sptLookup, sptWf, sptIsEmpty]
-- mbl_remap_inverse=([(3,0); (5,1)],[(1,5); (0,3)],2)
example : assoc (listRemap [5, 3, 5] (sptInsert 3 0 .ln, sptInsert 0 3 .ln, 1)) =
    ([(3, 0), (5, 1)], [(1, 5), (0, 3)], 2) := by
  simp [assoc, listRemap, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext]
-- mbl_tree_keys=([(1,0); (9,2); (4,3); (2,1)],[(3,4); (1,2); (0,1); (2,9)],4)
example : assoc (mkBij tree) = ([(1, 0), (9, 2), (4, 3), (2, 1)], [(3, 4), (1, 2), (0, 1), (2, 9)], 4) := by
  simp [assoc, mkBij, mkBijAux, tree, listRemap, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext,
    ]
-- mbl_tree_wf=(T,T)
example : (sptWf (mkBij tree).1, sptWf (mkBij tree).2.1) = (true, true) := by
  simp [mkBij, mkBijAux, tree, listRemap, sptInsert, sptLookup, sptToAList, sptFoldi, lrNext,
    sptWf, sptIsEmpty]
-- mbl_large=([(36893488147419103232,0)],[(0,36893488147419103232)],1)
example : assoc (mkBij (.delta [36893488147419103232] [])) =
    ([(36893488147419103232, 0)], [(0, 36893488147419103232)], 1) := by
  simp [assoc, mkBij, mkBijAux, listRemap, sptInsert, sptToAList, sptFoldi, lrNext,
    ]

private theorem invLn : spInverts .ln .ln := fun _ _ h => by simp [sptLookup] at h
private theorem domLn : sptDomain (.ln : Spt Nat) = fun x => x < 0 := by
  funext x; simp [sptDomain, sptLookup]

/-- `mk_bij_aux_domain`, `mk_bij_aux_bij` and `mk_bij_aux_wf` at the probe tree from
`mk_bij`'s empty maps. -/
example : let r := mkBijAux tree (.ln, .ln, 0)
    (sptDomain r.1 = fun x => sptDomain (.ln : Spt Nat) x ∨ inClashTree tree x) ∧
    (spInverts r.1 r.2.1 ∧ spInverts r.2.1 r.1 ∧ sptDomain r.2.1 = fun x => x < r.2.2) ∧
    (sptWf r.1 = true ∧ sptWf r.2.1 = true) :=
  ⟨mkBijAuxDomain tree .ln .ln 0 _ _ _ rfl,
   mkBijAuxBij tree .ln .ln 0 _ _ _ ⟨rfl, invLn, invLn, domLn⟩,
   mkBijAuxWf tree .ln .ln 0 _ _ _ ⟨rfl, rfl, rfl⟩⟩

/-- `list_remap_domain`, `list_remap_bij` and `list_remap_wf` at `mbl_remap_inverse`. -/
example : let r := listRemap [5, 3, 5] (sptInsert 3 0 .ln, sptInsert 0 3 .ln, 1)
    (sptDomain r.1 = fun x => sptDomain (sptInsert 3 0 .ln) x ∨ x ∈ [5, 3, 5]) ∧
    (sptWf r.1 = true ∧ sptWf r.2.1 = true) :=
  ⟨listRemapDomain _ _ _ _ _ _ _ rfl,
   listRemapWf _ _ _ _ _ _ _ ⟨rfl, sptWfInsert _ _ _ rfl, sptWfInsert _ _ _ rfl⟩⟩

end Flapjack.Test.RegAllocMkBijLemmasParity
