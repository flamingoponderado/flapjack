import Flapjack.Compiler.Backend.RegAlloc.Proofs.Invariants
import Flapjack.Compiler.Backend.RegAlloc.Exceptions
namespace Flapjack.Test.RegAllocInvariantsParity
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-! Kernel replay of `scripts/hol-probes/reg_alloc_invariants_probe.out`: original
HOL invariant rows. `T` rows are proved, `F` rows are refuted. -/

private def mkS (adj : List (List Nat)) (tags : List Tag) (deg : List Nat) (dim : Nat)
    (simp freeze : List Nat) (avail unavail : List (Nat × Nat × Nat)) (coal : List Nat)
    (mr : List Bool) : State :=
  { adj_ls := adj, node_tag := tags, degrees := deg, dim := dim, simp_wl := simp,
    spill_wl := [], freeze_wl := freeze, avail_moves_wl := avail,
    unavail_moves_wl := unavail, coalesced := coal, move_related := mr, stack := [] }

private def empty : State := mkS [] [] [] 0 [] [] [] [] [] []

-- he_hit=T
example : hasEdge [[1], [0]] 0 1 := by simp [hasEdge, holEl, holHd]
-- he_miss=F
example : ¬ hasEdge [[1], [0]] 0 0 := by simp [hasEdge, holEl, holHd]
-- he_y_oob=F
example : ¬ hasEdge [[5]] 0 5 := by simp [hasEdge]
-- he_x_oob=F
example : ¬ hasEdge [[1], [0]] 2 1 := by simp [hasEdge]
-- he_large=F
example : ¬ hasEdge [[36893488147419103232], []] 0 36893488147419103232 := by simp [hasEdge]
-- und_sym=T
example : undirected [[1], [0]] := by
  rintro x y ⟨hx, hy, hm⟩
  simp only [List.length_cons, List.length_nil] at hx hy
  refine ⟨hy, hx, ?_⟩
  rcases x with _ | _ | x <;> rcases y with _ | _ | y <;> simp_all [holEl, holHd] <;> omega
-- und_asym=F
example : ¬ undirected [[1], []] := fun h => by
  have := h 0 1 (by simp [hasEdge, holEl, holHd])
  simp [hasEdge, holEl, holHd] at this
-- grs_ok=T
example : goodRaState (mkS [[1], [0]] [.Atemp, .Atemp] [1, 1] 2 [0] [1] [(0, 0, 1)] [(3, 1, 1)]
    [0, 1] [false, false]) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [mkS, holSorted]
  rintro x y ⟨hx, hy, hm⟩
  simp only [List.length_cons, List.length_nil] at hx hy
  refine ⟨hy, hx, ?_⟩
  rcases x with _ | _ | x <;> rcases y with _ | _ | y <;> simp_all [holEl, holHd] <;> omega
-- grs_unsorted=F
example : ¬ goodRaState (mkS [[1, 2], [0], [0]] [.Atemp, .Atemp, .Atemp] [2, 1, 1] 3 [] [] [] []
    [0, 1, 2] [false, false, false]) := fun h => by
  have := h.2.2.2.2.2.2.2.1 [1, 2] (by simp [mkS])
  simp [holSorted] at this
-- grs_bad_move=F
example : ¬ goodRaState (mkS [[1], [0]] [.Atemp, .Atemp] [1, 1] 2 [] [] [(0, 0, 2)] [] [0, 1]
    [false, false]) := fun h => by
  have := h.2.2.2.2.2.2.2.2.2.2.2.1 (0, 0, 2) (by simp [mkS])
  simp [mkS] at this
-- grs_bad_length=F
example : ¬ goodRaState (mkS [[1], [0]] [.Atemp] [1, 1] 2 [] [] [] [] [0, 1] [false, false]) :=
  fun h => by have := h.2.1; simp [mkS] at this
-- nc_ok=T
example : noClash [[1], [0]] [.Fixed 0, .Fixed 1] := by
  rintro x y ⟨hx, hy, hm⟩
  simp only [List.length_cons, List.length_nil] at hx hy
  rcases x with _ | _ | x <;> rcases y with _ | _ | y <;> simp_all [holEl, holHd] <;> omega
-- nc_clash=F
example : ¬ noClash [[1], [0]] [.Fixed 0, .Fixed 0] := fun h => by
  have := h 0 1 (by simp [hasEdge, holEl, holHd])
  simp [holEl, holHd] at this
-- nc_atemp=T
example : noClash [[1], [0]] [.Fixed 0, .Atemp] := by
  rintro x y ⟨hx, hy, hm⟩
  simp only [List.length_cons, List.length_nil] at hx hy
  rcases x with _ | _ | x <;> rcases y with _ | _ | y <;> simp_all [holEl, holHd] <;> omega
-- nc_self=T
example : noClash [[0]] [.Fixed 3] := by
  rintro x y ⟨hx, hy, hm⟩
  simp only [List.length_cons, List.length_nil] at hx hy
  rcases x with _ | x <;> rcases y with _ | y <;> simp_all [holEl, holHd] <;> omega
-- spi_ok=T
example : spInverts (sptInsert 4 0 .ln) (sptInsert 0 4 .ln) := by
  intro m fm h
  by_cases hm : m = 4
  · subst hm; rw [sptLookup_sptInsert_same] at h; cases h; rw [sptLookup_sptInsert_same]
  · rw [sptLookup_sptInsert_ne _ _ _ _ hm] at h; simp [sptLookup] at h
-- spi_bad=F
example : ¬ spInverts (sptInsert 4 0 .ln) (sptInsert 0 5 .ln) := fun h => by
  have := h 4 0 (sptLookup_sptInsert_same ..)
  rw [sptLookup_sptInsert_same] at this
  cases this
-- spi_insert=T
example : spInverts (sptInsert 7 1 (sptInsert 4 0 .ln)) (sptInsert 1 7 (sptInsert 0 4 .ln)) := by
  refine spInvertsInsert _ _ 7 1 ⟨?_, ?_, ?_⟩
  · intro m fm h
    by_cases hm : m = 4
    · subst hm; rw [sptLookup_sptInsert_same] at h; cases h; rw [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne _ _ _ _ hm] at h; simp [sptLookup] at h
  · simp [sptDomain, sptLookup_sptInsert_ne _ _ _ _ (by decide : (7 : Nat) ≠ 4), sptLookup]
  · simp [sptDomain, sptLookup]
-- clq_ok=T
example : isClique [0, 1] [[1], [0]] := by
  rintro x y ⟨hx, hy, hne⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all [hasEdge, holEl, holHd]
-- clq_bad=F
example : ¬ isClique [0, 1, 2] [[1], [0], []] := fun h => by
  have := h 0 2 (by simp)
  simp [hasEdge, holEl, holHd] at this
-- sub_ok=T
example : isSubgraph [[1], [0]] [[2, 1], [0], []] := by
  rintro x y ⟨hx, hy, hm⟩
  simp only [List.length_cons, List.length_nil] at hx hy
  rcases x with _ | _ | x <;> rcases y with _ | _ | y <;> simp_all [hasEdge, holEl, holHd] <;> omega
-- sub_bad=F
example : ¬ isSubgraph [[1], [0]] [[1], []] := fun h => by
  have := h 1 0 (by simp [hasEdge, holEl, holHd])
  simp [hasEdge, holEl, holHd] at this
-- hide_num=36893488147419103232
example : hide (36893488147419103232 : Nat) = 36893488147419103232 := rfl
-- cs_ok=T
example : colouringSatisfactory (fun x : Nat => x) [[1], [0]] := fun _ _ _ _ h => h
-- cs_bad=F
example : ¬ colouringSatisfactory (fun _ : Nat => (0 : Nat)) [[1], [0]] := fun h => by
  have := h 0 (by simp) 1 (by simp [holEl, holHd]) rfl
  simp at this
-- cs_self_loop=T
example : colouringSatisfactory (fun _ : Nat => (0 : Nat)) [[0]] := by
  intro x hx y ⟨hy, hm⟩ _
  simp only [List.length_cons, List.length_nil] at hx hy
  omega
-- gp_first=T
example : goodPref (fun (_ : Nat) (ks : List Nat) (s : State) =>
    ((.success ks.head? : Exc (Option Nat) StateException), s)) := by
  intro n ks s _
  refine ⟨ks.head?, rfl, ?_⟩
  cases ks <;> simp
-- gp_outside=F
example : ¬ goodPref (fun (_ : Nat) (_ : List Nat) (s : State) =>
    ((.success (some 0) : Exc (Option Nat) StateException), s)) := fun h => by
  obtain ⟨res, hr, hm⟩ := h 0 [] empty (by simp [goodRaState, empty, mkS, undirected, hasEdge])
  simp only [Prod.mk.injEq, Exc.success.injEq] at hr
  obtain ⟨rfl, -⟩ := hr
  simp at hm
-- gnp_none=T
example : goodNegPref 5 (fun (_ : Nat) (_ : List Nat) (s : State) =>
    ((.success none : Exc (Option Nat) StateException), s)) :=
  fun _ _ _ _ => ⟨none, rfl, trivial⟩
-- gnp_low=F
example : ¬ goodNegPref 5 (fun (_ : Nat) (_ : List Nat) (s : State) =>
    ((.success (some 4) : Exc (Option Nat) StateException), s)) := fun h => by
  obtain ⟨res, hr, hm⟩ := h 0 [] empty (by simp [goodRaState, empty, mkS, undirected, hasEdge])
  simp only [Prod.mk.injEq, Exc.success.injEq] at hr
  obtain ⟨rfl, -⟩ := hr
  simp at hm

end Flapjack.Test.RegAllocInvariantsParity
