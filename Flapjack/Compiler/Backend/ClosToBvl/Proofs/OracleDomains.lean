module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Oracle
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
import Flapjack.Misc.Sptree.ToAList
import Mathlib.Data.Set.Lattice

@[expose] public section

/-! Domains and freshness of code accumulated from an oracle. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open BackendProps

/-- Accumulated code contains exactly the labels from earlier oracle entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "domain_nth_code"]
theorem domain_nthCode {C A : Type} (n : Nat) (orac : Nat → C × List (Nat × A)) :
    sptDomain (nthCode orac n) =
      ⋃₀ {s : Set Nat | s ∈ (List.range n).map (fun i => ({x | x ∈ (orac i).2.map Prod.fst} : Set Nat))} := by
  induction n generalizing orac with
  | zero =>
    ext x
    change sptDomain (nthCode orac 0) x ↔
      ∃ s : Set Nat, s ∈ (List.range 0).map (fun i => ({x | x ∈ (orac i).2.map Prod.fst} : Set Nat)) ∧ x ∈ s
    simp [nthCode, sptDomain]
  | succ n ih =>
    ext x
    change sptDomain (nthCode orac (n + 1)) x ↔
      ∃ s : Set Nat, s ∈ (List.range (n + 1)).map (fun i => ({x | x ∈ (orac i).2.map Prod.fst} : Set Nat)) ∧ x ∈ s
    simp only [nthCode, sptDomain_sptUnion, sptDomainFromAList, ih]
    change (x ∈ (orac 0).2.map Prod.fst ∨
      ∃ s : Set Nat, s ∈ (List.range n).map
        (fun i => ({x | x ∈ (orac (i + 1)).2.map Prod.fst} : Set Nat)) ∧ x ∈ s) ↔ _
    simp [List.range_succ_eq_map, Function.comp_def]

/-- A monotone oracle avoids all labels in the initial and previously accumulated code. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "DISJOINT_nth_code_monotonic"]
theorem disjoint_nthCode_monotonic {C A : Type}
    (init : Spt A) (orac : Nat → C × List (Nat × A)) (v : List (Nat × A)) (n : Nat)
    (h : oracleMonotonic (fun entry : C × List (Nat × A) => {x | x ∈ entry.2.map Prod.fst})
      (· < ·) (sptDomain init) orac ∧ v = (orac n).2) :
    ∀ x, ¬ (sptDomain (sptUnion init (nthCode orac n)) x ∧ x ∈ v.map Prod.fst) := by
  obtain ⟨mono, rfl⟩ := h
  intro x ⟨inUnion, current⟩
  change sptMem x (sptUnion init (nthCode orac n)) at inUnion
  rw [sptMem_sptUnion] at inUnion
  rcases inUnion with present | past
  · have lt := mono.2 n x x present current
    omega
  · change sptDomain (nthCode orac n) x at past
    rw [domain_nthCode] at past
    change ∃ s : Set Nat,
      s ∈ (List.range n).map (fun i => ({x | x ∈ (orac i).2.map Prod.fst} : Set Nat)) ∧ x ∈ s at past
    obtain ⟨s, smem, xmem⟩ := past
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp smem
    have hi := List.mem_range.mp hi
    have lt := mono.1 i n x x hi xmem current
    omega
end Flapjack.Compiler.Backend.ClosToBvl
