module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AuxNameRange
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Namespace

@[expose] public section

namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack

open Classical in
/-- Incremental compilation preserves distinct names and characterizes output namespaces. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_inc_lemma"]
theorem compileInc_lemma (next1 : Nat) (prog1 : List (Nat × Nat × Bvl.Exp))
    (next2 : Nat) (prog2 : List (Nat × Nat × Bvi.Exp))
    (compiled : compileIncSource next1 prog1 = (next2, prog2)) :
    ((prog1.map Prod.fst).Nodup → (prog2.map Prod.fst).Nodup) ∧ next1 ≤ next2 ∧
    (∀ p, bvlNumStubs + p * bvlToBviNamespaces ∈ prog2.map Prod.fst → p ∈ prog1.map Prod.fst) ∧
    (∀ p, p ∈ prog2.map Prod.fst →
      if inNs 0 p then ∃ q, bvlNumStubs + q * bvlToBviNamespaces = p
      else inNs 1 p ∧ bvlNumStubs + bvlToBviNamespaces * next1 ≤ p ∧
        p < bvlNumStubs + bvlToBviNamespaces * next2) := by
  have mono : next1 ≤ next2 := by simpa [compiled] using compileIncSource_counter_mono next1 prog1
  have classify (p : Nat) (member : p ∈ prog2.map Prod.fst) := by
    have orig : p ∈ (compileIncSource next1 prog1).2.map Prod.fst := by simpa [compiled] using member
    have h := compileIncSource_nameRange next1 prog1 p orig
    simpa [compiled] using h
  refine ⟨?_, mono, ?_, ?_⟩
  · intro distinct
    simpa [compiled] using compileIncSource_names_nodup next1 prog1 distinct
  · intro p member
    rcases classify _ member with ⟨q, qMember, eq⟩ | ⟨i, lower, upper, eq⟩
    · have : p = q := by
        simp only [bvlToBviNamespaces] at eq
        omega
      simpa [this] using qMember
    · simp only [bvlToBviNamespaces] at eq
      omega
  · have hstub : bvlNumStubs % 4 = 0 := by
      simpa [bvlToBviNamespaces] using bvlNumStubMod
    intro p member
    rcases classify p member with ⟨q, qMember, eq⟩ | ⟨i, lower, upper, eq⟩
    · have nsZero : inNs 0 p := by
        rw [eq]
        simp [inNs, Nat.add_mod, bvlToBviNamespaces, hstub]
      simp only [nsZero, if_true]
      exact ⟨q, by simpa [Nat.mul_comm] using eq.symm⟩
    · have nsOne : inNs 1 p := by
        rw [eq]
        simp [inNs, Nat.add_mod, bvlToBviNamespaces, hstub]
      have notZero : ¬ inNs 0 p := by
        rw [eq]
        simp [inNs, Nat.add_mod, bvlToBviNamespaces, hstub]
      simp only [notZero, if_false]
      refine ⟨nsOne, ?_, ?_⟩ <;> simp only [bvlToBviNamespaces] at eq ⊢ <;> omega

open Classical in
/-- Incremental compilation does not decrease the next counter. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_inc_next"]
theorem compileInc_next (next1 : Nat) (prog1 : List (Nat × Nat × Bvl.Exp))
    (next2 : Nat) (prog2 : List (Nat × Nat × Bvi.Exp))
    (compiled : compileIncSource next1 prog1 = (next2, prog2)) : next1 ≤ next2 :=
  (compileInc_lemma next1 prog1 next2 prog2 compiled).2.1
open Classical in
/-- Incremental compilation preserves distinct function names. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_inc_DISTINCT"]
theorem compileInc_distinct (next1 : Nat) (prog1 : List (Nat × Nat × Bvl.Exp))
    (next2 : Nat) (prog2 : List (Nat × Nat × Bvi.Exp))
    (h : compileIncSource next1 prog1 = (next2, prog2) ∧ (prog1.map Prod.fst).Nodup) :
    (prog2.map Prod.fst).Nodup :=
  (compileInc_lemma next1 prog1 next2 prog2 h.1).1 h.2
open Classical in
/-- Incremental compilation characterizes the range and origin of output names. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_inc_next_range"]
theorem compileInc_nextRange (next1 : Nat) (prog1 : List (Nat × Nat × Bvl.Exp))
    (next2 : Nat) (prog2 : List (Nat × Nat × Bvi.Exp)) (x : Nat)
    (h : compileIncSource next1 prog1 = (next2, prog2) ∧ x ∈ prog2.map Prod.fst) :
    if inNs 1 x then bvlNumStubs + bvlToBviNamespaces * next1 ≤ x ∧
        x < bvlNumStubs + bvlToBviNamespaces * next2
    else inNs 0 x ∧ bvlNumStubs ≤ x ∧
      (x - bvlNumStubs) / bvlToBviNamespaces ∈ prog1.map Prod.fst := by
  have invariant := compileInc_lemma next1 prog1 next2 prog2 h.1
  have hx := invariant.2.2.2 x h.2
  by_cases hz : inNs 0 x
  · simp only [hz, if_true] at hx
    obtain ⟨q, eq⟩ := hx
    have ho : ¬ inNs 1 x := by
      unfold inNs at hz ⊢
      omega
    simp only [ho, if_false]
    refine ⟨hz, ?_, ?_⟩
    · omega
    · have heq : (x - bvlNumStubs) / bvlToBviNamespaces = q := by
        rw [← eq]
        simp [bvlToBviNamespaces]
      rw [heq]
      apply invariant.2.2.1 q
      rw [eq]
      exact h.2
  · simp only [hz, if_false] at hx
    simp [hx.1, hx.2.1, hx.2.2]
end Flapjack.Compiler.Backend.BvlToBvi.Proofs
