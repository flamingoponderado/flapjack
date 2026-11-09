module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute

@[expose] public section

/-! Stack operations preserving the data-to-word abstract heap invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Dropping corresponding prefixes preserves the abstract heap invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "pop_thm"
  (words_as_type_indexed_bitvec)]
theorem popThm {width : Nat} [NeZero width] (conf : Config)
    (xs stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (rs roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) :
    absMlInv conf (xs ++ stack) refs (rs ++ roots, heap, bigEndian, a, sp, sp1, gens) limit next ∧
      xs.length = rs.length →
    absMlInv conf stack refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  rintro ⟨inv, lengths⟩
  have result := absMlInv_stackPermute conf stack refs roots heap bigEndian a sp sp1 gens limit next
    (xs.zip rs) [] (by
      refine ⟨?_, by simp⟩
      simpa only [List.map_fst_zip (Nat.le_of_eq lengths),
        List.map_snd_zip (Nat.le_of_eq lengths.symm)] using inv)
  simpa using result

/-- Duplicating corresponding prefixes preserves the abstract heap invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "duplicate_thm"
  (words_as_type_indexed_bitvec)]
theorem duplicateThm {width : Nat} [NeZero width] (conf : Config)
    (xs stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (rs roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) :
    absMlInv conf (xs ++ stack) refs (rs ++ roots, heap, bigEndian, a, sp, sp1, gens) limit next ∧
      xs.length = rs.length →
    absMlInv conf (xs ++ xs ++ stack) refs
      (rs ++ rs ++ roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  rintro ⟨inv, lengths⟩
  have result := absMlInv_stackPermute conf stack refs roots heap bigEndian a sp sp1 gens limit next
    (xs.zip rs) (xs.zip rs ++ xs.zip rs) (by
      refine ⟨?_, by simp⟩
      simpa only [List.map_fst_zip (Nat.le_of_eq lengths),
        List.map_snd_zip (Nat.le_of_eq lengths.symm)] using inv)
  simpa only [List.map_append, List.map_fst_zip (Nat.le_of_eq lengths),
    List.map_snd_zip (Nat.le_of_eq lengths.symm)] using result

/-- Exchanging two corresponding stack segments preserves the abstract invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "move_thm"
  (words_as_type_indexed_bitvec)]
theorem moveThm {width : Nat} [NeZero width] (conf : Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat)
    (xs1 : List Flapjack.Compiler.Backend.DataSem.Value) (rs1 : List (HeapAddress (WordLocW width)))
    (xs2 : List Flapjack.Compiler.Backend.DataSem.Value) (rs2 : List (HeapAddress (WordLocW width)))
    (xs3 : List Flapjack.Compiler.Backend.DataSem.Value) (rs3 : List (HeapAddress (WordLocW width))) :
    absMlInv conf (xs1 ++ xs2 ++ xs3 ++ stack) refs
      (rs1 ++ rs2 ++ rs3 ++ roots, heap, bigEndian, a, sp, sp1, gens) limit next ∧
      xs1.length = rs1.length ∧ xs2.length = rs2.length ∧ xs3.length = rs3.length →
    absMlInv conf (xs1 ++ xs3 ++ xs2 ++ stack) refs
      (rs1 ++ rs3 ++ rs2 ++ roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  rintro ⟨inv, len1, len2, len3⟩
  have result := absMlInv_stackPermute conf stack refs roots heap bigEndian a sp sp1 gens limit next
    (xs1.zip rs1 ++ xs2.zip rs2 ++ xs3.zip rs3)
    (xs1.zip rs1 ++ xs3.zip rs3 ++ xs2.zip rs2) (by
      refine ⟨?_, ?_⟩
      · simpa only [List.map_append, List.map_fst_zip (Nat.le_of_eq len1),
          List.map_snd_zip (Nat.le_of_eq len1.symm), List.map_fst_zip (Nat.le_of_eq len2),
          List.map_snd_zip (Nat.le_of_eq len2.symm), List.map_fst_zip (Nat.le_of_eq len3),
          List.map_snd_zip (Nat.le_of_eq len3.symm), List.append_assoc] using inv
      · intro pair member
        simp only [List.mem_append] at member ⊢
        tauto)
  simpa only [List.map_append, List.map_fst_zip (Nat.le_of_eq len1),
    List.map_snd_zip (Nat.le_of_eq len1.symm), List.map_fst_zip (Nat.le_of_eq len2),
    List.map_snd_zip (Nat.le_of_eq len2.symm), List.map_fst_zip (Nat.le_of_eq len3),
    List.map_snd_zip (Nat.le_of_eq len3.symm), List.append_assoc] using result

/-- A single paired element may be duplicated. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "duplicate1_thm"
  (words_as_type_indexed_bitvec)]
theorem duplicate1Thm {width : Nat} [NeZero width] (conf : Config)
    (x1 : Flapjack.Compiler.Backend.DataSem.Value) (stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (r1 : HeapAddress (WordLocW width)) (roots : List (HeapAddress (WordLocW width)))
    (heap : ValueHeap width) (bigEndian : Bool) (a sp sp1 : Nat)
    (gens : GenState) (limit next : Nat) :
    absMlInv conf (x1 :: stack) refs (r1 :: roots, heap, bigEndian, a, sp, sp1, gens) limit next →
    absMlInv conf (x1 :: x1 :: stack) refs
      (r1 :: r1 :: roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  intro inv
  simpa using duplicateThm conf [x1] stack refs [r1] roots heap bigEndian a sp sp1 gens limit next ⟨inv, rfl⟩

/-- The invariant relates one root to each value. This is Flapjack list infrastructure. -/
theorem absMlInv_rootsLength {width : Nat} [NeZero width] (conf : Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat)
    (inv : absMlInv conf stack refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next) :
    stack.length = roots.length := by
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨_, _, _, _, _, _, _, _, _, related, _⟩ := stackInv
  exact related.length_eq

/-- Split any sufficiently long list at a requested length. This is Flapjack list infrastructure. -/
theorem listSplitAtLength {α : Type} (items : List α) (n : Nat) (bound : n ≤ items.length) :
    ∃ front suffix, items = front ++ suffix ∧ front.length = n := by
  exact ⟨items.take n, items.drop n, (List.take_append_drop n items).symm,
    by simp [List.length_take, Nat.min_eq_left bound]⟩

/-- Split roots to match the first stack prefix. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "split1_thm"
  (words_as_type_indexed_bitvec)]
theorem split1Thm {width : Nat} [NeZero width] (conf : Config)
    (xs1 stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) :
    absMlInv conf (xs1 ++ stack) refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next →
    ∃ rs1 roots1, roots = rs1 ++ roots1 ∧ rs1.length = xs1.length := by
  intro inv
  have lengths := absMlInv_rootsLength conf (xs1 ++ stack) refs roots heap bigEndian a sp sp1 gens limit next inv
  apply listSplitAtLength roots xs1.length
  simp only [List.length_append] at lengths
  omega

/-- Split roots to match two stack prefixes. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "split2_thm"
  (words_as_type_indexed_bitvec)]
theorem split2Thm {width : Nat} [NeZero width] (conf : Config)
    (xs1 xs2 stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) :
    absMlInv conf (xs1 ++ xs2 ++ stack) refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next →
    ∃ rs1 rs2 roots1, roots = rs1 ++ rs2 ++ roots1 ∧
      rs1.length = xs1.length ∧ rs2.length = xs2.length := by
  intro inv
  have lengths := absMlInv_rootsLength conf (xs1 ++ xs2 ++ stack) refs roots heap bigEndian a sp sp1 gens limit next inv
  simp only [List.length_append] at lengths
  obtain ⟨rs1, rest, hroot, hlen1⟩ := listSplitAtLength roots xs1.length (by omega)
  have hrest : xs2.length ≤ rest.length := by
    have h := congrArg List.length hroot
    simp only [List.length_append, hlen1] at h
    omega
  obtain ⟨rs2, roots1, hrest, hlen2⟩ := listSplitAtLength rest xs2.length hrest
  exact ⟨rs1, rs2, roots1, by simpa [hrest] using hroot, hlen1, hlen2⟩

/-- Split roots to match three stack prefixes. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "split3_thm"
  (words_as_type_indexed_bitvec)]
theorem split3Thm {width : Nat} [NeZero width] (conf : Config)
    (xs1 xs2 xs3 stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) :
    absMlInv conf (xs1 ++ xs2 ++ xs3 ++ stack) refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next →
    ∃ rs1 rs2 rs3 roots1, roots = rs1 ++ rs2 ++ rs3 ++ roots1 ∧
      rs1.length = xs1.length ∧ rs2.length = xs2.length ∧ rs3.length = xs3.length := by
  intro inv
  have lengths := absMlInv_rootsLength conf (xs1 ++ xs2 ++ xs3 ++ stack) refs roots heap bigEndian a sp sp1 gens limit next inv
  simp only [List.length_append] at lengths
  obtain ⟨rs1, rest, hroot, hlen1⟩ := listSplitAtLength roots xs1.length (by omega)
  have hrest : xs2.length ≤ rest.length := by
    have h := congrArg List.length hroot
    simp only [List.length_append, hlen1] at h
    omega
  obtain ⟨rs2, rest2, hrest, hlen2⟩ := listSplitAtLength rest xs2.length hrest
  have hrest2 : xs3.length ≤ rest2.length := by
    have h := congrArg List.length hroot
    have h' := congrArg List.length hrest
    simp only [List.length_append, hlen1] at h
    simp only [List.length_append, hlen2] at h'
    omega
  obtain ⟨rs3, roots1, hrest2, hlen3⟩ := listSplitAtLength rest2 xs3.length hrest2
  exact ⟨rs1, rs2, rs3, roots1, by simpa [hrest, hrest2] using hroot, hlen1, hlen2, hlen3⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
