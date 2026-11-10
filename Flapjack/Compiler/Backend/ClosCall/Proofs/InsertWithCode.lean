module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.FiniteMap.AlistExact.Lookup
public import Flapjack.Misc.Option
@[expose] public section

/-! Inserting direct-call locations together with their auxiliary code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- Insert locations and append their looked-up code entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "insert_each'_def"]
noncomputable def insertWithCode {A : Type} [Nonempty A] (gt : List (Nat × A)) :
    Nat → Nat → NumSet × List (Nat × A) → NumSet × List (Nat × A)
  | _, 0, g => g
  | p, n + 1, (d, aux) =>
      insertWithCode gt (p + 2) n (sptInsert p () d, (p + 1, holThe (holALookup gt (p + 1))) :: aux)

/-- Paired insertion has the same sparse component as location insertion. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "FST_insert_each'"]
theorem insertWithCode_fst {A : Type} [Nonempty A] (gt : List (Nat × A)) (p n : Nat)
    (g : NumSet × List (Nat × A)) :
    (insertWithCode gt p n g).1 = (insertEachSource p n g).1 := by
  induction n generalizing p g with
  | zero => rfl
  | succ n ih =>
    cases g with
    | mk d aux =>
      simp only [insertWithCode, insertEachSource]
      rw [ih]
      exact insertEach_fst_same _ _ _ _ rfl

/-- Paired insertion prepends the reverse generated lookup list. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "SND_insert_each'"]
theorem insertWithCode_snd {A : Type} [Nonempty A] (gt : List (Nat × A)) (p n : Nat)
    (g : NumSet × List (Nat × A)) :
    (insertWithCode gt p n g).2 =
      ((List.range n).map (fun i => (2 * i + p + 1, holThe (holALookup gt (2 * i + p + 1))))).reverse ++ g.2 := by
  induction n generalizing p g with
  | zero => simp [insertWithCode]
  | succ n ih =>
    cases g with
    | mk d aux =>
      simp only [insertWithCode, ih, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.reverse_cons, List.append_assoc, List.singleton_append, Nat.mul_zero, Nat.zero_add]
      congr 1
      congr 2
      funext i
      simp only [Function.comp_apply]
      have eq : 2 * i + (p + 2) + 1 = 2 * (i + 1) + p + 1 := by omega
      rw [eq]

/-- Paired insertion prepends exactly the generated label sequence. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "MAP_FST_insert_each'"]
theorem insertWithCode_labels {A : Type} [Nonempty A] (gt : List (Nat × A)) (p n : Nat)
    (g : NumSet × List (Nat × A)) :
    (insertWithCode gt p n g).2.map Prod.fst =
      ((List.range n).map (fun i => p + i * 2 + 1)).reverse ++ g.2.map Prod.fst := by
  rw [insertWithCode_snd]
  simp [List.map_append, List.map_reverse, List.map_map, Function.comp_def,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

/-- Inserting fresh locations with their code preserves the full invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "wfg_insert_each'"]
theorem insertWithCode_wellFormed {A : Type} [Nonempty A] (gt : List (Nat × A)) (p n : Nat)
    (g : NumSet × List (Nat × A))
    (h : wellFormed g ∧ ∀ x, ¬ (x ∈ (List.range n).map (fun i => p + 2 * i) ∧ sptDomain g.1 x)) :
    wellFormed (insertWithCode gt p n g) := by
  obtain ⟨⟨oldEq, oldDistinct⟩, disjoint⟩ := h
  have fresh : ∀ x, x ∈ (List.range n).map (fun i => p + 2 * i) → ¬ sptDomain g.1 x :=
    fun x mem known => disjoint x ⟨mem, known⟩
  unfold wellFormed
  rw [insertWithCode_fst, domain_insertEach, insertWithCode_labels]
  constructor
  · ext label
    have old : label ∈ g.2.map Prod.fst ↔ ∃ x, sptDomain g.1 x ∧ Nat.succ x = label := by
      change label ∈ {label | label ∈ g.2.map Prod.fst} ↔ _
      rw [oldEq]
      rfl
    simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_reverse, old,
      Set.mem_image]
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro (⟨i, bound, eq⟩ | ⟨x, known, eq⟩)
      · refine ⟨2 * i + p, Or.inl ⟨i, bound, rfl⟩, ?_⟩
        omega
      · exact ⟨x, Or.inr known, eq⟩
    · rintro ⟨x, (⟨i, bound, eq⟩ | known), labelEq⟩
      · left
        refine ⟨i, bound, ?_⟩
        omega
      · exact Or.inr ⟨x, known, labelEq⟩
  · apply List.Nodup.append
    · apply List.nodup_reverse.mpr
      apply List.Nodup.map (fun _ _ equal => by omega) List.nodup_range
    · exact oldDistinct
    · intro label new old
      simp only [List.mem_reverse, List.mem_map, List.mem_range] at new
      obtain ⟨i, bound, eq⟩ := new
      have oldDomain : label ∈ Set.image Nat.succ (sptDomain g.1) := by
        rw [← oldEq]
        exact old
      obtain ⟨x, known, labelEq⟩ := oldDomain
      have same : x = p + 2 * i := by omega
      apply fresh x
      · exact List.mem_map.mpr ⟨i, List.mem_range.mpr bound, same.symm⟩
      · exact known

end Flapjack.Compiler.Backend.ClosCall
