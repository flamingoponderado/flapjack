module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeLookup
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

/-- The inserted lookup entries extend to the corresponding generated code
list under the original state, freshness, and lookup premises. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "subg_insert_each'"]
theorem stateExtends_insertWithCode {A B C D : Type} [Nonempty B] [Nonempty C] [Nonempty D]
    (newG : Spt A × List (Nat × B × C)) (ls : List (Nat × B × C))
    (loc : Nat) (g : NumSet × List (Nat × B × C))
    (gb : Spt A × List (Nat × B × C)) (fns1 : List (B × D))
    (es : List C) (g1 : List (Nat × B × C))
    (h : stateExtends gb (newG.1, ls ++ (insertWithCode g1 loc fns1.length g).2) ∧
      newG.2 = ls ++ g.2 ∧ fns1.length = es.length ∧ wellFormed g ∧
      (∀ x, ¬ (x ∈ (List.range fns1.length).map (fun i => 2 * i + loc + 1) ∧
        x ∈ Set.image Nat.succ (sptDomain g.1))) ∧
      (∀ x, ¬ (x ∈ ls.map Prod.fst ∧ x ∈ Set.image Nat.succ (sptDomain g.1))) ∧
      (∀ i, i < fns1.length → holALookup g1 (2 * i + loc + 1) =
        some ((holEl i fns1).1, holEl i es))) :
    stateExtends (newG.1, ls ++ (insertWithCode g1 loc fns1.length g).2)
      (codeListSource loc ((fns1.map Prod.fst).zip es) newG) := by
  classical
  obtain ⟨extension, oldCode, len, wf, fresh, disjoint, lookup⟩ := h
  let fns := (fns1.map Prod.fst).zip es
  have fnsLen : fns.length = fns1.length := by simp [fns, List.length_zip, len]
  let generated := (List.range fns1.length).map (fun i =>
    (2 * i + loc + 1, holThe (holALookup g1 (2 * i + loc + 1))))
  have generatedEq : generated = ((List.range fns.length).map (fun i => loc + 1 + 2 * i)).zip fns := by
    apply List.ext_getElem
    · simp [generated, fnsLen]
    · intro i hi hj
      have bound : i < fns1.length := by simpa [generated] using hi
      have boundE : i < es.length := by omega
      have boundF : i < fns.length := by omega
      have found := lookup i bound
      rw [holEl_eq_getElem i fns1 bound, holEl_eq_getElem i es boundE] at found
      simp only [generated, List.getElem_map, List.getElem_range, List.getElem_zip]
      simp only [fns, List.getElem_zip, List.getElem_map]
      rw [found]
      simp [holThe, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have inserted : (insertWithCode g1 loc fns1.length g).2 = generated.reverse ++ g.2 := by
    simpa [generated] using insertWithCode_snd g1 loc fns1.length g
  have compiled : (codeListSource loc fns newG).2 = generated.reverse ++ (ls ++ g.2) := by
    rw [codeListSource_snd_zip, ← generatedEq, oldCode]
  have perm : (ls ++ (insertWithCode g1 loc fns1.length g).2).Perm
      (codeListSource loc fns newG).2 := by
    rw [inserted, compiled]
    simpa [List.append_assoc] using (List.perm_append_comm (l₁ := ls) (l₂ := generated.reverse)).append_right g.2
  unfold stateExtends at extension ⊢
  simp only [codeListSource_fst]
  refine ⟨?_, ?_, ?_⟩
  · intro key member
    exact ⟨member, rfl⟩
  · intro key value found
    apply holALookup_of_distinct_member
    refine ⟨?_, ?_⟩
    · exact (perm.map Prod.fst).nodup_iff.mp extension.2.2
    · exact perm.mem_iff.mp (holALookup_member _ _ _ found)
  · exact (perm.map Prod.fst).nodup_iff.mp extension.2.2


end Flapjack.Compiler.Backend.ClosCall
