module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Restriction

@[expose] public section

/-! Rearrangement of roots and source values in the abstract heap invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- A member of a paired word stack has an aligned abstract root with the
same decoded word. This is Flapjack list infrastructure. -/
theorem pairedRoot_exists {α β γ : Type} (decode : γ → β) (xs : List (α × β)) (roots : List γ)
    (related : List.Forall₂ (fun root word => decode root = word) roots (xs.map Prod.snd)) :
    ∀ pair, pair ∈ xs → ∃ root, (pair.1, root) ∈ (xs.map Prod.fst).zip roots ∧ decode root = pair.2 := by
  induction xs generalizing roots with
  | nil => intro pair member; simp at member
  | cons head tail ih =>
      cases roots with
      | nil => cases related
      | cons root rest =>
          simp only [List.map_cons] at related
          cases related with
          | cons decoded remainder =>
            intro pair member
            rcases List.mem_cons.mp member with equal | inTail
            · subst pair
              exact ⟨root, by simp, decoded⟩
            · obtain ⟨chosen, fromTail, equation⟩ := ih rest remainder pair inTail
              refine ⟨chosen, ?_, equation⟩
              simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]
              exact Or.inr fromTail

/-- Select roots for a list of word pairs while preserving membership in an
original list of value/root pairs. This is Flapjack list infrastructure. -/
theorem selectPairedRoots {α β γ : Type} (decode : γ → β) (ys : List (α × β))
    (source : List (α × γ))
    (available : ∀ pair, pair ∈ ys → ∃ root, (pair.1, root) ∈ source ∧ decode root = pair.2) :
    ∃ selected : List (α × γ), selected.map Prod.fst = ys.map Prod.fst ∧
      List.Forall₂ (fun root word => decode root = word) (selected.map Prod.snd) (ys.map Prod.snd) ∧
      ∀ pair, pair ∈ selected → pair ∈ source := by
  induction ys with
  | nil => exact ⟨[], rfl, .nil, by simp⟩
  | cons head tail ih =>
      obtain ⟨root, rootInSource, equation⟩ := available head (by simp)
      obtain ⟨selected, firsts, related, contained⟩ :=
        ih (fun pair member => available pair (List.mem_cons_of_mem head member))
      refine ⟨(head.1, root) :: selected, ?_, ?_, ?_⟩
      · simp [firsts]
      · exact .cons equation related
      · intro pair member
        rcases List.mem_cons.mp member with equal | inTail
        · subst pair
          exact rootInSource
        · exact contained pair inTail

/-- Restricting the paired stack prefix preserves the abstract heap invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "abs_ml_inv_stack_permute"
  (words_as_type_indexed_bitvec)]
theorem absMlInv_stackPermute {width : Nat} [NeZero width] (conf : Config)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat)
    (xs ys : List (Flapjack.Compiler.Backend.DataSem.Value × HeapAddress (WordLocW width))) :
    absMlInv conf (xs.map Prod.fst ++ stack) refs
      (xs.map Prod.snd ++ roots, heap, bigEndian, a, sp, sp1, gens) limit next ∧
      (∀ pair, pair ∈ ys → pair ∈ xs) →
    absMlInv conf (ys.map Prod.fst ++ stack) refs
      (ys.map Prod.snd ++ roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  rintro ⟨invariant, subset⟩
  dsimp [absMlInv] at invariant ⊢
  obtain ⟨rootOk, heapOk', gc, unused, stackInv⟩ := invariant
  refine ⟨?_, heapOk', gc, unused, ?_⟩
  · intro ptr value member
    exact rootOk ptr value (mapAppend_subset Prod.snd ys xs roots subset _ member)
  · dsimp [bcStackRefInv] at stackInv ⊢
    obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimestamps, tfBound, endian, unique, values, cells⟩ := stackInv
    let newStack := ys.map Prod.fst ++ stack
    let newTf := restrictTimestampMap tf (allTimestamps refs newStack)
    refine ⟨f, newTf, fInj, fDomain, ?_, ?_, ?_, endian, ?_, ?_, ?_⟩
    · exact mapInjInto_restrict tf (allTimestamps refs newStack) _ tfInj
    · intro stamp domain
      exact ((mapDomain_restrict tf (allTimestamps refs newStack) stamp).mp domain).1
    · intro stamp domain
      exact tfBound stamp ((mapDomain_restrict tf (allTimestamps refs newStack) stamp).mp domain).2
    · exact blocksUnique_stackPermute ys xs next refs stack ⟨subset, unique⟩
    · obtain ⟨pairwise, suffix⟩ := forall2_pairPrefix_split
        (fun value addr => valueInv conf value refs (addr, f, tf, heap)) xs stack roots values
      apply forall2_pairPrefix_build
      · intro pair member
        apply valueInv_tfRestrict conf pair.1 refs newStack pair.2 f tf heap (allTimestamps refs newStack)
        refine ⟨pairwise pair (subset pair member), ?_, fun _ h => h⟩
        intro ts timestamp
        apply mem_allTimestamps pair.1 ts newStack refs
        refine ⟨mem_stack_allValues pair.1 newStack refs ?_, timestamp⟩
        exact List.mem_append_left _ (List.mem_map.mpr ⟨pair, member, rfl⟩)
      · apply forall2_imp_member suffix
        intro value addr member related
        apply valueInv_tfRestrict conf value refs newStack addr f tf heap (allTimestamps refs newStack)
        refine ⟨related, ?_, fun _ h => h⟩
        intro ts timestamp
        apply mem_allTimestamps value ts newStack refs
        exact ⟨mem_stack_allValues value newStack refs (List.mem_append_right _ member), timestamp⟩
    · intro n condition
      have previous : reachableRefs (xs.map Prod.fst ++ stack) refs n :=
        reachableRefs_stackSubset _ _ refs n
          ⟨condition.1, mapAppend_subset Prod.fst ys xs stack subset⟩
      exact bcRefInv_restrict conf n refs f tf heap bigEndian newStack (cells n ⟨previous, condition.2⟩)

/-- Restricting or reordering a word stack preserves its abstract invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_ml_inv_rearrange"
  (words_as_type_indexed_bitvec)]
theorem wordMlInv_rearrange {width : Nat} [NeZero width] (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat) (conf : Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (xs ys : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    (∀ pair, pair ∈ ys → pair ∈ xs) →
    wordMlInv (heap, bigEndian, a, sp, sp1, gens) limit next conf refs xs →
    wordMlInv (heap, bigEndian, a, sp, sp1, gens) limit next conf refs ys := by
  intro subset related
  dsimp [wordMlInv] at related ⊢
  obtain ⟨roots, abstractInv, addresses⟩ := related
  have lengths : (xs.map Prod.fst).length = roots.length := by
    simpa using addresses.length_eq.symm
  let oldPairs := (xs.map Prod.fst).zip roots
  have oldFirst : oldPairs.map Prod.fst = xs.map Prod.fst := by
    exact List.map_fst_zip (Nat.le_of_eq lengths)
  have oldSecond : oldPairs.map Prod.snd = roots := by
    exact List.map_snd_zip (Nat.le_of_eq lengths.symm)
  have oldAbstract : absMlInv conf (oldPairs.map Prod.fst ++ []) refs
      (oldPairs.map Prod.snd ++ [], heap, bigEndian, a, sp, sp1, gens) limit next := by
    simpa only [List.append_nil, oldFirst, oldSecond] using abstractInv
  have available : ∀ pair, pair ∈ ys →
      ∃ root, (pair.1, root) ∈ oldPairs ∧ wordAddr conf root = pair.2 := by
    intro pair member
    exact pairedRoot_exists (wordAddr conf) xs roots addresses pair (subset pair member)
  obtain ⟨selected, firsts, selectedAddresses, contained⟩ :=
    selectPairedRoots (wordAddr conf) ys oldPairs available
  have selectedAbstract := absMlInv_stackPermute conf [] refs [] heap bigEndian a sp sp1 gens limit next
    oldPairs selected ⟨oldAbstract, contained⟩
  refine ⟨selected.map Prod.snd, ?_, selectedAddresses⟩
  simpa only [List.append_nil, firsts] using selectedAbstract

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
