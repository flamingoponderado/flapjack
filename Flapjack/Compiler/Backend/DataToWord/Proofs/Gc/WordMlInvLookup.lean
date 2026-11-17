module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute

@[expose] public section

/-! Local lookup in the data-to-word word/ML invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A source local and its adjusted word local may be duplicated among the
roots of the word/ML invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_ml_inv_lookup"
  (words_as_type_indexed_bitvec)]
theorem wordMlInv_lookup {width : Nat} [NeZero width]
    (heap : ValueHeap width) (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (limit next : Nat) (conf : Config) (refs : Spt (BvlSem.Ref DataSem.Value))
    (ys xs : List (DataSem.Value × WordLocW width))
    (source : Spt DataSem.Value) (target : Spt (WordLocW width))
    (n : Nat) (value : DataSem.Value) (word : WordLocW width)
    (premises :
      wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
        (ys ++ joinEnv source (sptToAList (sptInter target (adjustSet source))) ++ xs) ∧
      sptLookup n source = some value ∧ sptLookup (adjustVar n) target = some word) :
    wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      (ys ++ [(value, word)] ++ joinEnv source (sptToAList (sptInter target (adjustSet source))) ++ xs) := by
  obtain ⟨invariant, sourceFound, targetFound⟩ := premises
  have adjustedFound : sptLookup (adjustVar n) (adjustSet source) = some () := by
    rw [lookup_adjustSet_map, sourceFound]
    rfl
  have entry : (adjustVar n, word) ∈ sptToAList (sptInter target (adjustSet source)) := by
    apply (sptMemToAList _ _ _).mpr
    rw [sptLookup_sptInterCases, targetFound, adjustedFound]
  have keyProperties : adjustVar n ≠ 0 ∧ adjustVar n % 2 = 0 := by
    simp [adjustVar]
  have index : (adjustVar n - 2) / 2 = n := by
    simp [adjustVar]
  have member : (value, word) ∈ joinEnv source (sptToAList (sptInter target (adjustSet source))) := by
    simp only [joinEnv, List.mem_map, List.mem_filter]
    refine ⟨(adjustVar n, word), ⟨entry, ?_⟩, ?_⟩
    · simpa using keyProperties
    · simp [index, sourceFound, holThe]
  apply wordMlInv_rearrange heap be a sp sp1 gens limit next conf refs _ _ ?_ invariant
  intro pair inNew
  simp only [List.mem_append, List.mem_singleton] at inNew ⊢
  rcases inNew with ((inYs | same) | inJoin) | inXs
  · exact Or.inl (Or.inl inYs)
  · subst pair
    exact Or.inl (Or.inr member)
  · exact Or.inl (Or.inr inJoin)
  · exact Or.inr inXs

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
