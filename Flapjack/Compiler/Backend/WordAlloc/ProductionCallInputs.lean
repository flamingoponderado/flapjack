import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorSetWF

namespace Flapjack.WordAlloc

/-! Independent Call input normalization. Original sparse-map insertion and
actual list concatenation represent the same unit-valued input map. These are
untagged implementation lemmas, without independent HOL declarations or any
assumption about the desired clash-tree output. -/

private theorem toNumSet_wf (names : List Nat) :
    sptWf (LoopToWord.toNumSetHOL names) = true := by
  induction names with
  | nil => rfl
  | cons name names ih => exact sptWfInsert _ _ _ ih

/-- Full original return-value insertion equals union with its canonical
source list, for arbitrary well-formed cutsets and overlapping names. -/
theorem callReturnInsertion_union (names : List Nat) (cutset : NumSet)
    (wellFormed : sptWf cutset = true) :
    numsetListInsert names cutset = sptUnion (LoopToWord.toNumSetHOL names) cutset := by
  induction names with
  | nil =>
      apply (sptEqThm _ _ ⟨wellFormed,
        sptWfUnion _ _ ⟨toNumSet_wf [], wellFormed⟩⟩).mpr
      intro key
      simp only [LoopToWord.toNumSetHOL, sptLookup_sptUnion, sptLookup]
  | cons name names ih =>
      apply (sptEqThm _ _ ⟨numsetListInsert_setsWf _ _ wellFormed,
        sptWfUnion _ _ ⟨toNumSet_wf _, wellFormed⟩⟩).mpr
      intro key
      by_cases equal : key = name
      · subst key
        simp only [numsetListInsert, LoopToWord.toNumSetHOL,
          sptLookup_sptInsert_same, sptLookup_sptUnion]
      · simp only [numsetListInsert, LoopToWord.toNumSetHOL,
          sptLookup_sptInsert_ne name key () _ equal, ih, sptLookup_sptUnion]

/-- Concatenating the original return-value list with a represented cutset is
exactly original recursive insertion. Duplicate keys are intentionally kept
in the input list and collapse through the native unit map. -/
theorem callReturnInsertion_append (names cutsetNames : List Nat) :
    numsetListInsert names (LoopToWord.toNumSetHOL cutsetNames) =
      LoopToWord.toNumSetHOL (names ++ cutsetNames) := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [numsetListInsert, List.cons_append, LoopToWord.toNumSetHOL, ih]

/-- The handler's exception insertion retains its original key and every
cutset entry, including a pre-existing exception key. -/
theorem callExceptionInsertion_cons (exception : Nat) (cutsetNames : List Nat) :
    sptInsert exception () (LoopToWord.toNumSetHOL cutsetNames) =
      LoopToWord.toNumSetHOL (exception :: cutsetNames) := rfl

end Flapjack.WordAlloc
