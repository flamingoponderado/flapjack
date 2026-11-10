module

public import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorSetWF

@[expose] public section

namespace Flapjack.WordAlloc

private theorem numSetCodec_wf (keys : List Nat) :
    sptWf (LoopToWord.toNumSetHOL keys) = true := by
  induction keys with
  | nil => rfl
  | cons key keys ih => exact sptWfInsert _ _ _ ih

/-- Canonical native sparse trees are fixed by the actual list-backed cutset
codec. Lookup preservation alone is insufficient for malformed tree shapes;
the original canonical-tree invariant supplies the genuine identity domain.
This is Flapjack codec infrastructure without a separate HOL original. -/
theorem canonicalNumSet_codec (tree : Spt Unit) (valid : sptWf tree = true) :
    LoopToWord.toNumSetHOL (LoopToWord.fromNumSetHOL tree) = tree := by
  apply (sptEqThm _ _ ⟨numSetCodec_wf _, valid⟩).2
  exact toNumSet_fromNumSet_lookup tree

end Flapjack.WordAlloc
