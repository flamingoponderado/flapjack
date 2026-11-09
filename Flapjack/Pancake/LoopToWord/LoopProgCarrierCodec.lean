module

public import Flapjack.Pancake.LoopToWord

@[expose] public section

/-!
# Width-specialized executable Loop program codec

This Flapjack-specific bridge converts executable `LoopProg (BitVec width)`
into exact `HolLoopProg width`. It is partial exactly where an executable
expression contains the extra `crepOp` or `cmp` constructors. List-backed live
sets are translated with HOL `toNumSet`; the existing executable/faithful
relation requires duplicate-free source lists. FFI names are encoded using
`MlString.ofString`, which truncates non-byte Lean characters; reverse name
equality requires the explicit `NameRanged` premise. The production route
checks the FFI byte range before using this codec and preserves the legacy
implementation for executable-only syntax.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.LoopToWord

/-- HOL `toNumSet` preserves the key-membership view of every source list,
including duplicates. -/
theorem sptLookup_toNumSetHOL_iff_mem (key : Nat) :
    ∀ live : List Nat,
      sptLookup key (Flapjack.LoopToWord.toNumSetHOL live) = some () ↔
        key ∈ live := by
  intro live
  induction live with
  | nil => simp [Flapjack.LoopToWord.toNumSetHOL]
  | cons head tail ih =>
      by_cases hkey : key = head
      · subst key
        simp [Flapjack.LoopToWord.toNumSetHOL,
          sptLookup_sptInsert_same]
      · simp [Flapjack.LoopToWord.toNumSetHOL,
          sptLookup_sptInsert_ne, hkey, ih]

/-- Duplicate-free source live sets satisfy the existing executable/faithful
representation relation after `toNumSet` conversion. -/
theorem numSetListRel_toNumSetHOL {live : List Nat} (hnodup : live.Nodup) :
    numSetListRel live (Flapjack.LoopToWord.toNumSetHOL live) := by
  refine ⟨hnodup, ?_⟩
  intro key
  exact sptLookup_toNumSetHOL_iff_mem key live

end Flapjack
