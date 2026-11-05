import Flapjack.Pancake.LoopToWord

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

end Flapjack
