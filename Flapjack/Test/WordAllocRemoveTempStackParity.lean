import Flapjack.Compiler.Backend.WordAlloc.StackOnly

namespace Flapjack.Test.WordAllocRemoveTempStackParity
open Flapjack Flapjack.WordAlloc

-- rts_empty=T
example : removeTempStack ([] : List Nat) ((.ln : Spt Unit), (.ln : Spt Unit)) = (.ln, .ln) := by rfl
-- rts_zero=T
example : removeTempStack [0] (sptFromAList [(0,()),(2,())], (.ln : Spt Unit)) =
    (sptFromAList [(2,())], .ln) := by simp [removeTempStack, sptFromAList, sptInsert, sptDelete]
-- rts_duplicate=T
example : removeTempStack [2,2] (sptFromAList [(0,()),(2,())], (.ln : Spt Unit)) =
    (.ls (), .ln) := by simp [removeTempStack, sptFromAList, sptInsert, sptDelete, sptMkBS]
-- rts_missing=T
example : removeTempStack [99] ((.ls () : Spt Unit), (.ls () : Spt Unit)) = (.ls (), .ls ()) := by simp [removeTempStack, sptDelete]
-- rts_fixed=T
example : removeTempStack [0,2] (sptFromAList [(0,()),(2,())], sptFromAList [(0,()),(2,())]) =
    (.ln, sptFromAList [(0,()),(2,())]) := by simp [removeTempStack, sptFromAList, sptInsert, sptDelete, sptMkBS]
-- rts_raw=T
example : removeTempStack [0] ((.bn .ln .ln : Spt Unit), (.bn .ln .ln : Spt Unit)) =
    (.bn .ln .ln, .bn .ln .ln) := by simp [removeTempStack, sptDelete]

-- rts_generic_payload=T
example : removeTempStack [0] ((.ls 7 : Spt Nat), (42 : Nat)) = (.ln,42) := by decide
-- rts_generic_fixed=T
example : removeTempStack [99] ((.ls () : Spt Unit), true) = (.ls (),true) := by decide

-- HOL generalizes both payload and untouched component, beyond allocator use.
example (keys : List Nat) (tree : Spt Nat) (fixed : String) :
    (removeTempStack keys (tree, fixed)).2 = fixed := rfl

end Flapjack.Test.WordAllocRemoveTempStackParity
