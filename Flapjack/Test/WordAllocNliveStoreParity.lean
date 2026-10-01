import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
namespace Flapjack.Test.WordAllocNliveStoreParity
open Flapjack Flapjack.WordAlloc

/-! Kernel replay of `scripts/hol-probes/word_alloc_nlive_store_probe.out`: original
HOL `nlive_store` rows (`T` proved, `F` refuted). -/

abbrev E := WordLangExpHOL (BitVec 64)

-- ns_lookup_dead=F
example : ¬ nliveStore [.nextFree] (.lookup .nextFree : E) := by simp [nliveStore]
-- ns_lookup_live=T
example : nliveStore [.nextFree] (.lookup .endOfHeap : E) := by simp [nliveStore]
-- ns_var=T
example : nliveStore [.nextFree] (.var 3 : E) := by simp [nliveStore]
-- ns_const=T
example : nliveStore [] (.const 7 : E) := by simp [nliveStore]
-- ns_op_dead=F
example : ¬ nliveStore [.nextFree] (.op .add [.var 1, .lookup .nextFree] : E) := by
  simp [nliveStore]
-- ns_op_live=T
example : nliveStore [.nextFree] (.op .add [.var 1, .lookup .currHeap] : E) := by
  simp [nliveStore]
-- ns_op_empty=T
example : nliveStore [.nextFree] (.op .add [] : E) := by simp [nliveStore]
-- ns_load=T
example : nliveStore [.nextFree] (.load (.lookup .endOfHeap) : E) := by simp [nliveStore]
-- ns_load_dead=F
example : ¬ nliveStore [.endOfHeap, .nextFree] (.load (.lookup .endOfHeap) : E) := by
  simp [nliveStore]
-- ns_shift_left_dead=F
example : ¬ nliveStore [.nextFree] (.shift .lsl (.lookup .nextFree) (.const 1) : E) := by
  simp [nliveStore]
-- ns_shift_right_dead=F
example : ¬ nliveStore [.nextFree] (.shift .lsl (.var 2) (.lookup .nextFree) : E) := by
  simp [nliveStore]
-- ns_shift_live=T
example : nliveStore [] (.shift .asr (.lookup .nextFree) (.var 4) : E) := by simp [nliveStore]

end Flapjack.Test.WordAllocNliveStoreParity
