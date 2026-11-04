import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanLang.Decl

/-!
Byte-range preservation facts for the executable `pan_simp` transform.
These are Flapjack-specific representation invariants, not HOL correctness
theorems: the rewrites reassociate sequences and move existing names and
expressions without changing their character data.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

theorem smartSeq_byteRanged {width : Nat} (pre program : Prog (BitVec width))
    (hpre : ProgByteRanged pre) (hprogram : ProgByteRanged program) :
    ProgByteRanged (smartSeq pre program) := by
  fun_cases smartSeq pre program with
  | case1 => exact hprogram
  | case2 => exact ⟨hpre, hprogram⟩

theorem seqCallRet_byteRanged {width : Nat} (program : Prog (BitVec width))
    (h : ProgByteRanged program) : ProgByteRanged (seqCallRet program) := by
  unfold seqCallRet
  split
  · split
    · exact ⟨h.1.1, h.1.2.1, trivial⟩
    · exact h
  · exact h

end Flapjack
