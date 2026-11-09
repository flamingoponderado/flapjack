import Flapjack.Compiler.Backend.WordGcFunctions

/-! Replay the original collector copy with independent word widths and a
natural-valued memory, from `word_gc_functions_probe.out`. -/
namespace Flapjack.Test.MemcpyParity
open Flapjack.Compiler.Backend.WordGcFunctions

example :
    (let (b, m, c) := memcpy (2 : BitVec 8) (16 : BitVec 64) (32 : BitVec 64)
      (fun w => if w = 16 then 7 else if w = 24 then 9 else 0 : BitVec 64 → Nat)
      (fun _ => true)
    (b, m 32, m 40, c)) = ((48 : BitVec 64), 7, 9, true) := by
  simp [memcpy, gcUpdate, Flapjack.wordSemBytesInWord]

end Flapjack.Test.MemcpyParity
