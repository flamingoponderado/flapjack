import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Allocator
import Flapjack.Compiler.Backend.LinearScan.TopLevel

/-!
# word_alloc register-allocator dispatcher

Literal port of `word_allocScript.sml:1697-1703`, `select_reg_alloc`: algorithms
from 4 on run the linear-scan allocator, lower algorithms the graph-colouring
allocator (`Simple` for 0 and 1, `IRC` otherwise). Proof-side port; the
executed compiler's allocator routing remains separate work.
-/

namespace Flapjack.WordAlloc

open Flapjack Flapjack.RegAlloc

/-- Literal `select_reg_alloc` (`word_allocScript.sml:1697-1703`). -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "select_reg_alloc_def"]
def selectRegAlloc (alg : Nat) (spillcosts : Option (Spt Nat)) (k : Nat)
    (heu_moves : List (Nat × (Nat × Nat))) (tree : ClashTree) (forced : List (Nat × Nat))
    (fs : NumSet) : Translator.Monadic.MonadBase.Exc (Spt Nat) StateException :=
  if 4 ≤ alg then LinearScan.linearScanRegAlloc k heu_moves tree forced
  else regAlloc (if alg ≤ 1 then .Simple else .IRC) spillcosts k heu_moves tree forced fs

end Flapjack.WordAlloc
