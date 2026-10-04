import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.SelectRegAlloc
import Flapjack.Compiler.Backend.WordAlloc.OracleColour
import Flapjack.Compiler.Backend.WordAlloc.GetHeuristics
import Flapjack.Compiler.Backend.WordAlloc.GetStackOnly
import Flapjack.Compiler.Backend.WordAlloc.GetForced

/-!
# word_alloc

Literal port of `word_allocScript.sml:1791-1807`, `word_alloc`: build the clash tree, the
stack-only set and the forced edges of a program; use the oracle colouring when
`oracle_colour_ok` accepts it, otherwise compute heuristics, run `select_reg_alloc` and
apply the total colouring, returning the original program if the allocator fails.
-/

namespace Flapjack.WordAlloc

open Flapjack Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `word_alloc_def` (`word_allocScript.sml:1791-1807`). The `let`s, the oracle
`case` and the allocator result `case` are literal, including the `M_failure _ => prog`
fallback. The sole carrier translation is HOL's type-indexed `'a word` and
`'a asm_config` to `BitVec width` and `AsmConfigExact width`, with HOL's positive dimension
discharged by `[NeZero width]`. This proof-side port does not replace the executed RISC-V
word allocator yet. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def wordAlloc {width : Nat} [NeZero width] (fc : Nat) (c : AsmConfigExact width) (alg k : Nat)
    (prog : WordLangProgHOL (BitVec width)) (col_opt : Option (Spt Nat)) :
    WordLangProgHOL (BitVec width) :=
  let tree := getClashTree prog []
  let fs := getStackOnly prog
  let forced := getForced c prog []
  match oracleColourOk k col_opt tree prog forced with
  | none =>
    let (heu_moves, spillcosts) := getHeuristics alg fc prog
    match selectRegAlloc alg spillcosts k heu_moves tree forced fs with
    | .success col => applyColour (totalColour col) prog
    | .failure _ => prog
  | some col_prog => col_prog

end Flapjack.WordAlloc
