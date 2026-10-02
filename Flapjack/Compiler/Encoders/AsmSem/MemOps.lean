import Flapjack.Compiler.Encoders.AsmSem.Memory
import Flapjack.Misc.Alignment

/-!
# asmSem generic memory wrappers

Ports of `mem_load_def`, `mem_store_def` and `mem_op_def` (`asmSemScript.sml:191-223`) over the
reviewed `addr`, `read_mem_word`, `write_mem_word`, `upd_reg`, `read_reg` and `assert` ports.
The byte count `n` is arbitrary, including `0`, and the alignment guard is the exact
`aligned (LOG2 n)` over the specified `LOG2`. `aligned (LOG2 0) a` therefore keeps HOL's
unconstrained `LOG2 0`, and the whole-word `mem_op` count `dimindex DIV 8` is `0` at widths below 8.
In `mem_load` the read result has the state's word width (it feeds `upd_reg`); in `mem_store`
the written value is the register word.
-/

namespace Flapjack.Compiler.Encoders.AsmSem
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `mem_load_def` (`asmSemScript.sml:191-197`). -/
@[hol "cakeml/compiler/encoders/asm/asmSemScript.sml" "mem_load_def" (words_as_type_indexed_bitvec)]
noncomputable def memLoad {width : Nat} [NeZero width] (n r : Nat) (a : HolAddr width)
    (s : AsmState width) : AsmState width :=
  let a := addrHOL a s
  let (w, s) := readMemWord (resultWidth := width)
    (if s.be then a + BitVec.ofNat width (n - 1) else a) n s
  let s := updReg r w s
  assertState (holAligned (holLOG2 n) a) s

/-- Exact HOL `mem_store_def` (`asmSemScript.sml:206-212`). -/
@[hol "cakeml/compiler/encoders/asm/asmSemScript.sml" "mem_store_def" (words_as_type_indexed_bitvec)]
noncomputable def memStore {width : Nat} [NeZero width] (n r : Nat) (a : HolAddr width)
    (s : AsmState width) : AsmState width :=
  let a := addrHOL a s
  let w := readReg r s
  let s := writeMemWord (valueWidth := width)
    (if s.be then a + BitVec.ofNat width (n - 1) else a) n w s
  assertState (holAligned (holLOG2 n) a) s

/-- Exact HOL `mem_op_def` (`asmSemScript.sml:214-223`), all eight clauses; the whole-word
count is `dimindex (:'a) DIV 8`. -/
@[hol "cakeml/compiler/encoders/asm/asmSemScript.sml" "mem_op_def" (words_as_type_indexed_bitvec)]
noncomputable def memOp {width : Nat} [NeZero width] :
    HolMemop → Nat → HolAddr width → AsmState width → AsmState width
  | .load, r, a => memLoad (width / 8) r a
  | .store, r, a => memStore (width / 8) r a
  | .load8, r, a => memLoad 1 r a
  | .store8, r, a => memStore 1 r a
  | .load16, r, a => memLoad 2 r a
  | .store16, r, a => memStore 2 r a
  | .load32, r, a => memLoad 4 r a
  | .store32, r, a => memStore 4 r a

end Flapjack.Compiler.Encoders.AsmSem
