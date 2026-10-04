import Flapjack.HolRef
import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
import Flapjack.Compiler.Backend.BackendCommon

/-!
# `stackLang` program overloads over the exact carrier

The `While`, `move` and arithmetic instruction overloads and `list_Seq` of
`cakeml/compiler/backend/stackLangScript.sml:68-90`, stated over the exact
width-indexed `HolProg width` carrier.  The shift, constant, load and store
overloads (`stackLangScript.sml:80-84`) are in
`Flapjack/Compiler/Backend/StackRemove.lean`.  HOL `bytes_in_word` is
`wordSemBytesInWord`.
-/

namespace Flapjack.Compiler.Backend.StackLang

open Flapjack.Compiler.Encoders.Asm

/-- HOL `While` (`stackLangScript.sml:68`):
`λcmp r ri c. Loop (If cmp r ri c (Break 0))`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def whileHOL {width : Nat} [NeZero width] (cmp : HolCmp) (r : Nat) (ri : HolRegImm width)
    (c : HolProg width) : HolProg width :=
  .loop (.ite cmp r ri c (.break 0))

/-- HOL `move` (`stackLangScript.sml:70`):
`λdest src. Inst (Arith (Binop Or dest src (Reg src)))`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def moveHOL {width : Nat} [NeZero width] (dest src : Nat) : HolProg width :=
  .inst (.arith (.binop .or dest src (.reg src)))

/-- HOL `sub_1_inst` (`stackLangScript.sml:71`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def sub1Inst {width : Nat} [NeZero width] (r1 : Nat) : HolProg width :=
  .inst (.arith (.binop .sub r1 r1 (.imm (1 : BitVec width))))

/-- HOL `sub_inst` (`stackLangScript.sml:72`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def subInst {width : Nat} [NeZero width] (r1 r2 : Nat) : HolProg width :=
  .inst (.arith (.binop .sub r1 r1 (.reg r2)))

/-- HOL `add_inst` (`stackLangScript.sml:73`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def addInst {width : Nat} [NeZero width] (r1 r2 : Nat) : HolProg width :=
  .inst (.arith (.binop .add r1 r1 (.reg r2)))

/-- HOL `and_inst` (`stackLangScript.sml:74`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def andInst {width : Nat} [NeZero width] (r1 r2 : Nat) : HolProg width :=
  .inst (.arith (.binop .and r1 r1 (.reg r2)))

/-- HOL `xor_inst` (`stackLangScript.sml:75`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def xorInst {width : Nat} [NeZero width] (r1 r2 : Nat) : HolProg width :=
  .inst (.arith (.binop .xor r1 r1 (.reg r2)))

/-- HOL `add_1_inst` (`stackLangScript.sml:76`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def add1Inst {width : Nat} [NeZero width] (r1 : Nat) : HolProg width :=
  .inst (.arith (.binop .add r1 r1 (.imm (1 : BitVec width))))

/-- HOL `or_inst` (`stackLangScript.sml:77`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def orInst {width : Nat} [NeZero width] (r1 r2 : Nat) : HolProg width :=
  .inst (.arith (.binop .or r1 r1 (.reg r2)))

/-- HOL `add_bytes_in_word_inst` (`stackLangScript.sml:78`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def addBytesInWordInst {width : Nat} [NeZero width] (r1 : Nat) : HolProg width :=
  .inst (.arith (.binop .add r1 r1 (.imm wordSemBytesInWord)))

/-- HOL `div2_inst` (`stackLangScript.sml:79`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def div2Inst {width : Nat} [NeZero width] (r : Nat) : HolProg width :=
  .inst (.arith (.shift .lsr r r (.imm (1 : BitVec width))))

/-- Exact HOL `list_Seq_def` (`stackLangScript.sml:86-90`) over the exact carrier:
the generic `listSeq` at `HolProg width`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def listSeqHOL {width : Nat} [NeZero width] : List (HolProg width) → HolProg width
  | [] => .skip
  | [x] => x
  | x :: y :: xs => .seq x (listSeqHOL (y :: xs))

theorem listSeqHOL_eq_listSeq {width : Nat} [NeZero width] (xs : List (HolProg width)) :
    listSeqHOL xs = listSeq xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys => simp [listSeqHOL, listSeq, ih]

/-- Exact HOL `gc_stub_location_def` (`stackLangScript.sml:92-94`). -/
@[hol "cakeml/compiler/backend/stackLangScript.sml" "gc_stub_location_def"]
def gcStubLocation : Nat := stackNumStubs - 1

end Flapjack.Compiler.Backend.StackLang
