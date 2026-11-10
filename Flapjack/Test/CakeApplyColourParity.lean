module

public import Flapjack.RiscV.OracleAllocator
public import Flapjack.Compiler.Backend.WordUnreach
public import Flapjack.RiscV.CakeRegAlloc
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

@[expose] public section

/-! Direct HOL parity for CakeML `total_colour` followed by `apply_colour`.
    The source fixture is `scripts/hol-probes/apply_colour_probe.out`. -/

namespace Flapjack.Test.CakeApplyColourParity

open Flapjack

def oracle : NatInfoMap Nat := [(1, 7), (3, 9)]

def aliasColour (name : Nat) : Nat := if name = 0 then 0 else 1

/-- Nine original get_live_inst EVAL rows, including the 16-bit catchall,
output deletion order, four-register carry, and both FP word dimensions.
The shared production instruction cases are replayed below as well. -/
def instructionLivenessExact : Bool :=
  let live : NumSet := sptFromAList [(1, ()), (2, ()), (3, ()), (4, ()), (9, ())]
  let keys {width : Nat} [NeZero width] (inst : WordLangInst (BitVec width)) :=
    (sptToAList (WordAlloc.getLiveInst inst live)).map Prod.fst
  keys (.mem .load16 3 (.addr 5 7) : WordLangInst (BitVec 8)) == [3, 1, 9, 4, 2] &&
    keys (.mem .load8 3 (.addr 5 7) : WordLangInst (BitVec 8)) == [1, 9, 5, 4, 2] &&
    keys (.mem .store32 3 (.addr 5 7) : WordLangInst (BitVec 8)) == [3, 1, 9, 5, 4, 2] &&
    keys (.arith (.addCarry 1 2 3 4) : WordLangInst (BitVec 8)) == [3, 9, 4, 2] &&
    keys (.arith (.addOverflow 1 2 3 4) : WordLangInst (BitVec 8)) == [3, 9, 2] &&
    keys (.fp (.fpMovToReg 1 2 3) : WordLangInst (BitVec 64)) == [3, 9, 4, 2] &&
    keys (.fp (.fpMovToReg 1 2 3) : WordLangInst (BitVec 32)) == [3, 9, 4] &&
    keys (.fp (.fpMovFromReg 1 6 7) : WordLangInst (BitVec 64)) == [3, 1, 9, 4, 2, 6] &&
    keys (.fp (.fpMovFromReg 1 6 7) : WordLangInst (BitVec 32)) == [7, 3, 1, 9, 4, 2, 6]

example : instructionLivenessExact = true := by
  simp [instructionLivenessExact, WordAlloc.getLiveInst, WordAlloc.getLiveInstCore,
    sptToAList, sptFoldi, lrNext, sptFromAList, sptInsert, sptDelete, sptMkBS, sptMkBN]

end Flapjack.Test.CakeApplyColourParity
