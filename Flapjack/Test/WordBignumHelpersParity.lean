import Flapjack.Compiler.Backend.WordBignum.Helpers

/-! Replay the pinned HOL bignum helper probe. -/
namespace Flapjack.Test.WordBignumHelpersParity
open Flapjack Flapjack.Compiler.Backend.WordBignum

private abbrev P := WordLangProgHOL (BitVec 64)

#guard match seqTemp 7 33 (.skip : P) with
  | .seq (.assign 7 (.lookup (.temp n))) .skip => n == 1
  | _ => false

#guard match seqTempImmNot 4 (.reg 33) (.skip : P) with
  | .seq (.assign 4 (.lookup (.temp n)))
      (.seq (.assign 4 (.op .xor [.var 4, .const w])) .skip) =>
      n == 1 && w == (~~~(0 : BitVec 64))
  | _ => false

#guard match seqTempImmNot 4 (.imm 5) (.skip : P) with
  | .seq (.assign 4 (.const w)) .skip => w == (~~~(5 : BitVec 64))
  | _ => false

#guard match loadRegs [0, 33] (.skip : P) with
  | .seq (.get 2 (.temp a)) (.seq (.get 35 (.temp b)) .skip) => a == 0 && b == 1
  | _ => false

#guard match (saveRegs [0, 33] : P) with
  | .seq (.set (.temp a) (.var 2)) (.seq (.set (.temp b) (.var 35)) .skip) =>
      a == 0 && b == 1
  | _ => false

#guard match seqIndex 3 33 .in2 (.skip : WordLangProgHOL (BitVec 32)) with
  | .seq (.assign 3 (.op .add [.lookup (.temp base),
      .shift .lsl (.lookup (.temp index)) (.const shift)])) .skip =>
      base == 30 && index == 1 && shift == 2
  | _ => false

#guard match seqIndex 3 33 .out (.skip : P) with
  | .seq (.assign 3 (.op .add [.lookup (.temp base),
      .shift .lsl (.lookup (.temp index)) (.const shift)])) .skip =>
      base == 29 && index == 1 && shift == 3
  | _ => false

#guard match (divCode 1 2 3 4 5 6 7 : P) with
  | .mustTerminate (.seq (.call (some ([3], (.ls (), .ln), .skip, 1, 2))
      (some 23) [5, 6, 7] none) (.assign 4 (.lookup (.temp temp)))) => temp == 28
  | _ => false

end Flapjack.Test.WordBignumHelpersParity
