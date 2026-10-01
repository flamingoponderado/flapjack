import Flapjack.Compiler.Backend.WordToStack.ProductionSsaCodecDomain

/-! Exact same-input kernel replay of eight fresh original full SSA equations.
Separate domain sentinels exercise the production-only five-register primitive
and nested Call/loop rejection. The universal proofs do not assume codec
success or a desired output. -/
namespace Flapjack.Test.WordToStackSsaCodecParity
open Flapjack

private def rows : List Bool :=
  [match (wordFullSsaCcTrans 2 (.skip : WordProg (BitVec 8))).2.2 with
   | .seq (.move 1 [(5,0),(9,2)]) .skip => true
   | _ => false,
   match (wordFullSsaCcTrans 2 (.seq (.assign 0 (.const 0)) (.assign 2 (.var 0)) : WordProg (BitVec 8))).2.2 with
   | .seq (.move 1 [(5,0),(9,2)]) (.seq (.assign 13 (.const 0)) (.assign 17 (.var 13))) => true
   | _ => false,
   match (wordFullSsaCcTrans 0 (.inst (.const 1 7) : WordProg (BitVec 8))).2.2 with
   | .seq (.move 1 []) (.inst (.const 5 7)) => true
   | _ => false,
   match (wordFullSsaCcTrans 0 (.inst (.arith (.shift .lsl 1 2 (.reg 3))) : WordProg (BitVec 8))).2.2 with
   | .seq (.move 1 []) (.seq (.move 1 [(8,0)]) (.inst (.arith (.shift .lsl 5 0 (.reg 8))))) => true
   | _ => false,
   match (wordFullSsaCcTrans 0 (.inst (.arith (.longMul 1 2 3 4)) : WordProg (BitVec 8))).2.2 with
   | .seq (.move 1 []) (.seq (.move 1 [(0,0),(4,0)])
       (.seq (.inst (.arith (.longMul 6 0 0 4))) (.move 1 [(13,0),(9,6)]))) => true
   | _ => false,
   match (wordFullSsaCcTrans 2 (.raise 2 : WordProg (BitVec 8))).2.2 with
   | .seq (.move 1 [(5,0),(9,2)]) (.seq (.move 1 [(2,9)]) (.raise 2)) => true
   | _ => false,
   match (wordFullSsaCcTrans 2 (.call none (some 7) [0,2] none : WordProg (BitVec 8))).2.2 with
   | .seq (.move 1 [(5,0),(9,2)]) (.seq (.move 1 [(0,5),(2,9)]) (.call none (some 7) [0,2] none)) => true
   | _ => false,
   match (wordFullSsaCcTrans 3 (.return 0 [2,4] : WordProg (BitVec 8))).2.2 with
   | .seq (.move 1 [(9,0),(13,2),(17,4)]) (.seq (.move 0 [(2,13),(4,17)]) (.return 9 [2,4])) => true
   | _ => false]

example : rows = [true,true,true,true,true,true,true,true] := by
  simp only [rows, wordFullSsaCcTrans, wordSsaRenameFunctionWithEntry,
    wordSsaRenameFunction, wordSsaSetupParameters, wordSsaLimitVar,
    wordProgCakeMaxVar, wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaAbiParameters, wordSsaEntryMove, wordSsaFresh,
    wordSsaRenameInstProgram, wordSsaRenameInst, wordSsaRead,
    wordSsaReadMoveSource, wordSsaRenameExp, wordExpCakeMaxVar,
    wordInstCakeMaxVar, wordArithCakeMaxVar, wordSsaCallAbiRegisters, wordSsaSeq]
  decide +kernel

private def fiveCarry : WordProg (BitVec 8) := .inst (.arith (.addCarry 1 2 3 4 5))
private def domains : List (WordProg (BitVec 8)) :=
  [.skip, .inst (.arith (.cakeAddCarry 1 2 3 4)),
   .inst (.memOffset .load16 3 5 7), fiveCarry,
   .call none none [] (some (1,fiveCarry,2,3)),
   .call (some ([],([],[]),fiveCarry,2,3)) none [] none,
   .call (some ([],([],[]),.skip,2,3)) none [] (some (1,fiveCarry,4,5)),
   .loop [] (.mustTerminate fiveCarry) [],
   .ite .equal 1 (.imm 0) .skip (.inst (.const 2 7))]

example : domains.map (fun program =>
    (wordLangProgToHOL (wordFullSsaCcTrans 3 program).2.2).isSome) =
    [true,true,true,false,false,false,false,false,true] := by
  simp only [wordLangProgToHOL_wordFullSsaCcTrans_isSome]
  decide +kernel

example {width : Nat} (frames : List WordSsaLoopFrame) (state : WordSsaState)
    (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordSsaRenameProgramWithLoops frames state program).2).isSome =
      (wordLangProgToHOL program).isSome :=
  wordLangProgToHOL_wordSsaRenameProgramWithLoops_isSome frames state program

example {width : Nat} (parameterCount : Nat) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL (wordFullSsaCcTrans parameterCount program).2.2).isSome =
      (wordLangProgToHOL program).isSome := wordLangProgToHOL_wordFullSsaCcTrans_isSome parameterCount program

end Flapjack.Test.WordToStackSsaCodecParity
