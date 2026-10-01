import Flapjack.Compiler.Backend.WordToStack.ProductionProgramMaximum

/-! Same-input kernel replay of fresh original full-program maxima. Every
production constructor is covered, with recursive Call forms, duplicate
cutsets, Return's nonzero accumulator and names above 2^80. Rejection and
ordinary 16-bit guard sentinels are independent of the accepted rows. -/
namespace Flapjack.Test.WordToStackProgramMaximumParity
open Flapjack

private def inputs : List (WordProg (BitVec 8)) :=
  [.skip, .tick,
   .move 2 [(3,7),(11,5)],
   .assign 9 (.op .add [.var 3,.const 7]),
   .inst (.arith (.binOp .add 3 11 (.reg 17))),
   .get 17 .currHeap, .store (.var 17) 3, .set .currHeap (.var 17),
   .seq (.assign 1 (.var 8)) (.raise 17),
   .ite .equal 3 (.reg 17) (.raise 5) (.get 11 .currHeap),
   .ite .equal 3 (.imm 99) (.raise 5) (.get 11 .currHeap),
   .loop [3,3,17] (.raise 11) [5,2],
   .mustTerminate (.seq (.raise 7) .tick),
   .break 17, .continue 17, .raise 17, .locValue 17 999,
   .return 7 [3,17,17], .return 23 [1,3],
   .call none (some 999) [3,7] (some (999,.raise 888,19,23)),
   .call (some ([3,17],([7,7],[11]),.raise 5,19,23)) none [2,13] none,
   .call (some ([3],([7],[11]),.raise 5,19,23)) none [2,13]
     (some (17,.raise 23,29,31)),
   .alloc 3 ([17],[7]),
   .storeConsts 3 7 11 17 [(true,99)],
   .opCurrHeap .add 17 3,
   .install 3 7 11 17 ([23,23],[]),
   .codeBufferWrite 3 17, .dataBufferWrite 17 3,
   .ffi "probe" 3 7 11 17 ([23],[]),
   .shareInst .load16 3 (.var 17),
   .loop [1208925819614629174706177,3,3] (.return 7 [17]) [11],
   .call none none [] none]

private def expected : List Nat :=
  [0,0,11,9,17,17,17,17,17,17,11,17,7,0,0,17,17,17,23,7,17,23,
   17,17,17,23,17,17,23,17,1208925819614629174706177,0]

private theorem sourceRows : inputs.map wordProgCakeMaxVar = expected := by
  simp [inputs, expected, wordProgCakeMaxVar, wordInstCakeMaxVar,
    wordArithCakeMaxVar, wordExpCakeMaxVar, wordCutsetsCakeMaxVar]

private theorem supportedInputs : inputs.all RiscV.allocatorMemorySupported = true := by
  simp [inputs, RiscV.allocatorMemorySupported]

private theorem encodedInputs : inputs.all (fun program => (wordLangProgToHOL program).isSome) = true := by
  decide +kernel

/-- Flapjack-only Option payload packaging for the finite replay. -/
private theorem mappedConstant {α : Type} (value : Option α) (number : Nat)
    (present : value.isSome = true) : value.map (fun _ => number) = some number := by
  cases value <;> simp_all

example : inputs.map (fun program => (wordLangProgToHOL program).map maxVarHOL) =
    expected.map some := by
  rw [← sourceRows, List.map_map]
  apply List.map_congr_left
  intro program member
  rw [wordProgCakeMaxVar_codec program]
  exact mappedConstant _ _ ((List.all_eq_true.mp encodedInputs) program member)

example : (wordLangProgToHOL
    (.call none none [] (some (1,.inst (.arith (.addCarry 1 2 3 4 5)),2,3)) :
      WordProg (BitVec 8))).map maxVarHOL = none := by decide +kernel

example : RiscV.allocatorMemorySupported
    (.call none none [] (some (1,.inst (.memOffset .load16 3 17 99),2,3)) :
      WordProg (BitVec 8)) = false := by simp [RiscV.allocatorMemorySupported]

example : maxVarHOL (.inst (.mem .load16 3 (.addr 17 99)) : WordLangProgHOL (BitVec 8)) = 0 := by
  simp [maxVarHOL, maxVarInstHOL]

example {width : Nat} [NeZero width] (program : WordProg (BitVec width))
    :
    (wordLangProgToHOL program).map maxVarHOL =
      (wordLangProgToHOL program).map (fun _ => wordProgCakeMaxVar program) :=
  wordProgCakeMaxVar_codec program

-- Fresh word_program_max_unrestricted_probe.out: exact native inputs with
-- ordinary 16-bit memory, rejected by the allocator memory guard but accepted
-- by the carrier codec. The theorem does not assume that guard.
private def unrestrictedInputs : List (WordProg (BitVec 64)) :=
  [.seq .tick (.inst (.memOffset .load16 7 19 3)),
   .call none none [2,6] (some (999,.inst (.memOffset .load16 1000 2000 3),3,4)),
   .call (some ([11],([13,13],[]),.inst (.memOffset .load16 99 100 3),3,4))
     none [2,6] (some (17,.inst (.memOffset .store16 1000 2000 3),5,6)),
   .loop [29,29] (.inst (.memOffset .load16 1000 2000 3)) [31,31]]

example : unrestrictedInputs.map wordProgCakeMaxVar = [0,6,17,31] := by decide +kernel
example : unrestrictedInputs.map (wordSsaLimitVar []) = [5,9,21,33] := by decide +kernel
example : unrestrictedInputs.map (fun program => (wordLangProgToHOL program).map maxVarHOL) =
    [some 0,some 6,some 17,some 31] := by decide +kernel
example : unrestrictedInputs.all (fun program => (wordLangProgToHOL program).isSome) = true := by decide +kernel
example : unrestrictedInputs.map RiscV.allocatorMemorySupported = [false,false,false,false] := by decide +kernel

end Flapjack.Test.WordToStackProgramMaximumParity
