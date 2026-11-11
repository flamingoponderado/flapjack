module

public import Flapjack.Compiler.Backend.SourceToFlat.ToBviIncremental
public import Flapjack.Compiler.Backend.SourceToFlat.ToDataIncremental
public import Flapjack.Compiler.Backend.SourceToFlat.ToWordIncremental
public import Flapjack.Compiler.Backend.SourceToFlat.ToRiscVIncremental
public import Flapjack.Compiler.Backend.RiscVConfig.Executable
public meta import Flapjack.Compiler.Encoders.Asm
public meta import Flapjack.AstHOL.Syntax
public meta import Flapjack.Compiler.Backend.SourceToFlat.ToRiscVIncremental
public meta import Flapjack.Compiler.Backend.RiscVConfig.Executable

@[expose] public section

/-! Replay incremental source-to-BVI observations from pinned CakeML/HOL. -/
namespace Flapjack.Test.CakeIncrementalBviParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString

private def closureConfig : ClosToBvl.Config :=
  { ClosToBvl.defaultConfig with nextLoc := 10, maxApp := 2, doMti := false, doCall := false, knownConf := none }

private def bvlConfig : BvlToBvi.Config :=
  { BvlToBvi.defaultConfig with inlineSizeLimit := 0, doTailrec := false, doTmc := false }

private def wordConfig : DataToWord.Config :=
  ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩

private def riscvConfig : Backend.Config :=
  { RiscVConfig.riscvBackendConfigExecutable with
    sourceConf := SourceToFlat.emptyConfig
    closConf := closureConfig
    bvlConf := bvlConfig }

-- `backend_fp_config_probe.out`: original target-specific capability flags.
private def fpCaps (isa : Flapjack.Compiler.Encoders.Asm.AsmArchitecture) (registers : Nat) : Bool × Bool :=
  let asm := { Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig with isa := isa, fpRegCount := registers }
  let data := Backend.ensureFpConfOk asm riscvConfig.dataConf
  (data.hasFpOps, data.hasFpTern)

#guard fpCaps .riscv 0 == (false, false)
#guard fpCaps .armv7 3 == (true, true)
#guard fpCaps .armv7 2 == (true, false)
#guard fpCaps .riscv 3 == (true, false)

#guard match SourceToFlat.compileCakeIncToRiscVFuel 100 riscvConfig (0, 0)
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 1))] with
  | some (config, none) => config.wordConf.bitmapsLength == 6 && config.labConf.pos == 0
  | _ => false

private def seededLab : LabToTarget.Config :=
  { riscvConfig.labConf with pos := 4096, labels := sptFromAList ((List.range 132).map fun n => (n, sptInsert 0 0 .ln)) }

private def wordOracleConfig : WordToWord.Config :=
  { riscvConfig.wordToWordConf with colOracle := [some (sptInsert 7 11 .ln)] }

#guard match SourceToFlat.compileCakeIncToRiscVFuel 100
    { riscvConfig with labConf := seededLab, wordToWordConf := wordOracleConfig } (0, 0)
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 1))] with
  | some (config, some (bytes, bitmaps)) => config.wordConf.bitmapsLength == 6 &&
    config.labConf.pos == 4316 && bytes.length == 220 &&
    bitmaps == [2, 2, 8, 8589934595, 0, 0] &&
    match config.wordToWordConf.colOracle with
    | [some oracle] => sptLookup 7 oracle == some 11
    | _ => false
  | _ => false

-- The evaluation callback returns the same emitted bytes and bitmaps and
-- preserves the updated configuration; assembly failure stays a failure.
#guard match SourceToFlat.compileCakeIncForEvalFuel 100
    ((0, 0), { riscvConfig with labConf := seededLab },
      [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 1))]) with
  | some (config, bytes, bitmaps) => config.labConf.pos == 4316 && config.wordConf.bitmapsLength == 6 &&
      bytes.length == 220 && bitmaps == [2, 2, 8, 8589934595, 0, 0]
  | none => false

#guard (SourceToFlat.compileCakeIncForEvalFuel 100
  ((0, 0), riscvConfig, [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 1))])).isNone

private def unit : Bvi.Exp := .op (.blockOp (.cons 0)) []
private def storeEnv : Bvi.Exp :=
  .let [.op (.globOp (.global 3)) []]
    (.op (.memOp .update) [.op (.blockOp (.build [.int 0, .con 0 [0, 0]])) [],
      .op (.intOp (.const 0)) [], .var 0])

private def expected (count : Int) : List (Nat × Nat × Bvi.Exp) :=
  let allocation := .let [.call 0 (some 62) [.op (.intOp (.const count)) []] none] unit
  let entry := (132, 0, Bvi.Exp.let [allocation] (.call 0 (some 136) [] none))
  if count == 0 then
    [entry, (136, 0, .let [storeEnv] (.call 0 (some 140) [] none)), (140, 0, unit)]
  else
    [entry, (136, 0, .let [.op (.globOp (.setGlobal 3)) [.op (.intOp (.const 1)) []]]
      (.call 0 (some 140) [] none)),
      (140, 0, .let [storeEnv] (.call 0 (some 144) [] none)), (144, 0, unit)]

private def check (decls : List AstHOL.Dec) (count : Int) : Bool :=
  match SourceToFlat.compileCakeIncToBviFuel 100 (SourceToFlat.emptyConfig, closureConfig, bvlConfig)
      (0, 0) decls with
  | some ((source, closure, bvl), code) =>
    source.envs.next == 1 && source.next.vidx == count.toNat && closure.nextLoc == 14 &&
      bvl.nextName1 == 73 && bvl.nextName2 == 74 && bvl.nextName3 == 75 && code == expected count
  | none => false

#guard check [] 0
#guard check [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 1))] 1

-- The second batch refers to the first batch's saved environment. The
-- source aliases the existing global instead of allocating a new one.
#guard match SourceToFlat.compileCakeIncToBviFuel 100 (SourceToFlat.emptyConfig, closureConfig, bvlConfig)
    (0, 0) [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 1))] with
  | some (config, _) =>
    match SourceToFlat.compileCakeIncToBviFuel 100 config (0, 0)
      [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "y")) (.var (.short (ofString "x")))] with
    | some ((source, closure, bvl), code) =>
      source.envs.next == 2 && source.next.vidx == 1 && closure.nextLoc == 18 &&
        bvl.nextName1 == 73 && bvl.nextName2 == 74 && bvl.nextName3 == 75 &&
        code == [(148, 0, .let [.let [.call 0 (some 62) [.op (.intOp (.const 0)) []] none] unit]
          (.call 0 (some 152) [] none)),
          (152, 0, .let [.let [.op (.globOp (.global 3)) []]
            (.op (.memOp .update) [.op (.blockOp (.build [.int 1, .int 0, .con 0 [0, 1]])) [],
              .op (.intOp (.const 0)) [], .var 0])] (.call 0 (some 156) [] none)),
          (156, 0, unit)]
    | none => false
  | none => false

-- Complete data-language output from the original incremental pipeline.
#guard match SourceToFlat.compileCakeIncToDataFuel 100 (SourceToFlat.emptyConfig, closureConfig, bvlConfig)
    (0, 0) [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 1))] with
  | some ((source, closure, bvl),
    [(132, 0, .seq (.assign 0 (.intOp (.const 1)) [] none)
      (.seq (.call (some ([1], .ln)) (some 62) [0] none)
        (.seq (.assign 2 (.blockOp (.cons 0)) [] none) (.call none (some 136) [] none)))),
     (136, 0, .seq (.assign 0 (.intOp (.const 1)) [] none)
      (.seq (.assign 1 (.globOp (.setGlobal 3)) [0] none) (.call none (some 140) [] none))),
     (140, 0, .seq (.makeSpace 3 .ln)
      (.seq (.assign 0 (.globOp (.global 3)) [] none)
       (.seq (.assign 1 (.blockOp (.build [.int 0, .con 0 [0, 0]])) [] none)
        (.seq (.assign 2 (.intOp (.const 0)) [] none)
         (.seq (.assign 3 (.memOp .update) [0, 2, 1] none) (.call none (some 144) [] none)))))),
     (144, 0, .seq (.assign 0 (.blockOp (.cons 0)) [] none) (.return [0]))]) =>
      source.envs.next == 1 && source.next.vidx == 1 && closure.nextLoc == 14 && bvl.nextName1 == 73
  | _ => false

#guard match SourceToFlat.compileCakeIncToWord64Fuel 100 (SourceToFlat.emptyConfig, closureConfig, bvlConfig)
    wordConfig (0, 0) [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.lit (.intLit 1))] with
  | some ((source, closure, bvl),
    [(132, 1, .seq (.assign 2 (.const 4))
      (.seq (.call (some ([4], (live1, .ln), .skip, 132, 2)) (some 62) [2] none)
        (.seq (.assign 6 (.const 2)) (.call none (some 136) [0] none)))),
     (136, 1, .seq (.assign 2 (.const 4))
      (.seq (.seq (.store (.op .add [.lookup .globReal, .const 32]) 2) (.assign 4 (.const 2)))
        (.call none (some 140) [0] none))),
     (140, 1, .seq
      (.seq (.assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree]))
        (.ite .lower 1 (.imm 24) (.seq .skip (.seq (.assign 1 (.const 24))
          (.seq (.alloc 1 (live2, .ln)) .skip))) .skip))
      (.seq (.assign 2 (.load (.op .add [.lookup .globReal, .const 32])))
       (.seq (.seq (.assign 1 (.lookup .nextFree))
         (.seq (.assign 3 (.shift .lsl (.op .sub [.var 1, .lookup .currHeap]) (.const 5)))
          (.seq (.storeConsts 1 3 1 3 [(false, 562949953421315), (false, 0), (false, 0)])
           (.seq (.set .nextFree (.var 1)) (.assign 4 (.op .add [.const 5, .var 3]))))))
        (.seq (.assign 6 (.const 0))
         (.seq (.seq (.store (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 2) (.const 5)],
                    .op .add [.const 8, .shift .lsl (.var 6) (.const 1)]]) 4)
              (.assign 8 (.const 2))) (.call none (some 144) [0] none)))))),
     (144, 1, .seq (.assign 2 (.const 2)) (.return 0 [2]))]) =>
    source.envs.next == 1 && source.next.vidx == 1 && closure.nextLoc == 14 && bvl.nextName1 == 73 &&
      decide (live1 = sptListInsert [0] .ln) && decide (live2 = sptListInsert [0] .ln)
  | _ => false

end Flapjack.Test.CakeIncrementalBviParity
