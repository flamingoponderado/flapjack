import Flapjack.Compiler.Backend.SourceToFlat.ToBviIncremental

/-! Replay incremental source-to-BVI observations from pinned CakeML/HOL. -/
namespace Flapjack.Test.CakeIncrementalBviParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString

private def closureConfig : ClosToBvl.Config :=
  { ClosToBvl.defaultConfig with nextLoc := 10, maxApp := 2, doMti := false, doCall := false, knownConf := none }

private def bvlConfig : BvlToBvi.Config :=
  { BvlToBvi.defaultConfig with inlineSizeLimit := 0, doTailrec := false, doTmc := false }

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

end Flapjack.Test.CakeIncrementalBviParity
