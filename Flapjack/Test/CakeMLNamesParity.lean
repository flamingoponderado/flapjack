import Flapjack.Compiler.Backend.BvlToBvi.Names
import Flapjack.Compiler.Backend.DataToWord.Names
import Flapjack.Compiler.Backend.SourceToFlat.ToRiscV
import Flapjack.Test.CakeMLFlatOracle

/-! Original output and runtime symbol-name observations. -/
namespace Flapjack.Test.CakeMLNamesParity
open Flapjack Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend

#guard let old := sptInsert 3 (ofString "alpha") .ln
  let names := BvlToBvi.getNames [62, 63, 64, 65, 66, 67, 68, 69, 70, 84, 85, 96, 97] old
  ([62, 63, 64, 65, 66, 67, 68, 69, 70, 84, 85, 96, 97].map fun n =>
    (sptLookup n names).map toStringOfBytes) ==
  [some "AllocGlobal", some "CopyGlobals", some "start", some "ListLength", some "FromListByte",
   some "ToListByte", some "SumListLength", some "ConcatByte", some "bvi_unknown",
   some "alpha", some "alpha_bvi_aux", some "bvi_unmapped", some "bvi_unmapped_bvi_aux"]
#guard Flapjack.Test.CakeMLFlatOracle.bvl_output_names

#guard let names := DataToWord.stubNames ()
  (names.take 32 |>.map fun (n, s) => (n, toStringOfBytes s)) ==
  [(7, "_FromList"), (8, "_FromList1"), (9, "_RefByte"), (10, "_RefArray"), (11, "_Replicate"),
   (12, "_AnyArith"), (13, "_Add"), (14, "_Sub"), (15, "_Mul"), (16, "_Div"), (17, "_Mod"),
   (18, "_Compare1"), (19, "_Compare"), (20, "_Equal1"), (21, "_Equal"), (22, "_LongDiv1"),
   (23, "_LongDiv"), (29, "_Install"), (30, "_InstallCode"), (31, "_InstallData"), (33, "_Append"),
   (34, "_AppendMainLoop"), (35, "_AppendLenLoop"), (36, "_XorLoop"), (37, "_Unused"),
   (38, "_StringCmpLoop"), (24, "_MemCopy"), (25, "_ByteCopy"), (26, "_ByteCopyAdd"),
   (27, "_ByteCopySub"), (28, "_ByteCopyNew"), (32, "_Dummy")] &&
  (names.drop 32 |>.map fun (n, s) => (n, toStringOfBytes s)) ==
    (List.range 23).map (fun n => (n + 39, "_Bignum"))
#guard Flapjack.Test.CakeMLFlatOracle.data_stub_names

private def noOpts : ClosToBvl.Config :=
  { ClosToBvl.defaultConfig with maxApp := 0, doMti := false, doCall := false, knownConf := none }

#guard match SourceToFlat.compileCakeToBviWithNamesNoOptsFuel 100 SourceToFlat.emptyConfig noOpts [] with
  | some (_, _, _, _, _, names) =>
      let names := SourceToFlat.backendNames names
      ([0, 1, 2, 3, 4, 5, 6, 7, 9, 39, 61, 62, 63, 64, 65, 69, 70, 72, 76, 80, 84, 88].map fun n =>
        (sptLookup n names).map toStringOfBytes) ==
      [some "_Init", some "_Halt0", some "_Halt2", none, some "_GC", some "_Raise", some "_StoreConsts",
       some "_FromList", some "_RefByte", some "_Bignum", some "_Bignum", some "AllocGlobal",
       some "CopyGlobals", some "start", some "ListLength", some "ConcatByte", none, some "bvl_force",
       some "bvl_init", some "dec", some "dec", some "dec"]
  | none => false
#guard Flapjack.Test.CakeMLFlatOracle.source_output_names

end Flapjack.Test.CakeMLNamesParity
