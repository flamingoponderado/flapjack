import Flapjack.Compiler.Backend.DataToWord.Locations
import Flapjack.Basis.Pure.MlString
import Flapjack.HolRef

/-! Names for fixed and generated data-to-word stubs. -/
namespace Flapjack.Compiler.Backend.DataToWord
open Flapjack.Basis.Pure.MlString

/-- Original ordered data-to-word stub name list. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "stub_names_def"]
def stubNames (_ : Unit) : List (Nat × MlString) :=
  [(fromListLocation, ofString "_FromList"), (fromList1Location, ofString "_FromList1"),
   (refByteLocation, ofString "_RefByte"), (refArrayLocation, ofString "_RefArray"),
   (replicateLocation, ofString "_Replicate"), (anyArithLocation, ofString "_AnyArith"),
   (addLocation, ofString "_Add"), (subLocation, ofString "_Sub"), (mulLocation, ofString "_Mul"),
   (divLocation, ofString "_Div"), (modLocation, ofString "_Mod"),
   (compare1Location, ofString "_Compare1"), (compareLocation, ofString "_Compare"),
   (equal1Location, ofString "_Equal1"), (equalLocation, ofString "_Equal"),
   (longDiv1Location, ofString "_LongDiv1"), (longDivLocation, ofString "_LongDiv"),
   (installLocation, ofString "_Install"), (installCodeLocation, ofString "_InstallCode"),
   (installDataLocation, ofString "_InstallData"), (appendLocation, ofString "_Append"),
   (appendMainLoopLocation, ofString "_AppendMainLoop"), (appendLenLoopLocation, ofString "_AppendLenLoop"),
   (xorLoopLocation, ofString "_XorLoop"), (unusedLocation, ofString "_Unused"),
   (stringCmpLoopLocation, ofString "_StringCmpLoop"), (memCopyLocation, ofString "_MemCopy"),
   (byteCopyLocation, ofString "_ByteCopy"), (byteCopyAddLocation, ofString "_ByteCopyAdd"),
   (byteCopySubLocation, ofString "_ByteCopySub"), (byteCopyNewLocation, ofString "_ByteCopyNew"),
   (dummyLocation, ofString "_Dummy")] ++
  (List.range (dataNumStubs - bignumLocation)).map fun i => (i + bignumLocation, ofString "_Bignum")

end Flapjack.Compiler.Backend.DataToWord
