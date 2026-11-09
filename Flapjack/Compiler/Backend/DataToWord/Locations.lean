import Flapjack.Compiler.Backend.BackendCommon

/-! Stub locations reserved by data-to-word compilation. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- Location of the FromList stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "FromList_location_def"]
def fromListLocation : Nat := wordNumStubs

/-- Location of the FromList1 stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "FromList1_location_def"]
def fromList1Location : Nat := fromListLocation + 1

/-- Location of the RefByte stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "RefByte_location_def"]
def refByteLocation : Nat := fromList1Location + 1

/-- Location of the RefArray stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "RefArray_location_def"]
def refArrayLocation : Nat := refByteLocation + 1

/-- Location of the Replicate stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Replicate_location_def"]
def replicateLocation : Nat := refArrayLocation + 1

/-- Location of the AnyArith stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "AnyArith_location_def"]
def anyArithLocation : Nat := replicateLocation + 1

/-- Location of the Add stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Add_location_def"]
def addLocation : Nat := anyArithLocation + 1

/-- Location of the Sub stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Sub_location_def"]
def subLocation : Nat := addLocation + 1

/-- Location of the Mul stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Mul_location_def"]
def mulLocation : Nat := subLocation + 1

/-- Location of the Div stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Div_location_def"]
def divLocation : Nat := mulLocation + 1

/-- Location of the Mod stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Mod_location_def"]
def modLocation : Nat := divLocation + 1

/-- Location of the Compare1 stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Compare1_location_def"]
def compare1Location : Nat := modLocation + 1

/-- Location of the Compare stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Compare_location_def"]
def compareLocation : Nat := compare1Location + 1

/-- Location of the Equal1 stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Equal1_location_def"]
def equal1Location : Nat := compareLocation + 1

/-- Location of the Equal stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Equal_location_def"]
def equalLocation : Nat := equal1Location + 1

/-- Location of the LongDiv1 stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "LongDiv1_location_def"]
def longDiv1Location : Nat := equalLocation + 1

/-- Location of the LongDiv stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "LongDiv_location_def"]
def longDivLocation : Nat := longDiv1Location + 1

/-- Location of the MemCopy stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "MemCopy_location_def"]
def memCopyLocation : Nat := longDivLocation + 1

/-- Location of the ByteCopy stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "ByteCopy_location_def"]
def byteCopyLocation : Nat := memCopyLocation + 1

/-- Location of the ByteCopyAdd stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "ByteCopyAdd_location_def"]
def byteCopyAddLocation : Nat := byteCopyLocation + 1

/-- Location of the ByteCopySub stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "ByteCopySub_location_def"]
def byteCopySubLocation : Nat := byteCopyAddLocation + 1

/-- Location of the ByteCopyNew stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "ByteCopyNew_location_def"]
def byteCopyNewLocation : Nat := byteCopySubLocation + 1

/-- Location of the Install stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Install_location_def"]
def installLocation : Nat := byteCopyNewLocation + 1

/-- Location of the InstallCode stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "InstallCode_location_def"]
def installCodeLocation : Nat := installLocation + 1

/-- Location of the InstallData stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "InstallData_location_def"]
def installDataLocation : Nat := installCodeLocation + 1

/-- Location of the Dummy stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Dummy_location_def"]
def dummyLocation : Nat := installDataLocation + 1

/-- Location of the Append stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Append_location_def"]
def appendLocation : Nat := dummyLocation + 1

/-- Location of the AppendMainLoop stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "AppendMainLoop_location_def"]
def appendMainLoopLocation : Nat := appendLocation + 1

/-- Location of the AppendLenLoop stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "AppendLenLoop_location_def"]
def appendLenLoopLocation : Nat := appendMainLoopLocation + 1

/-- Location of the XorLoop stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "XorLoop_location_def"]
def xorLoopLocation : Nat := appendLenLoopLocation + 1

/-- Location of the Unused stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Unused_location_def"]
def unusedLocation : Nat := xorLoopLocation + 1

/-- Location of the StringCmpLoop stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "StringCmpLoop_location_def"]
def stringCmpLoopLocation : Nat := unusedLocation + 1

/-- Location of the Bignum stub. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "Bignum_location_def"]
def bignumLocation : Nat := stringCmpLoopLocation + 1

end Flapjack.Compiler.Backend.DataToWord
