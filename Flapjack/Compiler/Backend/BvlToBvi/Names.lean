import Flapjack.Compiler.Backend.BvlToBvi.CompileOp
import Flapjack.Misc.Sptree
import Flapjack.Basis.Pure.MlString
import Flapjack.HolRef

/-! Names for BVL-to-BVI output locations. -/
namespace Flapjack.Compiler.Backend.BvlToBvi
open Flapjack.Basis.Pure.MlString

/-- Build the output name tree, retaining original stub and auxiliary names. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "get_names_def"]
def getNames (finalNums : List Nat) (oldNames : Spt MlString) : Spt MlString :=
  sptFromAList (finalNums.map fun n => (n,
    if n = initGlobalsLocation then ofString "start"
    else if n = allocGlobalLocation then ofString "AllocGlobal"
    else if n = copyGlobalsLocation then ofString "CopyGlobals"
    else if n = listLengthLocation then ofString "ListLength"
    else if n = fromListByteLocation then ofString "FromListByte"
    else if n = toListByteLocation then ofString "ToListByte"
    else if n = sumListLengthLocation then ofString "SumListLength"
    else if n = concatByteLocation then ofString "ConcatByte"
    else if n < bvlNumStubs then ofString "bvi_unknown"
    else
      let k := n - bvlNumStubs
      let name := (sptLookup (k / bvlToBviNamespaces) oldNames).getD (ofString "bvi_unmapped")
      MlString.concat [name, ofString (if k % bvlToBviNamespaces = 0 then "" else "_bvi_aux")]))

end Flapjack.Compiler.Backend.BvlToBvi
