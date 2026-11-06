import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileConcatByte
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileUnsupported

/-! Assembly of memory-operation cases for BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Every memory operation satisfies pass simulation given operand
simulation. Untagged pending evaluator and dispatcher review. -/
theorem simulation_memOp {C F : Type} (op : ClosLang.MemOp) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp op) arguments] env source := by
  cases op with
  | ref => exact simulation_ref arguments env source argsIH
  | update => exact simulation_arrayUpdate arguments env source argsIH
  | el => exact simulation_element arguments env source argsIH
  | length => exact simulation_arrayLength arguments env source argsIH
  | lengthByte => exact simulation_byteArrayLength arguments env source argsIH
  | refByte flag =>
    cases flag with
    | false => exact simulation_refByte arguments env source argsIH
    | true => exact simulation_sourceUnsupported _ arguments env source (by simp) argsIH
  | refArray => exact simulation_refArray arguments env source argsIH
  | derefByte => exact simulation_byteRead arguments env source argsIH
  | updateByte => exact simulation_byteArrayUpdate arguments env source argsIH
  | concatByteVec => exact simulation_concatByte arguments env source argsIH
  | copyByte flag =>
    cases flag with
    | false => exact simulation_copyByte arguments env source argsIH
    | true => exact simulation_copyByteAllocate arguments env source argsIH
  | fromListByte => exact simulation_fromListByte arguments env source argsIH
  | toListByte => exact simulation_toListByte arguments env source argsIH
  | lengthByteVec => exact simulation_sourceUnsupported _ arguments env source (by simp) argsIH
  | derefByteVec => exact simulation_sourceUnsupported _ arguments env source (by simp) argsIH
  | stringCmp fast op => exact simulation_stringCmp fast op arguments env source argsIH
  | xorByte => exact simulation_xorByte arguments env source argsIH
  | boundsCheckArray => exact simulation_arrayBounds arguments env source argsIH
  | boundsCheckByte loose => exact simulation_byteBounds loose arguments env source argsIH
  | mutCons tag index => exact simulation_sourceUnsupported _ arguments env source (by simp) argsIH
  | updateCons => exact simulation_sourceUnsupported _ arguments env source (by simp) argsIH
  | finaliseCons => exact simulation_sourceUnsupported _ arguments env source (by simp) argsIH
  | configGC => exact simulation_configGC arguments env source argsIH

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
