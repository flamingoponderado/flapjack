import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateRejected
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateInteger
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateWord
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateConstant
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockBoolean
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockInspect
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockCompare
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockCons
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockExtend
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockList
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateBlockEqual
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateGlobal
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryLength
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryByte
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryEl
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryBounds
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteBounds
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteVectorRead
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryAlloc
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryUpdate
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteToList
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteStringCmp
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteConstruct
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteCopy
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateByteXor
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateMemoryConfig
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateFfi
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateThunk

/-! Assembly of ordinary operator cases for the candidate simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Every non-force, non-install operator satisfies the expression simulation
when its argument list does. This remains a candidate until the semantic
carriers and complete pass theorem are reviewed. -/
theorem expressionSimulation_ordinary {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (notForce : op ≠ .thunkOp .forceThunk) (notInstall : op ≠ .install) :
    expressionSimulation (C := C) (F := F) [.op trace op args] := by
  cases op with
  | label index => exact expressionSimulation_rejected trace (.label index) args argsIH
  | ffi name => exact expressionSimulation_ffi trace name args argsIH
  | intOp operation => exact expressionSimulation_int trace operation args argsIH
  | wordOp operation => exact expressionSimulation_word trace operation args argsIH
  | install => exact False.elim (notInstall rfl)
  | thunkOp operation =>
    cases operation with
    | allocThunk mode => exact expressionSimulation_allocThunk trace mode args argsIH
    | updateThunk mode => exact expressionSimulation_updateThunk trace mode args argsIH
    | forceThunk => exact False.elim (notForce rfl)
  | globOp operation =>
    cases operation with
    | global index => exact expressionSimulation_global trace index args argsIH
    | setGlobal index => exact expressionSimulation_setGlobal trace index args argsIH
    | allocGlobal => exact expressionSimulation_alloc trace args argsIH
    | globalsPtr => exact expressionSimulation_rejected trace .globalsPtr args argsIH
    | setGlobalsPtr => exact expressionSimulation_rejected trace .setGlobalsPtr args argsIH
  | blockOp operation =>
    cases operation with
    | cons tag => exact expressionSimulation_consBlock trace tag args argsIH
    | elemAt index => exact expressionSimulation_inspect trace (.elemAt index) args argsIH
    | tagLenEq tag len => exact expressionSimulation_inspect trace (.tagLengthEq tag len) args argsIH
    | lenEq len => exact expressionSimulation_inspect trace (.lengthEq len) args argsIH
    | tagEq tag => exact expressionSimulation_inspect trace (.tagEq tag) args argsIH
    | lengthBlock => exact expressionSimulation_inspect trace .length args argsIH
    | boolTest test => exact expressionSimulation_boolean trace (.test test) args argsIH
    | boolNot => exact expressionSimulation_boolean trace .not args argsIH
    | boundsCheckBlock => exact expressionSimulation_compare trace .bounds args argsIH
    | consExtend tag => exact expressionSimulation_extend trace tag args argsIH
    | fromList tag => exact expressionSimulation_listOp trace (.fromList tag) args argsIH
    | listAppend => exact expressionSimulation_listOp trace .append args argsIH
    | constant constant => exact expressionSimulation_constant trace constant args argsIH
    | equal => exact expressionSimulation_equal trace args argsIH
    | equalConst part =>
      cases part with
      | int n => exact expressionSimulation_compare trace (.intEq n) args argsIH
      | str text => exact expressionSimulation_compare trace (.stringEq text) args argsIH
      | w64 word => exact expressionSimulation_compare trace (.wordEq word) args argsIH
      | con tag fields => exact expressionSimulation_rejected trace (.equalCon tag fields) args argsIH
    | build parts => exact expressionSimulation_rejected trace (.build parts) args argsIH
  | memOp operation =>
    cases operation with
    | ref => exact expressionSimulation_ref trace args argsIH
    | update => exact expressionSimulation_updateArray trace args argsIH
    | el => exact expressionSimulation_memoryEl trace args argsIH
    | length => exact expressionSimulation_memoryLength trace .array args argsIH
    | lengthByte => exact expressionSimulation_memoryLength trace .bytes args argsIH
    | refByte flag =>
      cases flag with
      | false => exact expressionSimulation_refByte trace args argsIH
      | true => exact expressionSimulation_refByteTrue trace args argsIH
    | refArray => exact expressionSimulation_refArray trace args argsIH
    | derefByte => exact expressionSimulation_memoryByte trace args argsIH
    | updateByte => exact expressionSimulation_updateByte trace args argsIH
    | concatByteVec => exact expressionSimulation_byteConstruct trace .concat args argsIH
    | fromListByte => exact expressionSimulation_byteConstruct trace .fromList args argsIH
    | toListByte => exact expressionSimulation_byteToList trace args argsIH
    | lengthByteVec => exact expressionSimulation_byteVectorRead trace .length args argsIH
    | derefByteVec => exact expressionSimulation_byteVectorRead trace .deref args argsIH
    | stringCmp fast comparison => exact expressionSimulation_byteStringCmp trace fast comparison args argsIH
    | xorByte => exact expressionSimulation_xorByte trace args argsIH
    | copyByte fresh =>
      cases fresh with
      | false => exact expressionSimulation_copyByteInto trace args argsIH
      | true => exact expressionSimulation_copyByteNew trace args argsIH
    | boundsCheckArray => exact expressionSimulation_memoryBoundsArray trace args argsIH
    | boundsCheckByte loose => exact expressionSimulation_memoryBoundsByte trace loose args argsIH
    | mutCons tag size => exact expressionSimulation_rejected trace (.mutCons tag size) args argsIH
    | updateCons => exact expressionSimulation_rejected trace .updateCons args argsIH
    | finaliseCons => exact expressionSimulation_rejected trace .finaliseCons args argsIH
    | configGC => exact expressionSimulation_configGC trace args argsIH

end Flapjack.Compiler.Backend.ClosToBvl
