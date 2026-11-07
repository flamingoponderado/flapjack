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

/-- Ordinary operators preserve simulation under a shared source clock bound. -/
theorem expressionSimulationBelow_ordinary {C F : Type} (clockBound : Nat) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp)
    (argsIH : expressionSimulationBelow (C := C) (F := F) clockBound args)
    (notForce : op ≠ .thunkOp .forceThunk) (notInstall : op ≠ .install) :
    expressionSimulationBelow (C := C) (F := F) clockBound [.op trace op args] := by
  cases op with
  | label index => exact expressionSimulationBelow_rejected clockBound trace (.label index) args argsIH
  | ffi name => exact expressionSimulationBelow_ffi clockBound trace name args argsIH
  | intOp operation => exact expressionSimulationBelow_int clockBound trace operation args argsIH
  | wordOp operation => exact expressionSimulationBelow_word clockBound trace operation args argsIH
  | install => exact False.elim (notInstall rfl)
  | thunkOp operation =>
    cases operation with
    | allocThunk mode => exact expressionSimulationBelow_allocThunk clockBound trace mode args argsIH
    | updateThunk mode => exact expressionSimulationBelow_updateThunk clockBound trace mode args argsIH
    | forceThunk => exact False.elim (notForce rfl)
  | globOp operation =>
    cases operation with
    | global index => exact expressionSimulationBelow_global clockBound trace index args argsIH
    | setGlobal index => exact expressionSimulationBelow_setGlobal clockBound trace index args argsIH
    | allocGlobal => exact expressionSimulationBelow_alloc clockBound trace args argsIH
    | globalsPtr => exact expressionSimulationBelow_rejected clockBound trace .globalsPtr args argsIH
    | setGlobalsPtr => exact expressionSimulationBelow_rejected clockBound trace .setGlobalsPtr args argsIH
  | blockOp operation =>
    cases operation with
    | cons tag => exact expressionSimulationBelow_consBlock clockBound trace tag args argsIH
    | elemAt index => exact expressionSimulationBelow_inspect clockBound trace (.elemAt index) args argsIH
    | tagLenEq tag len => exact expressionSimulationBelow_inspect clockBound trace (.tagLengthEq tag len) args argsIH
    | lenEq len => exact expressionSimulationBelow_inspect clockBound trace (.lengthEq len) args argsIH
    | tagEq tag => exact expressionSimulationBelow_inspect clockBound trace (.tagEq tag) args argsIH
    | lengthBlock => exact expressionSimulationBelow_inspect clockBound trace .length args argsIH
    | boolTest test => exact expressionSimulationBelow_boolean clockBound trace (.test test) args argsIH
    | boolNot => exact expressionSimulationBelow_boolean clockBound trace .not args argsIH
    | boundsCheckBlock => exact expressionSimulationBelow_compare clockBound trace .bounds args argsIH
    | consExtend tag => exact expressionSimulationBelow_extend clockBound trace tag args argsIH
    | fromList tag => exact expressionSimulationBelow_listOp clockBound trace (.fromList tag) args argsIH
    | listAppend => exact expressionSimulationBelow_listOp clockBound trace .append args argsIH
    | constant constant => exact expressionSimulationBelow_constant clockBound trace constant args argsIH
    | equal => exact expressionSimulationBelow_equal clockBound trace args argsIH
    | equalConst part =>
      cases part with
      | int n => exact expressionSimulationBelow_compare clockBound trace (.intEq n) args argsIH
      | str text => exact expressionSimulationBelow_compare clockBound trace (.stringEq text) args argsIH
      | w64 word => exact expressionSimulationBelow_compare clockBound trace (.wordEq word) args argsIH
      | con tag fields => exact expressionSimulationBelow_rejected clockBound trace (.equalCon tag fields) args argsIH
    | build parts => exact expressionSimulationBelow_rejected clockBound trace (.build parts) args argsIH
  | memOp operation =>
    cases operation with
    | ref => exact expressionSimulationBelow_ref clockBound trace args argsIH
    | update => exact expressionSimulationBelow_updateArray clockBound trace args argsIH
    | el => exact expressionSimulationBelow_memoryEl clockBound trace args argsIH
    | length => exact expressionSimulationBelow_memoryLength clockBound trace .array args argsIH
    | lengthByte => exact expressionSimulationBelow_memoryLength clockBound trace .bytes args argsIH
    | refByte flag =>
      cases flag with
      | false => exact expressionSimulationBelow_refByte clockBound trace args argsIH
      | true => exact expressionSimulationBelow_refByteTrue clockBound trace args argsIH
    | refArray => exact expressionSimulationBelow_refArray clockBound trace args argsIH
    | derefByte => exact expressionSimulationBelow_memoryByte clockBound trace args argsIH
    | updateByte => exact expressionSimulationBelow_updateByte clockBound trace args argsIH
    | concatByteVec => exact expressionSimulationBelow_byteConstruct clockBound trace .concat args argsIH
    | fromListByte => exact expressionSimulationBelow_byteConstruct clockBound trace .fromList args argsIH
    | toListByte => exact expressionSimulationBelow_byteToList clockBound trace args argsIH
    | lengthByteVec => exact expressionSimulationBelow_byteVectorRead clockBound trace .length args argsIH
    | derefByteVec => exact expressionSimulationBelow_byteVectorRead clockBound trace .deref args argsIH
    | stringCmp fast comparison => exact expressionSimulationBelow_byteStringCmp clockBound trace fast comparison args argsIH
    | xorByte => exact expressionSimulationBelow_xorByte clockBound trace args argsIH
    | copyByte fresh =>
      cases fresh with
      | false => exact expressionSimulationBelow_copyByteInto clockBound trace args argsIH
      | true => exact expressionSimulationBelow_copyByteNew clockBound trace args argsIH
    | boundsCheckArray => exact expressionSimulationBelow_memoryBoundsArray clockBound trace args argsIH
    | boundsCheckByte loose => exact expressionSimulationBelow_memoryBoundsByte clockBound trace loose args argsIH
    | mutCons tag size => exact expressionSimulationBelow_rejected clockBound trace (.mutCons tag size) args argsIH
    | updateCons => exact expressionSimulationBelow_rejected clockBound trace .updateCons args argsIH
    | finaliseCons => exact expressionSimulationBelow_rejected clockBound trace .finaliseCons args argsIH
    | configGC => exact expressionSimulationBelow_configGC clockBound trace args argsIH


end Flapjack.Compiler.Backend.ClosToBvl
