import Flapjack.Compiler.Backend.StackRemove.StackFree
import Flapjack.Compiler.Backend.StackRemove.StackAddress
import Flapjack.Compiler.Backend.StackRemove.StackAlloc
import Flapjack.Compiler.Backend.StackRemove.StoreAddress
import Flapjack.Compiler.Backend.StackRemove.CopyLoop
import Flapjack.Compiler.Backend.BackendCommon

/-! Full native stack_removeScript.sml:161–222 compiler definition.
Actual runtime replacement remains dependency-linked on 36ez.3.
-/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Complete original compiler on faithful native programs. All configuration,
store/register/word inputs and unchanged constructors are retained; no successful
compilation, source safety or target evaluation premise is assumed. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "comp_def"
  (words_as_type_indexed_bitvec)]
def comp {width : Nat} [NeZero width] (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer : Nat) (program : HolProg width) : HolProg width :=
  match program with
  | .get register name =>
      if name = .currHeap then moveInst register (pointer + 2)
      else .inst (.mem .load register (.addr (pointer + 1) (storeOffset name)))
  | .set name register =>
      if name = .currHeap then moveInst (pointer + 2) register
      else .inst (.mem .store register (.addr (pointer + 1) (storeOffset name)))
  | .opCurrHeap operator destination source =>
      .inst (.arith (.binop operator destination source (.reg (pointer + 2))))
  | .stackFree count => stackFree pointer count
  | .stackAlloc count => stackAlloc jump pointer count
  | .stackStore register count =>
      let offset := wordOffset count
      if asmOffsetOkExact 0 bounds offset then
        .inst (.mem .store register (.addr pointer offset))
      else stackStore pointer register count
  | .stackLoad register count =>
      let offset := wordOffset count
      if asmOffsetOkExact 0 bounds offset then
        .inst (.mem .load register (.addr pointer offset))
      else .seq (moveInst register pointer) (stackLoad register count)
  | .dataBufferWrite address register => .inst (.mem .store register (.addr address 0))
  | .stackLoadAny register index =>
      .seq (.seq (moveInst register index) (addInst register pointer))
        (.inst (.mem .load register (.addr register 0)))
  | .stackStoreAny register index =>
      .seq (.inst (.arith (.binop .add pointer pointer (.reg index))))
        (.seq (.inst (.mem .store register (.addr pointer 0)))
          (.inst (.arith (.binop .sub pointer pointer (.reg index)))))
  | .stackGetSize register =>
      .seq (.seq (moveInst register pointer) (subInst register (pointer + 1)))
        (rightShiftInst register (wordShiftAmount width))
  | .stackSetSize register =>
      .seq (leftShiftInst register (wordShiftAmount width))
        (.seq (moveInst pointer (pointer + 1)) (addInst pointer register))
  | .bitmapLoad register value =>
      listSeqHOL [.inst (.mem .load register (.addr (pointer + 1) (storeOffset .bitmapBase))),
        addInst register value, leftShiftInst register (wordShiftAmount width),
        .inst (.mem .load register (.addr register 0))]
  | .storeConsts temporary bitmap _ =>
      listSeqHOL [.inst (.mem .load bitmap (.addr (pointer + 1) (storeOffset .bitmapBase))),
        addInst bitmap 1, leftShiftInst bitmap (wordShiftAmount width),
        copyLoop temporary bitmap, moveInst temporary 1, moveInst bitmap 1]
  | .seq first second => .seq (comp jump bounds pointer first) (comp jump bounds pointer second)
  | .ite comparison register right first second =>
      .ite comparison register right (comp jump bounds pointer first) (comp jump bounds pointer second)
  | .loop body => .loop (comp jump bounds pointer body)
  | .call ret target handler =>
      .call (match ret with
        | none => none
        | some (body, register, label, entry) => some (comp jump bounds pointer body, register, label, entry))
        target (match handler with
        | none => none
        | some (body, label, entry) => some (comp jump bounds pointer body, label, entry))
  | other => other
termination_by sizeOf program

end Flapjack.Compiler.Backend.StackRemove
