import Flapjack.Compiler.Backend.DataToWord.Locations
import Flapjack.Compiler.Backend.DataToWord.Control
import Flapjack.Pancake.WordLang

/-! A partial selection of data-to-word runtime stubs. -/
namespace Flapjack.Compiler.Backend.DataToWord

private def listSeq {α : Type} : List (WordLangProgHOL α) → WordLangProgHOL α
  | [] => .skip
  | [x] => x
  | x :: y :: xs => .seq x (listSeq (y :: xs))

/-- Flapjack's partial stub lookup. It supplies only the listed stubs and
returns `none` for all others; the complete HOL `stubs` list, including
bignum code, remains unported. -/
def compileStub? {width : Nat} (location : Nat) : Option (Nat × WordLangProgHOL (BitVec width)) :=
  if location = memCopyLocation then
    some (5, .ite .test 2 (.reg 2) (.return 0 [8]) (listSeq [
      .assign 1 (.load (.var 4)),
      .assign 2 (.op .sub [.var 2, .const 4]),
      .assign 4 (.op .add [.var 4, .const (BitVec.ofNat width (width / 8))]),
      .store (.var 6) 1,
      .assign 6 (.op .add [.var 6, .const (BitVec.ofNat width (width / 8))]),
      .call none (some memCopyLocation) [0, 2, 4, 6, 8] none]))
  else if location = stringCmpLoopLocation then
    some (6, .ite .equal 6 (.imm (BitVec.ofNat width (width / 8))) (.return 0 [8, 10])
      (listSeq [
        .inst (.mem .load8 1 (.addr 2 0)),
        .inst (.mem .load8 3 (.addr 4 0)),
        .ite .notEqual 1 (.reg 3) (.return 0 [1, 3]) .skip,
        .assign 2 (.op .add [.var 2, .const 1]),
        .assign 4 (.op .add [.var 4, .const 1]),
        .assign 6 (.op .sub [.var 6, .const 1]),
        .call none (some stringCmpLoopLocation) [0, 2, 4, 6, 8, 10] none]))
  else if location = replicateLocation then
    some (5, .ite .equal 6 (.imm 0) (.return 0 [8]) (listSeq [
      .assign 2 (.op .add [.var 2, .const (BitVec.ofNat width (width / 8))]),
      .store (.var 2) 4,
      .assign 6 (.op .sub [.var 6, .const 4]),
      .call none (some replicateLocation) [0, 2, 4, 6, 8] none]))
  else if location = addLocation ∨ location = subLocation ∨ location = mulLocation ∨
      location = divLocation ∨ location = modLocation then
    let operation := if location = addLocation then 0 else if location = subLocation then 1
      else if location = mulLocation then 4 else if location = divLocation then 5 else 6
    some (3, .seq (.assign 6 (.const (BitVec.ofNat width (4 * operation))))
      (.call none (some anyArithLocation) [0, 2, 4, 6] none))
  else if location = unusedLocation then some (6, .skip)
  else if location = byteCopyNewLocation then some (4, .skip)
  else if location = dummyLocation then some (0, .skip)
  else none

/-- Extend the partial stub lookup with configuration-dependent cases. The
unimplemented stubs still return `none`, so this is not HOL's complete list. -/
def compileConfiguredStub? {width : Nat} [NeZero width] (conf : Config) (location : Nat) :
    Option (Nat × WordLangProgHOL (BitVec width)) :=
  if location = refArrayLocation then
    let shiftN (op : Shift) (value : WordLangExpHOL (BitVec width)) (amount : Nat) :=
      WordLangExpHOL.shift op value (.const (BitVec.ofNat width amount))
    some (3, listSeq [
      .assign 1 (shiftN .lsl (.op .add [shiftN .lsr (.var 2) 2, .const 1]) (wordShiftAmount width)),
      .set .triggerGC (.op .sub [.lookup .triggerGC, .var 1]),
      .assign 1 (.op .sub [.lookup .endOfHeap, .var 1]),
      .set .endOfHeap (.var 1),
      .assign 3 (.op .or [shiftN .lsl (.op .sub [.var 1, .lookup .currHeap])
        (shiftLength conf - wordShiftAmount width), .const 1]),
      .assign 5 (.op .or [shiftN .lsl (.var 2) (width - conf.lenSize - 2),
        .const (makeHeader conf 2 0)]),
      .store (.var 1) 5,
      .call none (some replicateLocation) [0, 1, 4, 2, 3] none])
  else if location = fromList1Location then
    let bytes := BitVec.ofNat width (width / 8)
    some (6, listSeq [
      .store (.var 2) 10,
      .assign 2 (.op .add [.var 2, .const bytes]),
      .ite .equal 6 (.imm 0)
        (listSeq [.set .nextFree (.var 2), .return 0 [8]])
        (listSeq [
          .assign 4 (realAddr conf 4),
          .assign 10 (.load (.op .add [.var 4, .const bytes])),
          .assign 4 (.load (.op .add [.var 4, .const (2 * bytes)])),
          .assign 6 (.op .sub [.var 6, .const 4]),
          .call none (some fromList1Location) [0, 2, 4, 6, 8, 10] none])])
  else if location = byteCopyLocation then
    let bytes := BitVec.ofNat width (width / 8)
    some (6, listSeq [
      .assign 4 (shiftVar .lsr 4 2), .assign 6 (shiftVar .lsr 6 2),
      .assign 10 (shiftVar .lsr 10 2), .assign 1 (.const 2),
      .assign 2 (.op .add [realAddr conf 2, .const bytes, .var 4]),
      .assign 8 (.op .add [realAddr conf 8, .const bytes, .var 10]),
      .ite .lower 4 (.reg 10)
        (listSeq [
          .assign 3 (.op .sub [.var 6, .const 1]),
          .assign 2 (.op .add [.var 2, .var 3]),
          .assign 8 (.op .add [.var 8, .var 3]),
          .call none (some byteCopySubLocation) [0, 6, 2, 8, 1] none])
        (.call none (some byteCopyAddLocation) [0, 6, 2, 8, 1] none)])
  else compileStub? location

end Flapjack.Compiler.Backend.DataToWord
