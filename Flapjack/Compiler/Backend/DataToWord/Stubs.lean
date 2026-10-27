import Flapjack.Compiler.Backend.DataToWord.Locations
import Flapjack.Compiler.Backend.DataToWord.Control
import Flapjack.Pancake.WordLang

/-! A partial selection of data-to-word runtime stubs. -/
namespace Flapjack.Compiler.Backend.DataToWord

private def listSeq {α : Type} : List (WordLangProgHOL α) → WordLangProgHOL α
  | [] => .skip
  | [x] => x
  | x :: y :: xs => .seq x (listSeq (y :: xs))

/-- Internal common shape of the two directional byte-copy loops. -/
private def byteCopyLoop {width : Nat} (forward : Bool) : WordLangProgHOL (BitVec width) :=
  let offset (n : Nat) : BitVec width :=
    if forward then BitVec.ofNat width n else -(BitVec.ofNat width n)
  let load (r n : Nat) := WordLangProgHOL.inst (.mem .load8 r (.addr 4 (offset n)))
  let store (r n : Nat) := WordLangProgHOL.inst (.mem .store8 r (.addr 6 (offset n)))
  let op := if forward then BinOp.add else BinOp.sub
  let loc := if forward then byteCopyAddLocation else byteCopySubLocation
  .ite .lower 2 (.imm 4)
    (.ite .lower 2 (.imm 2)
      (.ite .equal 2 (.imm 0) (.return 0 [8]) (listSeq [load 1 0, store 1 0, .return 0 [8]]))
      (listSeq [load 1 0, load 3 1,
        .ite .equal 2 (.imm 2) (listSeq [store 1 0, store 3 1, .return 0 [8]])
          (listSeq [load 5 2, store 1 0, store 3 1, store 5 2, .return 0 [8]])]))
    (listSeq [load 1 0, load 3 1, load 5 2, load 7 3,
      store 1 0, store 3 1, store 5 2, store 7 3,
      .assign 9 (.op .sub [.var 2, .const 4]),
      .assign 11 (.op op [.var 4, .const 4]),
      .assign 13 (.op op [.var 6, .const 4]),
      .call none (some loc) [0, 9, 11, 13, 8] none])

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
  else if location = byteCopyAddLocation then some (5, byteCopyLoop true)
  else if location = byteCopySubLocation then some (5, byteCopyLoop false)
  else if location = xorLoopLocation then
    let bytes := BitVec.ofNat width (width / 8)
    some (4, .ite .lower 6 (.imm 2)
      (.ite .equal 6 (.imm 0) (listSeq [.assign 1 (.const 2), .return 0 [1]])
        (listSeq [.assign 5 (.load (.var 4)), .assign 3 (.load (.var 2)),
          .assign 7 (.op .xor [.var 5, .var 3]), .store (.var 2) 7,
          .assign 1 (.const 2), .return 0 [1]]))
      (listSeq [.assign 5 (.load (.var 4)), .assign 3 (.load (.var 2)),
        .assign 9 (.load (.op .add [.var 4, .const bytes])),
        .assign 7 (.load (.op .add [.var 2, .const bytes])),
        .assign 6 (.op .sub [.var 6, .const 2]),
        .assign 5 (.op .xor [.var 5, .var 3]), .assign 9 (.op .xor [.var 9, .var 7]),
        .store (.var 2) 5, .store (.op .add [.var 2, .const bytes]) 9,
        .assign 4 (.op .add [.var 4, .const (2 * bytes)]),
        .assign 2 (.op .add [.var 2, .const (2 * bytes)]),
        .call none (some xorLoopLocation) [0, 2, 4, 6] none]))
  else if location = installLocation then
    some (3, listSeq [.assign 1 (.lookup .bitmapBuffer), .assign 3 (.lookup .codeBuffer),
      .set .bitmapBuffer (.var 2), .set .codeBuffer (.var 4),
      .install 3 4 1 2 (.ls (), .ln), .return 0 [3]])
  else if location = compare1Location then
    let bytes := BitVec.ofNat width (width / 8)
    let result (n : Nat) := WordLangProgHOL.seq (.assign 2 (.const (BitVec.ofNat width n))) (.return 0 [2])
    some (4, .ite .equal 2 (.imm 0) (result 1) (listSeq [
      .assign 8 (.load (.var 4)), .assign 9 (.load (.var 6)),
      .ite .equal 8 (.reg 9) (listSeq [
        .assign 2 (.op .sub [.var 2, .const 1]),
        .assign 4 (.op .sub [.var 4, .const bytes]),
        .assign 6 (.op .sub [.var 6, .const bytes]),
        .call none (some compare1Location) [0, 2, 4, 6] none])
        (.ite .lower 8 (.reg 9) (result 0) (result 2))]))
  else if location = equal1Location then
    let bytes := BitVec.ofNat width (width / 8)
    some (4, listSeq [
      .ite .equal 2 (.imm 0) (.seq (.assign 2 (.const 1)) (.return 0 [2])) .skip,
      .assign 1 (.load (.var 4)), .assign 3 (.load (.var 6)),
      .call (some ([5], (sptListInsert [0, 2, 4, 6] .ln, .ln), .skip, equal1Location, 2))
        (some equalLocation) [1, 3] none,
      .ite .equal 5 (.imm 1) .skip (.return 0 [5]),
      .assign 2 (.op .sub [.var 2, .const 1]),
      .assign 4 (.op .add [.var 4, .const bytes]),
      .assign 6 (.op .add [.var 6, .const bytes]),
      .call none (some equal1Location) [0, 2, 4, 6] none])
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
  if location = fromListLocation then
    let maxout (bits shift dest src : Nat) : WordLangProgHOL (BitVec width) :=
      let max := 2 ^ bits - 1
      .ite .lower src (.imm (BitVec.ofNat width max))
        (.assign dest (.op .or [.var dest, shiftN .lsl (.var src) shift]))
        (.assign dest (.op .or [.var dest, .const (BitVec.ofNat width (max * 2 ^ shift))]))
    let ptr := listSeq [
      .assign 3 (.op .or [.const 1, shiftN .lsl (.op .sub [.lookup .nextFree, .lookup .currHeap])
        (shiftLength conf - wordShiftAmount width)]),
      maxout conf.tagBits (1 + conf.lenBits) 3 9,
      maxout conf.lenBits 1 3 7]
    let limit := min (2 ^ conf.lenSize) (2 ^ width / 16)
    some (4, .ite .equal 2 (.imm 0)
      (listSeq [.assign 6 (.op .add [.var 6, .const 2]), .return 0 [6]])
      (listSeq [
        .ite .test 2 (.imm 1) .skip giveUp,
        .assign 1 (.var 2), allocVar conf limit (sptListInsert [0, 1, 2] .ln),
        .assign 1 (.lookup .nextFree),
        .assign 5 (.op .or [shiftN .lsl (.var 2) (width - conf.lenSize - 2), .const 3, .var 6]),
        .assign 7 (shiftN .lsr (.var 2) 2), .assign 9 (shiftN .lsr (.var 6) 4),
        ptr, .call none (some fromList1Location) [0, 1, 4, 2, 3, 5] none]))
  else if location = refArrayLocation then
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
  else if location = appendLocation then
    match encodeHeader (width := width) conf 0 2 with
    | none => some (3, .skip)
    | some header =>
        let mask := BitVec.ofNat width (2 ^ smallShiftLength conf - 1)
        let ptr := (pointerBits conf 0 2 &&& mask) ||| 1
        some (3, .ite .test 4 (.imm 1) (.return 0 [2]) (listSeq [
          .set (.temp 0) (.var 2), .set (.temp 1) (.var 4),
          .assign 1 (.lookup .nextFree), .assign 3 (.const header),
          .assign 5 (.op .sub [.lookup .triggerGC, .var 1]),
          .assign 7 (.op .or [shiftN .lsl (.op .sub [.var 1, .lookup .currHeap])
            (shiftLength conf - wordShiftAmount width), .const ptr]),
          .set (.temp 2) (.var 7),
          .call none (some appendMainLoopLocation) [0, 1, 4, 3, 5, 7] none]))
  else if location = appendMainLoopLocation then
    let bytes := BitVec.ofNat width (width / 8)
    some (6, listSeq [
      .assign 1 (realAddr conf 4),
      .assign 3 (.load (.op .add [.var 1, .const bytes])),
      .assign 5 (.load (.op .add [.var 1, .const (2 * bytes)])),
      .ite .lower 8 (.imm (3 * bytes))
        (.seq (.assign 1 (.const 0)) (.call none (some appendLenLoopLocation) [0, 4, 1] none)) .skip,
      .store (.var 2) 6, .store (.op .add [.var 2, .const bytes]) 3,
      .ite .test 5 (.imm 1) .skip (listSeq [
        .assign 10 (.op .add [.var 10, .const (BitVec.ofNat width (3 * 2 ^ shiftLength conf))]),
        .assign 8 (.op .sub [.var 8, .const (3 * bytes)]),
        .store (.op .add [.var 2, .const (2 * bytes)]) 10,
        .assign 2 (.op .add [.var 2, .const (3 * bytes)]),
        .call none (some appendMainLoopLocation) [0, 2, 5, 6, 8, 10] none]),
      .assign 1 (.lookup (.temp 0)), .assign 3 (.lookup (.temp 2)),
      .store (.op .add [.var 2, .const (2 * bytes)]) 1,
      .set .nextFree (.op .add [.var 2, .const (3 * bytes)]), .return 0 [3]])
  else if location = appendLenLoopLocation then
    let bytes := BitVec.ofNat width (width / 8)
    some (3, .ite .test 2 (.imm 1) (listSeq [
      .assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree]),
      .assign 1 (.op .add [.var 4, shiftVar .lsr 1 (wordShiftAmount width - 2)]),
      .assign 4 (.lookup (.temp 0)), .assign 2 (.lookup (.temp 1)),
      allocVar conf (2 ^ width / 8 - 1) (sptListInsert [0, 1] .ln),
      .call none (some appendLocation) [0, 4, 2] none]) (listSeq [
        .assign 2 (.load (.op .add [realAddr conf 2, .const (2 * bytes)])),
        .assign 4 (.op .add [.var 4, .const 12]),
        .call none (some appendLenLoopLocation) [0, 2, 4] none]))
  else if location = installCodeLocation then
    let bytes := BitVec.ofNat width (width / 8)
    some (4, .ite .test 2 (.imm 1)
      (.seq (.assign 2 (.lookup .bitmapBuffer)) (.call none (some installDataLocation) [0, 2, 4, 6] none))
      (listSeq [.assign 3 (realAddr conf 2),
        .assign 2 (.load (.op .add [.var 3, .const bytes])),
        .assign 2 (shiftVar .lsr 2 2), .codeBufferWrite 6 2,
        .assign 6 (.op .add [.var 6, .const 1]),
        .assign 2 (.load (.op .add [.var 3, .const (2 * bytes)])),
        .call none (some installCodeLocation) [0, 2, 4, 6] none]))
  else if location = installDataLocation then
    let bytes := BitVec.ofNat width (width / 8)
    some (4, .ite .test 4 (.imm 1)
      (.call none (some installLocation) [0, 2, 6] none)
      (listSeq [.assign 3 (realAddr conf 4),
        .assign 4 (.load (.op .add [.var 3, .const bytes])), .assign 4 (realAddr conf 4),
        .assign 4 (.load (.op .add [.var 4, .const bytes])), .dataBufferWrite 2 4,
        .assign 2 (.op .add [.var 2, .const bytes]),
        .assign 4 (.load (.op .add [.var 3, .const (2 * bytes)])),
        .call none (some installDataLocation) [0, 2, 4, 6] none]))
  else if location = compareLocation then
    let result (n : Nat) := WordLangProgHOL.seq (.assign 2 (.const (BitVec.ofNat width n))) (.return 0 [2])
    some (3, .ite .test 2 (.imm 1)
      (listSeq [.assign 1 (.load (realAddr conf 4)), .ite .test 1 (.imm 16) (result 0) (result 2)])
      (.ite .test 4 (.imm 1)
        (listSeq [.assign 1 (.load (realAddr conf 2)), .ite .test 1 (.imm 16) (result 2) (result 0)])
        (listSeq [.assign 11 (realAddr conf 2), .assign 1 (.load (.var 11)),
          .assign 13 (realAddr conf 4), .assign 3 (.load (.var 13)),
          .assign 6 (shiftN .lsr (.var 1) (width - conf.lenSize)),
          .assign 8 (shiftN .lsr (.var 3) (width - conf.lenSize)),
          .ite .equal 1 (.reg 3)
            (listSeq [.assign 2 (.op .add [.var 11, shiftN .lsl (.var 6) (wordShiftAmount width)]),
              .assign 4 (.op .add [.var 13, shiftN .lsl (.var 6) (wordShiftAmount width)]),
              .ite .test 1 (.imm 16) (.call none (some compare1Location) [0, 6, 2, 4] none)
                (.call none (some compare1Location) [0, 6, 4, 2] none)])
            (.ite .test 1 (.imm 16)
              (.ite .test 3 (.imm 16) (.ite .lower 6 (.reg 8) (result 0) (result 2)) (result 2))
              (.ite .test 3 (.imm 16) (result 0) (.ite .lower 6 (.reg 8) (result 2) (result 0))))])))
  else if location = equalLocation then
    let bytes := BitVec.ofNat width (width / 8)
    let result (n : Nat) := WordLangProgHOL.seq (.assign 2 (.const (BitVec.ofNat width n))) (.return 0 [2])
    let tagMask := BitVec.ofNat width (((2 ^ (width - conf.lenSize) - 1) / 4) * 4) ||| 2
    some (3, listSeq [
      .ite .equal 2 (.reg 4) (result 1) .skip,
      .assign 1 (.op .and [.var 2, .var 4]), .ite .test 1 (.imm 1) (result 0) .skip,
      .assign 20 (realAddr conf 2), .assign 40 (realAddr conf 4),
      .assign 21 (.load (.var 20)), .assign 41 (.load (.var 40)),
      .ite .test 21 (.imm 12) (listSeq [
        .assign 1 (.op .and [.var 21, .const tagMask]),
        .ite .equal 1 (.imm 482) (result 1) .skip,
        .ite .equal 1 (.imm 498) (result 1) .skip,
        .ite .equal 21 (.reg 41) .skip (result 0),
        .assign 6 (shiftVar .lsr 21 (width - conf.lenSize)),
        .assign 20 (.op .add [.var 20, .const bytes]), .assign 40 (.op .add [.var 40, .const bytes]),
        .call none (some equal1Location) [0, 6, 20, 40] none]) .skip,
      .ite .equal 21 (.reg 41) .skip (result 0), .ite .test 21 (.imm 4) (result 0) .skip,
      .assign 1 (.op .and [.var 21, .const 24]), .ite .equal 1 (.imm 16) (result 0) .skip,
      .assign 6 (shiftVar .lsr 21 (width - conf.lenSize)),
      .assign 2 (.op .add [.var 20, shiftVar .lsl 6 (wordShiftAmount width)]),
      .assign 4 (.op .add [.var 40, shiftVar .lsl 6 (wordShiftAmount width)]),
      .call none (some compare1Location) [0, 6, 2, 4] none])
  else compileStub? location

end Flapjack.Compiler.Backend.DataToWord
