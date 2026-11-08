import Flapjack.Compiler.Backend.DataLang.Syntax
import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.DataToWord.Numbers
import Flapjack.Compiler.Backend.DataToWord.Header
import Flapjack.Compiler.Backend.DataToWord.Build
import Flapjack.Compiler.Backend.DataToWord.Locations
import Flapjack.Compiler.Backend.DataToWord.Variables
import Flapjack.Compiler.Backend.DataToWord.WordOp
import Flapjack.Pancake.WordLang

/-! Checked control-flow cases of data-to-word compilation. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- Sequence word programs, avoiding a trailing `Skip` on a nonempty list. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "list_Seq_def"
  (words_as_type_indexed_bitvec)]
def wordListSeq {width : Nat} [NeZero width] :
    List (WordLangProgHOL (BitVec width)) → WordLangProgHOL (BitVec width)
  | [] => .skip
  | [x] => x
  | x :: y :: xs => .seq x (wordListSeq (y :: xs))

/-- Store registers at consecutive word-sized offsets from a base register. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "StoreEach_def"
  (words_as_type_indexed_bitvec)]
def storeEach {width : Nat} [NeZero width] (base : Nat) : List Nat → BitVec width → WordLangProgHOL (BitVec width)
  | [], _ => .skip
  | x :: xs, offset => .seq (.store (.op .add [.var base, .const offset]) x)
      (storeEach base xs (offset + (wordSemBytesInWord : BitVec width)))

/-- Compare consecutive memory words against a constant layout. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "MemEqList_def"
  (words_as_type_indexed_bitvec)]
def memEqList {width : Nat} [NeZero width] (offset : BitVec width) :
    List (BitVec width) → WordLangProgHOL (BitVec width)
  | [] => .assign 1 (.const 18)
  | w :: ws => .seq (.assign 5 (.load (.op .add [.var 3, .const offset])))
      (.ite .equal 5 (.imm w) (memEqList (offset + (wordSemBytesInWord : BitVec width)) ws) .skip)

/-- Emit the optional allocation diagnostic FFI call. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "SilentFFI_def"
  (words_as_type_indexed_bitvec)]
def silentFfi {width : Nat} [NeZero width] (conf : Config) (n : Nat) (names : WordLangCutsetsHOL) :
    WordLangProgHOL (BitVec width) :=
  if conf.callEmptyFfi then
    wordListSeq [.assign n (.const 0),
      .assign 7 (.op .sub [.lookup .nextFree, .lookup .currHeap]),
      .assign 9 (.lookup .heapLength), .ffi (.implode []) 7 n 9 n names]
  else .skip

/-- Original allocation-failure sequence used by the data-to-word pass. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "GiveUp_def"
  (words_as_type_indexed_bitvec)]
def giveUp {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) :=
  .seq (.assign 1 (.const (-1))) (.alloc 1 (adjustSets (.ln : NumSet)))

/-- Construct a word-language heap address from a tagged pointer, following
the original three branches for the architecture and pointer layout. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "real_addr_def"
  (words_as_type_indexed_bitvec)]
def realAddr {width : Nat} [NeZero width] (conf : Config) (r : Nat) : WordLangExpHOL (BitVec width) :=
  let k := wordShiftAmount width
  let l := shiftLength conf
  let offset := if k = l ∧ conf.lenBits = 0 ∧ conf.tagBits = 0 then
      WordLangExpHOL.op .sub [.var r, .const 1]
    else if k ≤ conf.padBits + 1 then
      WordLangExpHOL.shift .lsr (.var r) (.const (BitVec.ofNat width (l - k)))
    else WordLangExpHOL.shift .lsl
      (.shift .lsr (.var r) (.const (BitVec.ofNat width l))) (.const (BitVec.ofNat width k))
  .op .add [.lookup .currHeap, offset]

/-- Internal helper for supported comparisons; the source `SetBool` uses an
already adjusted destination and remains a separate unported declaration. -/
private def boolResult {width : Nat} (dest : Nat) (cmp : Cmp) (r : Nat)
    (other : WordRegImm (BitVec width)) : WordLangProgHOL (BitVec width) :=
  .ite cmp r other (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2))

/-- Internal constructor for HOL's `ShiftN` overload. -/
def shiftN {width : Nat} (op : Shift) (e : WordLangExpHOL (BitVec width)) (n : Nat) :
    WordLangExpHOL (BitVec width) := .shift op e (.const (BitVec.ofNat width n))

/-- Construct a variable shift with the original rotate and saturation rules. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "ShiftVar_def"
  (words_as_type_indexed_bitvec)]
def shiftVar {width : Nat} [NeZero width] (op : Shift) (v n : Nat) : WordLangExpHOL (BitVec width) :=
  match op with
  | .ror =>
      let m := if n < width then n else n % width
      if m = 0 then .var v else shiftN .ror (.var v) m
  | _ =>
      if n = 0 then .var v
      else if width ≤ n then
        match op with
        | .asr => shiftN .asr (.var v) (width - 1)
        | _ => .const 0
      else shiftN op (.var v) n

/-- Storage sequence shared by the checked 64-bit word operations. -/
private def writeWord64 {width : Nat} [NeZero width] (conf : Config) (header : BitVec width)
    (dest : Nat) : WordLangProgHOL (BitVec width) :=
  let bytes := (wordSemBytesInWord : BitVec width)
  wordListSeq [
    .assign 1 (.lookup .nextFree), .store (.op .add [.var 1, .const bytes]) 3,
    .assign 3 (.const header), .store (.var 1) 3,
    .set .nextFree (.op .add [.var 1, .const (2 * bytes)]),
    .assign (adjustVar dest) (.op .or [
      shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
      .const 1])]

/-- Two-word representation used when lowering Word64 onto a 32-bit target.
The standalone HOL helper is not yet independently reviewed as a port. -/
private def writeWord64On32 {width : Nat} [NeZero width] (conf : Config) (header : BitVec width)
    (dest high low : Nat) : WordLangProgHOL (BitVec width) :=
  let bytes := (wordSemBytesInWord : BitVec width)
  wordListSeq [
    .assign 1 (.lookup .nextFree), .store (.op .add [.var 1, .const bytes]) low,
    .store (.op .add [.var 1, .const (2 * bytes)]) high,
    .assign 3 (.const header), .store (.var 1) 3,
    .set .nextFree (.op .add [.var 1, .const (3 * bytes)]),
    .assign (adjustVar dest) (.op .or [
      shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
      .const 1])]

/-- Select the floating-point comparison instruction and operand order. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "fp_cmp_inst_def"]
def fpCmpInst : FpCmp → WordLangFp
  | .less => .fpLess 3 0 1
  | .lessEqual => .fpLessEqual 3 0 1
  | .greater => .fpLess 3 1 0
  | .greaterEqual => .fpLessEqual 3 1 0
  | .equal => .fpEqual 3 0 1

/-- Select the floating-point binary arithmetic instruction. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "fp_bop_inst_def"]
def fpBopInst : FpBop → WordLangFp
  | .add => .fpAdd 0 0 1
  | .sub => .fpSub 0 0 1
  | .mul => .fpMul 0 0 1
  | .div => .fpDiv 0 0 1

/-- Select the floating-point unary arithmetic instruction. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "fp_uop_inst_def"]
def fpUopInst : FpUop → WordLangFp
  | .abs => .fpAbs 1 0
  | .neg => .fpNeg 1 0
  | .sqrt => .fpSqrt 1 0

/-- Select the floating-point ternary arithmetic instruction. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "fp_top_inst_def"]
def fpTopInst : FpTop → WordLangFp
  | .fma => .fpFma 0 1 2

/-- Operand layout for the floating-point lowering sequences. -/
private def fpOperand (source position : Nat) : Nat × Nat × Nat × Nat × Nat × Nat :=
  match position with
  | 0 => (source, 3, 15, 11, 13, 0)
  | 1 => (source, 5, 17, 21, 23, 1)
  | _ => (source, 7, 19, 31, 33, 2)

/-- Load floating-point operands in the order used by the source compiler. -/
private def fpLoads {width : Nat} [NeZero width] (conf : Config) (sources : List Nat) :
    List (WordLangProgHOL (BitVec width)) :=
  let operands := sources.zipIdx |>.map fun (source, position) => fpOperand source position
  let bytes := (wordSemBytesInWord : BitVec width)
  if width = 64 then
    (operands.map fun (source, reg, _, _, _, _) =>
      .assign reg (.load (.op .add [realAddr conf (adjustVar source), .const bytes]))) ++
    (operands.map fun (_, reg, _, _, _, fp) => .inst (.fp (.fpMovFromReg fp reg reg)))
  else
    (operands.map fun (source, _, addr, _, _, _) => .assign addr (realAddr conf (adjustVar source))) ++
    (operands.flatMap fun (_, _, addr, low, high, _) => [
      .assign low (.load (.op .add [.var addr, .const bytes])),
      .assign high (.load (.op .add [.var addr, .const (2 * bytes)]))]) ++
    (operands.map fun (_, _, _, low, high, fp) => .inst (.fp (.fpMovFromReg fp high low)))

/-- Emit a floating-point result allocation after its instruction. -/
private def fpResult {width : Nat} [NeZero width] (conf : Config) (dest : Nat)
    (sources : List Nat) (operation : WordLangFp) (resultFp : Nat) : WordLangProgHOL (BitVec width) :=
  let words := if width = 64 then 1 else 2
  match encodeHeader (width := width) conf 3 words with
  | none => giveUp
  | some header =>
    let transfer := if width = 64 then .fpMovToReg 3 5 resultFp else .fpMovToReg 5 3 resultFp
    let store := if width = 64 then writeWord64 conf header dest else writeWord64On32 conf header dest 5 3
    wordListSeq (fpLoads conf sources ++ [.inst (.fp operation), .inst (.fp transfer), store])

/-- Internal tag-mask construction used by checked word lowering. -/
def tagMask {width : Nat} (conf : Config) : BitVec width :=
  BitVec.ofNat width (((2 ^ (width - conf.lenSize) - 1) / 4) * 4)

/-- Internal pointer-field program used by the checked allocation cases. -/
def makePtrBitsCode {width : Nat} [NeZero width] (conf : Config) (tag len dest : Nat) :
    WordLangProgHOL (BitVec width) :=
  let maxout (bits shift src : Nat) : WordLangProgHOL (BitVec width) :=
    let max := 2 ^ bits - 1
    .ite .lower src (.imm (BitVec.ofNat width max))
      (.assign dest (.op .or [.var dest, shiftN .lsl (.var src) shift]))
      (.assign dest (.op .or [.var dest, .const (BitVec.ofNat width (max * 2 ^ shift))]))
  wordListSeq [
    .assign dest (.op .or [.const 1, shiftN .lsl (.op .sub [.lookup .nextFree, .lookup .currHeap])
      (shiftLength conf - wordShiftAmount width)]),
    maxout conf.tagBits (1 + conf.lenBits) tag, maxout conf.lenBits 1 len]

/-- Construct the variable-allocation sequence used for reference arrays. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "AllocVar_def"
  (words_as_type_indexed_bitvec)]
def allocVar {width : Nat} [NeZero width] (conf : Config) (limit : Nat) (names : NumSet) :
    WordLangProgHOL (BitVec width) :=
  let cutsets := adjustSets names
  let ffiCutsets := (cutsets.1, sptInsert 1 () cutsets.2)
  wordListSeq [
    .assign 1 (shiftN .lsr (.var 1) 2),
    .ite .lower 1 (.imm (BitVec.ofNat width limit))
      (.assign 1 (shiftN .lsl (.op .add [.var 1, .const 1]) (wordShiftAmount width)))
      (.assign 1 (.const (-1))),
    .assign 3 (.op .sub [.lookup .triggerGC, .lookup .nextFree]),
    .ite .lower 3 (.reg 1)
      (wordListSeq [silentFfi conf 3 ffiCutsets, .alloc 1 cutsets, silentFfi conf 3 cutsets]) .skip]

/-- Shared constructor lowering for immutable and non-generational mutable
blocks. This is bounded-path infrastructure, not a separately reviewed port. -/
private def compileCons {width : Nat} [NeZero width] (conf : Config) (l dest tag : Nat)
    (args : List Nat) : WordLangProgHOL (BitVec width) × Nat :=
  if args.isEmpty then
    if tag < 2 ^ width / 16 then
      (.assign (adjustVar dest) (.const (BitVec.ofNat width (16 * tag + 2))), l)
    else (giveUp, l)
  else match encodeHeader (width := width) conf (4 * tag) args.length with
    | none => (giveUp, l)
    | some header =>
        let bytes := (wordSemBytesInWord : BitVec width) * BitVec.ofNat width (args.length + 1)
        let pointer := getLowerBits conf (.word (ptrBits conf tag args.length))
        (wordListSeq [
          .assign 1 (.lookup .nextFree), .assign 3 (.const header),
          storeEach 1 (3 :: args.map adjustVar) 0,
          .assign (adjustVar dest) (.op .or [
            shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
            .const pointer]),
          .set .nextFree (.op .add [.var 1, .const bytes])], l)

/-- Lower an integer constant into its tagged word representation. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "assign_Const_def"
  (words_as_type_indexed_bitvec)]
def assignConst {width : Nat} [NeZero width] (i : Int) (l dest : Nat) :
    WordLangProgHOL (BitVec width) × Nat :=
  if i < 0 then
    (.assign (adjustVar dest) (.const (0 - BitVec.ofNat width (4 * (0 - i)).toNat)), l)
  else
    (.assign (adjustVar dest) (.const (BitVec.ofNat width (4 * i).toNat)), l)

/-- Apply a unary assignment when its argument list has exactly one element. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "arg1_def"]
def arg1 {α β : Type} (args : List α) (f : α → β) (fallback : β) : β :=
  match args with
  | [arg] => f arg
  | _ => fallback

/-- Apply a binary assignment when its argument list has exactly two elements. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "arg2_def"]
def arg2 {α β : Type} (args : List α) (f : α → α → β) (fallback : β) : β :=
  match args with
  | [first, second] => f first second
  | _ => fallback

/-- Apply a ternary assignment only to an argument list of length three. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "arg3_def"]
def arg3 {α β : Type} (args : List α) (f : α → α → α → β) (fallback : β) : β :=
  match args with
  | [first, second, third] => f first second third
  | _ => fallback

/-- Construct the word offset of a block element. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "real_offset_def"
  (words_as_type_indexed_bitvec)]
def realOffset {width : Nat} [NeZero width] (_conf : Config) (r : Nat) :
    WordLangExpHOL (BitVec width) :=
  .op .add [.const wordSemBytesInWord,
    if width = 32 then .var r else shiftN .lsl (.var r) 1]

/-- Construct the word-language byte offset for a tagged index. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "real_byte_offset_def"
  (words_as_type_indexed_bitvec)]
def realByteOffset {width : Nat} [NeZero width] (r : Nat) : WordLangExpHOL (BitVec width) :=
  .op .add [.const wordSemBytesInWord, shiftN .lsr (.var r) 2]

/-- Load a block element at a dynamic index. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "assign_El_def"
  (words_as_type_indexed_bitvec)]
def assignEl {width : Nat} [NeZero width] (conf : Config) (l dest base index : Nat) :
    WordLangProgHOL (BitVec width) × Nat :=
  (.assign (adjustVar dest) (.load (.op .add [realAddr conf (adjustVar base),
    realOffset conf (adjustVar index)])), l)

/-- Load a block element at a constant index. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "assign_ElemAt_def"
  (words_as_type_indexed_bitvec)]
def assignElemAt {width : Nat} [NeZero width] (conf : Config) (n l dest src : Nat) :
    WordLangProgHOL (BitVec width) × Nat :=
  let bytes := (wordSemBytesInWord : BitVec width)
  (.assign (adjustVar dest) (.load (.op .add [realAddr conf (adjustVar src),
    .const (bytes + bytes * BitVec.ofNat width n)])), l)

/-- Load a byte and convert it to a tagged small integer. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "assign_DerefByte_def"
  (words_as_type_indexed_bitvec)]
def assignDerefByte {width : Nat} [NeZero width] (conf : Config) (l dest base index : Nat) :
    WordLangProgHOL (BitVec width) × Nat :=
  (wordListSeq [
    .assign 1 (.op .add [realAddr conf (adjustVar base), realByteOffset (adjustVar index)]),
    .inst (.mem .load8 3 (.addr 1 0)),
    .assign (adjustVar dest) (shiftN .lsl (.var 3) 2)], l)

/-- Store a word-valued block element and return unit. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "assign_Update_def"
  (words_as_type_indexed_bitvec)]
def assignUpdate {width : Nat} [NeZero width] (conf : Config) (l dest base index value : Nat) :
    WordLangProgHOL (BitVec width) × Nat :=
  (.seq (.store (.op .add [realAddr conf (adjustVar base), realOffset conf (adjustVar index)])
      (adjustVar value)) (.assign (adjustVar dest) (.const 2)), l)

/-- Store the byte represented by a tagged small integer and return unit. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "assign_UpdateByte_def"
  (words_as_type_indexed_bitvec)]
def assignUpdateByte {width : Nat} [NeZero width] (conf : Config) (l dest base index value : Nat) :
    WordLangProgHOL (BitVec width) × Nat :=
  (wordListSeq [
    .assign 1 (.op .add [realAddr conf (adjustVar base), realByteOffset (adjustVar index)]),
    .assign 3 (shiftN .lsr (.var (adjustVar value)) 2),
    .inst (.mem .store8 3 (.addr 1 0)),
    .assign (adjustVar dest) (.const 2)], l)

/-- Set the globals pointer and its derived real address. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "assign_SetGlobalsPtr_def"
  (words_as_type_indexed_bitvec)]
def assignSetGlobalsPtr {width : Nat} [NeZero width] (conf : Config) (l dest src : Nat) :
    WordLangProgHOL (BitVec width) × Nat :=
  (.seq (.set .globals (.var (adjustVar src)))
    (.seq (.set .globReal (realAddr conf (adjustVar src)))
      (.assign (adjustVar dest) (.const 2))), l)

/-- Load a global slot from the real globals pointer. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "assign_Global_def"
  (words_as_type_indexed_bitvec)]
def assignGlobal {width : Nat} [NeZero width] (_conf : Config) (n l dest : Nat) :
    WordLangProgHOL (BitVec width) × Nat :=
  let offset := (wordSemBytesInWord : BitVec width) * BitVec.ofNat width (n + 1)
  (.assign (adjustVar dest) (.load (.op .add [.lookup .globReal, .const offset])), l)

/-- Store a global slot and return the unit value. -/
@[hol "cakeml/compiler/backend/data_to_wordScript.sml" "assign_SetGlobal_def"
  (words_as_type_indexed_bitvec)]
def assignSetGlobal {width : Nat} [NeZero width] (_conf : Config) (n l dest src : Nat) :
    WordLangProgHOL (BitVec width) × Nat :=
  let offset := (wordSemBytesInWord : BitVec width) * BitVec.ofNat width (n + 1)
  (.seq (.store (.op .add [.lookup .globReal, .const offset]) (adjustVar src))
    (.assign (adjustVar dest) (.const 2)), l)

/-- Flapjack's checked traversal. Some non-64-bit operations return `none`;
this definition has not yet been reviewed as HOL's total `comp`. -/
def compileControl? {width : Nat} [NeZero width] (conf : Config) (secn : Nat) :
    Nat → DataLang.Prog → Option (WordLangProgHOL (BitVec width) × Nat)
  | l, .skip => some (.skip, l)
  | l, .tick => some (.tick, l)
  | l, .raise n => some (.raise (adjustVar n), l)
  | l, .return ns => some (.return 0 (ns.map adjustVar), l)
  | l, .move dst src => some (.move 0 [(adjustVar dst, adjustVar src)], l)
  | l, .seq x y => do
      let (x, l) ← compileControl? conf secn l x
      let (y, l) ← compileControl? conf secn l y
      pure (.seq x y, l)
  | l, .ifThenElse n x y => do
      let (x, l) ← compileControl? conf secn l x
      let (y, l) ← compileControl? conf secn l y
      pure (.ite .equal (adjustVar n) (.imm 18) x y, l)
  | l, .makeSpace n names =>
      let bytes := n * (width / 8)
      let value := BitVec.ofNat width bytes
      let value := if value.toNat = bytes then value else (-1 : BitVec width)
      let cutsets := adjustSets names
      some (.seq (.assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree]))
        (.ite .lower 1 (.imm value)
          (wordListSeq [silentFfi conf 3 cutsets, .assign 1 (.const value),
            .alloc 1 cutsets, silentFfi conf 3 cutsets]) .skip), l)
  | l, .assign dest (.intOp (.const i)) _ _ =>
      some (assignConst i l dest)
  | l, .assign dest (.globOp .globalsPtr) _ _ =>
      some (.assign (adjustVar dest) (.lookup .globals), l)
  | l, .assign dest (.globOp .setGlobalsPtr) args _ =>
      some (arg1 args (assignSetGlobalsPtr conf l dest) (.skip, l))
  | l, .assign dest (.globOp (.global n)) _ _ =>
      some (assignGlobal conf n l dest)
  | l, .assign dest (.globOp (.setGlobal n)) args _ =>
      some (arg1 args (assignSetGlobal conf n l dest) (.skip, l))
  | l, .assign dest (.blockOp (.build parts)) _ _ =>
      if width != 32 && width != 64 then none else
      match Build.partsWords (width := width) conf parts with
      | none => some (giveUp, l)
      | some ((relative, value), words) =>
          let final : WordLangProgHOL (BitVec width) := .seq (.set .nextFree (.var 1))
            (.assign (adjustVar dest) (if relative then .op .add [.const value, .var 3] else .const value))
          let store := if words.isEmpty then final else .seq (.storeConsts 1 3 1 3 words) final
          some (wordListSeq [.assign 1 (.lookup .nextFree),
            .assign 3 (shiftN .lsl (.op .sub [.var 1, .lookup .currHeap])
              (shiftLength conf - wordShiftAmount width)), store], l)
  | l, .assign dest (.blockOp (.fromList tag)) args names =>
      match args with
      | [x, y] => match encodeHeader (width := width) conf (4 * tag) 0 with
        | none => some (giveUp, l)
        | some _ => some (.mustTerminate (wordListSeq [
            .assign 1 (.const (BitVec.ofNat width (16 * tag))),
            .call (some ([adjustVar dest], adjustSets (names.getD .ln), .skip, secn, l))
              (some fromListLocation) [adjustVar x, adjustVar y, 1] none]), l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp .listAppend) args names =>
      match args with
      | [first, second] =>
          match encodeHeader (width := width) conf 0 2 with
          | none => some (giveUp, l)
          | some _ => some (.mustTerminate (.call
              (some ([adjustVar dest], adjustSets (names.getD .ln), .skip, secn, l))
              (some appendLocation) [adjustVar second, adjustVar first] none), l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp .boolNot) args _ =>
      match args with
      | [src] => some (.assign (adjustVar dest) (.op .xor [.var (adjustVar src), .const 16]), l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp .lengthBlock) args _ =>
      match args with
      | [src] =>
          let header := WordLangExpHOL.load (realAddr conf (adjustVar src))
          let length := shiftN .lsl (shiftN .lsr header (width - conf.lenSize)) 2
          some (.ite .test (adjustVar src) (.imm 1) (.assign (adjustVar dest) (.const 0))
            (.assign (adjustVar dest) length), l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp (.lenEq len)) args _ =>
      match args with
      | [src] =>
          let src := adjustVar src
          if len = 0 then
            some (boolResult dest .test src (.imm 1), l)
          else if len < 2 ^ conf.lenBits - 1 then
            let mask := BitVec.ofNat width (2 ^ (conf.lenBits + 1) - 1)
            let bits := ptrBits conf 0 len ||| 1
            some (.seq (.assign 1 (.op .and [.var src, .const mask]))
              (boolResult dest .equal 1 (.imm bits)), l)
          else if len < 2 ^ width then
            some (wordListSeq [
              .assign 1 (.const 0),
              .ite .test src (.imm 1) .skip
                (.assign 1 (shiftN .lsr (.load (realAddr conf src)) (width - conf.lenSize))),
              boolResult dest .equal 1 (.imm (BitVec.ofNat width len))], l)
          else some (.assign (adjustVar dest) (.const 2), l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp (.tagLenEq tag len)) args _ =>
      match args with
      | [src] =>
          let src := adjustVar src
          if len = 0 then
            if tag < 2 ^ width / 16 then
              some (boolResult dest .equal src (.imm (BitVec.ofNat width (16 * tag + 2))), l)
            else some (.assign (adjustVar dest) (.const 2), l)
          else if tag < 2 ^ conf.tagBits - 1 ∧ len < 2 ^ conf.lenBits - 1 then
            let mask := BitVec.ofNat width (2 ^ (conf.lenBits + conf.tagBits + 1) - 1)
            let bits := (BitVec.ofNat width tag <<< (1 + conf.lenBits)) |||
              (BitVec.ofNat width len <<< 1) ||| 1
            some (.seq (.assign 1 (.op .and [.var src, .const mask]))
              (boolResult dest .equal 1 (.imm bits)), l)
          else
            match encodeHeader (width := width) conf (4 * tag) len with
            | none => some (.assign (adjustVar dest) (.const 2), l)
            | some header => some (wordListSeq [
                .assign 1 (.const 0),
                .ite .test src (.imm 1) .skip (.assign 1 (.load (realAddr conf src))),
                boolResult dest .equal 1 (.imm header)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp (.tagEq tag)) args _ =>
      match args with
      | [src] =>
          let src := adjustVar src
          if tag < 2 ^ width / 16 then
            some (wordListSeq [
              .assign 1 (.var src),
              .ite .test src (.imm 1) .skip
                (.assign 1 (.op .and [.load (realAddr conf src), .const (tagMask conf ||| 2)])),
              boolResult dest .equal 1 (.imm (BitVec.ofNat width (16 * tag + 2)))], l)
          else some (.assign (adjustVar dest) (.const 2), l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp (.boolTest _)) args _ =>
      match args with
      | [x, y] => some (boolResult dest .equal (adjustVar x) (.reg (adjustVar y)), l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp .equal) args names =>
      match args with
      | [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          some (wordListSeq [
            .assign 1 (.var (adjustVar x)), .assign 3 (.var (adjustVar y)),
            .assign 5 (.op .and [.var 1, .var 3]),
            .ite .test 5 (.imm 1) .skip
              (.ite .equal 1 (.reg 3) .skip
                (.seq (.mustTerminate (.call (some ([1], cutsets, .skip, secn, l))
                  (some equalLocation) [1, 3] none)) (.assign 3 (.const 1)))),
            boolResult dest .equal 1 (.reg 3)], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp (.equalConst part)) args _ =>
      match args with
      | [src] =>
          if width != 32 && width != 64 then none else
          match Build.partWords conf .ln part 0 with
          | none => some (.assign (adjustVar dest) (.const 2), l)
          | some ((false, w), _) => some (boolResult dest .equal (adjustVar src) (.imm w), l)
          | some ((true, _), words) =>
              let words := words.map Prod.snd
              let compare (address : WordLangExpHOL (BitVec width)) (words : List (BitVec width)) :=
                wordListSeq [.assign 1 (.const 2), .assign 3 address, memEqList 0 words,
                  .assign (adjustVar dest) (.var 1)]
              let code := match part with
                | .int _ => .ite .test (adjustVar src) (.imm 1)
                    (.assign (adjustVar dest) (.const 2)) (compare (realAddr conf (adjustVar src)) words)
                | .w64 _ => compare (.op .add [realAddr conf (adjustVar src),
                    .const ((wordSemBytesInWord : BitVec width))]) (words.drop 1)
                | .str _ => compare (realAddr conf (adjustVar src)) words
                | _ => .skip
              some (code, l)
      | _ => some (.skip, l)
  | l, .assign dest (.intOp (.lessConstSmall i)) args _ =>
      match args with
      | [src] => some (boolResult dest .less (adjustVar src) (.imm (BitVec.ofNat width (4 * i))), l)
      | _ => some (.skip, l)
  | l, .assign dest (.intOp .less) args names =>
      match args with
      | [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          some (wordListSeq [
            .assign 1 (.var (adjustVar x)), .assign 3 (.var (adjustVar y)),
            .assign 5 (.op .or [.var 1, .var 3]),
            .ite .test 5 (.imm 1) .skip
              (.seq (.mustTerminate (.call (some ([1], cutsets, .skip, secn, l))
                (some compareLocation) [1, 3] none)) (.assign 3 (.const 1))),
            boolResult dest .less 1 (.reg 3)], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.intOp .lessEq) args names =>
      match args with
      | [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          some (wordListSeq [
            .assign 1 (.var (adjustVar x)), .assign 3 (.var (adjustVar y)),
            .assign 5 (.op .or [.var 1, .var 3]),
            .ite .test 5 (.imm 1) .skip
              (.seq (.mustTerminate (.call (some ([1], cutsets, .skip, secn, l))
                (some compareLocation) [1, 3] none)) (.assign 3 (.const 1))),
            boolResult dest .notLess 3 (.reg 1)], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.intOp op) args names =>
      match op, args with
      | .add, [x, y] | .sub, [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          let (instr, loc) := match op with
            | .add => (WordLangArith.addOverflow 1 (adjustVar x) (adjustVar y) 3, addLocation)
            | _ => (WordLangArith.subOverflow 1 (adjustVar x) (adjustVar y) 3, subLocation)
          some (wordListSeq [
            .inst (.arith instr),
            .assign 3 (.op .or [.var 3, .var (adjustVar x), .var (adjustVar y)]),
            .ite .test 3 (.imm 1) .skip
              (.mustTerminate (.call (some ([1], cutsets, .skip, secn, l))
                (some loc) [adjustVar x, adjustVar y] none)),
            .move 2 [(adjustVar dest, 1)]], l + 1)
      | .add, _ | .sub, _ => some (.skip, l)
      | .mult, [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          some (wordListSeq [
            .assign 1 (shiftVar .lsr (adjustVar x) 1),
            .inst (.arith (.longMul 3 1 1 (adjustVar y))),
            .assign 3 (.op .or [.var 3, .op .and [.const 1, .op .or [.var (adjustVar x), .var (adjustVar y)]]]),
            .assign 1 (shiftVar .lsr 1 1),
            .ite .equal 3 (.imm 0) .skip (.mustTerminate
              (.call (some ([1], cutsets, .skip, secn, l)) (some mulLocation) [adjustVar x, adjustVar y] none)),
            .move 2 [(adjustVar dest, 1)]], l + 1)
      | .div, [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          let fast := if conf.hasDiv then wordListSeq [
              .inst (.arith (.div 1 (adjustVar x) (adjustVar y))),
              .assign (adjustVar dest) (shiftVar .lsl 1 2)]
            else if conf.hasLongdiv then wordListSeq [
              .assign 1 (.const 0), .inst (.arith (.longDiv 1 3 1 (adjustVar x) (adjustVar y))),
              .assign (adjustVar dest) (shiftVar .lsl 1 2)]
            else wordListSeq [
              .assign 1 (.const 0),
              .mustTerminate (.call (some ([1], cutsets, .skip, secn, l + 1))
                (some longDivLocation) [1, adjustVar x, adjustVar y] none),
              .assign (adjustVar dest) (shiftVar .lsl 1 2)]
          some (wordListSeq [
            .assign 1 (.op .or [.var (adjustVar x), .var (adjustVar y)]),
            .assign 1 (.op .or [.var 1, shiftVar .lsr 1 (width - 1)]),
            .ite .test 1 (.imm 1) fast (wordListSeq [
              .mustTerminate (.call (some ([1], cutsets, .skip, secn, l))
                (some divLocation) [adjustVar x, adjustVar y] none),
              .move 2 [(adjustVar dest, 1)]])], l + 2)
      | .mod, [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          let fast := if conf.hasDiv then wordListSeq [
              .inst (.arith (.div 1 (adjustVar x) (adjustVar y))),
              .inst (.arith (.longMul 3 1 1 (adjustVar y))),
              .assign (adjustVar dest) (.op .sub [.var (adjustVar x), .var 1])]
            else if conf.hasLongdiv then wordListSeq [
              .assign 1 (.const 0), .inst (.arith (.longDiv 1 3 1 (adjustVar x) (adjustVar y))),
              .move 2 [(adjustVar dest, 3)]]
            else wordListSeq [
              .assign 1 (.const 0),
              .mustTerminate (.call (some ([1], cutsets, .skip, secn, l + 1))
                (some longDivLocation) [1, adjustVar x, adjustVar y] none),
              .get (adjustVar dest) (.temp 28)]
          some (wordListSeq [
            .assign 1 (.op .or [.var (adjustVar x), .var (adjustVar y)]),
            .assign 1 (.op .or [.var 1, shiftVar .lsr 1 (width - 1)]),
            .ite .test 1 (.imm 1) fast (wordListSeq [
              .mustTerminate (.call (some ([1], cutsets, .skip, secn, l))
                (some modLocation) [adjustVar x, adjustVar y] none),
              .move 2 [(adjustVar dest, 1)]])], l + 2)
      | .mult, _ | .div, _ | .mod, _ => some (.skip, l)
      | _, _ => some (.skip, l)
  | l, .assign dest (.wordOp (.wordTest _ test)) args _ =>
      match args, test with
      | [x, y], .equal => some (boolResult dest .equal (adjustVar x) (.reg (adjustVar y)), l)
      | [x, y], .compare .lt => some (boolResult dest .lower (adjustVar x) (.reg (adjustVar y)), l)
      | [x, y], .compare .leq => some (boolResult dest .notLower (adjustVar y) (.reg (adjustVar x)), l)
      | _, _ => some (.skip, l)
  | l, .assign dest (.wordOp (.fpCmp comparison)) args _ =>
      match args with
      | [left, right] =>
          if !conf.hasFpOps then some (giveUp, l)
          else
            let bytes := (wordSemBytesInWord : BitVec width)
            let finish : List (WordLangProgHOL (BitVec width)) := [
              .inst (.fp (fpCmpInst comparison)),
              .assign (adjustVar dest) (.op .add [shiftVar .lsl 3 4, .const 2])]
            if width = 64 then
              some (wordListSeq ([
                .assign 3 (.load (.op .add [realAddr conf (adjustVar left), .const bytes])),
                .assign 5 (.load (.op .add [realAddr conf (adjustVar right), .const bytes])),
                .inst (.fp (.fpMovFromReg 0 3 3)), .inst (.fp (.fpMovFromReg 1 5 5))] ++ finish), l)
            else
              some (wordListSeq ([
                .assign 15 (realAddr conf (adjustVar left)), .assign 17 (realAddr conf (adjustVar right)),
                .assign 11 (.load (.op .add [.var 15, .const bytes])),
                .assign 13 (.load (.op .add [.var 15, .const (2 * bytes)])),
                .assign 21 (.load (.op .add [.var 17, .const bytes])),
                .assign 23 (.load (.op .add [.var 17, .const (2 * bytes)])),
                .inst (.fp (.fpMovFromReg 0 13 11)), .inst (.fp (.fpMovFromReg 1 23 21))] ++ finish), l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp (.fpBop operation)) args _ =>
      match args with
      | [left, right] => if !conf.hasFpOps then some (giveUp, l)
          else some (fpResult conf dest [left, right] (fpBopInst operation) 0, l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp (.fpUop operation)) args _ =>
      match args with
      | [source] => if !conf.hasFpOps then some (giveUp, l)
          else some (fpResult conf dest [source] (fpUopInst operation) 1, l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp (.fpTop operation)) args _ =>
      match args with
      | [first, second, third] => if !conf.hasFpOps || !conf.hasFpTern then some (giveUp, l)
          else some (fpResult conf dest [first, second, third] (fpTopInst operation) 0, l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp (.wordOpw .w8 op)) args _ =>
      match args with
      | [x, y] =>
          let (binop, carried) := match lookupWordOp op with
            | .bitwise b => (b, false)
            | .carried b => (b, true)
          let value := WordLangExpHOL.op binop [.var (adjustVar x), .var (adjustVar y)]
          let amount := BitVec.ofNat width (width - 10)
          let value := if carried then WordLangExpHOL.shift .lsr (.shift .lsl value (.const amount)) (.const amount)
            else value
          some (.assign (adjustVar dest) value, l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp (.wordOpw .w64 op)) args _ =>
      match args with
      | [x, y] =>
          if width != 64 then none else
          match encodeHeader (width := width) conf 3 1 with
          | none => some (giveUp, l)
          | some header =>
              let binop := match lookupWordOp op with | .bitwise b | .carried b => b
              let bytes := (wordSemBytesInWord : BitVec width)
              let addr (v : Nat) := WordLangExpHOL.op .add [realAddr conf (adjustVar v), .const bytes]
              let stored := wordListSeq [
                .assign 1 (.lookup .nextFree), .store (.op .add [.var 1, .const bytes]) 3,
                .assign 3 (.const header), .store (.var 1) 3,
                .set .nextFree (.op .add [.var 1, .const (2 * bytes)]),
                .assign (adjustVar dest) (.op .or [
                  shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
                  .const 1])]
              some (.seq (.assign 3 (.op binop [.load (addr x), .load (addr y)])) stored, l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp (.wordShift .w8 sh n)) args _ =>
      match args with
      | [src] =>
          let src := adjustVar src
          let amount := min n 8
          let value := match sh with
            | .lsl => shiftN .lsr (shiftN .lsl (.var src) (width - 10 + amount)) (width - 10)
            | .lsr => shiftN .lsl (shiftN .lsr (.var src) (amount + 2)) 2
            | .asr => shiftN .lsl (shiftN .lsr (shiftN .asr (shiftN .lsl (.var src) (width - 10)) amount) (width - 8)) 2
            | .ror =>
                let n := n % 8
                WordLangExpHOL.op .or [shiftN .lsl (shiftVar .lsr src (n + 2)) 2,
                  shiftN .lsr (shiftVar .lsl src ((width - 2) - n)) (width - 10)]
          some (.assign (adjustVar dest) value, l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp (.wordShift .w64 sh n)) args _ =>
      match args with
      | [src] =>
          if width != 64 then none else
          match encodeHeader (width := width) conf 3 1 with
          | none => some (giveUp, l)
          | some header =>
              let bytes := (wordSemBytesInWord : BitVec width)
              let address := WordLangExpHOL.op .add [realAddr conf (adjustVar src), .const bytes]
              let stored := wordListSeq [
                .assign 1 (.lookup .nextFree), .store (.op .add [.var 1, .const bytes]) 3,
                .assign 3 (.const header), .store (.var 1) 3,
                .set .nextFree (.op .add [.var 1, .const (2 * bytes)]),
                .assign (adjustVar dest) (.op .or [
                  shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
                  .const 1])]
              some (wordListSeq [.assign 3 (.load address), .assign 3 (shiftVar sh 3 n), stored], l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp (.wordFromWord narrow)) args _ =>
      match args with
      | [src] =>
          if width != 32 && width != 64 then none else
          let src := adjustVar src
          let bytes := (wordSemBytesInWord : BitVec width)
          if narrow then
            let offset := if width = 32 then 2 * bytes else bytes
            some (wordListSeq [
              .assign 1 (realAddr conf src),
              .assign 1 (.load (.op .add [.var 1, .const offset])),
              .assign 1 (.op .and [.var 1, .const 255]),
              .assign (adjustVar dest) (shiftVar .lsl 1 2)], l)
          else
            let count := if width < 64 then 2 else 1
            match encodeHeader (width := width) conf 3 count with
            | none => some (giveUp, l)
            | some header =>
                if width < 64 then
                  some (wordListSeq [.assign 5 (shiftN .lsr (.var src) 2),
                    .assign 3 (.const 0), writeWord64On32 conf header dest 5 3], l)
                else some (.seq (.assign 3 (shiftN .lsr (.var src) 2))
                    (writeWord64 conf header dest), l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp .wordFromInt) args _ =>
      match args with
      | [src] =>
          if width != 64 then none else
          match encodeHeader (width := width) conf 3 1 with
          | none => some (giveUp, l)
          | some header =>
              let src := adjustVar src
              let bytes := (wordSemBytesInWord : BitVec width)
              let loadBignum := wordListSeq [
                .assign 3 (realAddr conf src), .assign 1 (.load (.var 3)),
                .assign 3 (.load (.op .add [.var 3, .const bytes]))]
              let value := WordLangProgHOL.ite .test src (.imm 1)
                (.assign 3 (shiftN .asr (.var src) 2))
                (.seq loadBignum (.ite .test 1 (.imm 16) .skip
                  (.assign 3 (.op .sub [.const 0, .var 3]))))
              some (.seq value (writeWord64 conf header dest), l)
      | _ => some (.skip, l)
  | l, .assign dest (.wordOp .wordToInt) args _ =>
      match args with
      | [src] =>
          if width != 64 then none else
          match encodeHeader (width := width) conf 3 1 with
          | none => some (giveUp, l)
          | some header =>
              let bytes := (wordSemBytesInWord : BitVec width)
              let address := WordLangExpHOL.op .add [realAddr conf (adjustVar src), .const bytes]
              some (wordListSeq [
                .assign 3 (.load address), .assign 1 (shiftN .lsr (.var 3) 61),
                .ite .equal 1 (.imm 0) (.assign (adjustVar dest) (shiftN .lsl (.var 3) 2))
                  (writeWord64 conf header dest)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp .boundsCheckBlock) args _ =>
      match args with
      | [base, index] =>
          let base := adjustVar base
          let header := WordLangExpHOL.load (realAddr conf base)
          some (wordListSeq [
            .ite .test base (.imm 1) (.assign 1 (.const 0))
              (.assign 1 (shiftN .lsr header (width - conf.lenSize))),
            .assign 3 (shiftVar .ror (adjustVar index) 2),
            boolResult dest .lower 3 (.reg 1)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp (.cons tag)) args _ =>
      some (compileCons conf l dest tag args)
  | l, .assign dest (.blockOp (.consExtend tag)) args names =>
      match args with
      | old :: start :: len :: total :: rest =>
          match encodeHeader (width := width) conf (4 * tag) 0 with
          | none => some (giveUp, l)
          | some header =>
              let names := names.getD .ln
              let bytes := (wordSemBytesInWord : BitVec width)
              let limit := min (2 ^ conf.lenSize) (2 ^ width / 16)
              let total := adjustVar total
              some (wordListSeq [
                .ite .test total (.imm 1) .skip giveUp,
                .assign 1 (.var total), allocVar conf limit (sptListInsert args names),
                .assign 1 (.lookup .nextFree),
                .assign 5 (.op .or [shiftN .lsl (.var total) (width - conf.lenSize - 2), .const header]),
                .assign 7 (shiftN .lsr (.var total) 2), .assign 9 (.const (BitVec.ofNat width tag)),
                storeEach 1 (5 :: rest.map adjustVar) 0, makePtrBitsCode conf 9 7 3,
                .set .nextFree (.op .add [.var 1, .const bytes, shiftN .lsl (.var 7) (wordShiftAmount width)]),
                .assign 15 (.var (adjustVar len)),
                .assign 13 (.op .add [.var 1, .const (bytes * BitVec.ofNat width (rest.length + 1))]),
                .assign 11 (.op .add [realAddr conf (adjustVar old), .const bytes,
                  shiftVar .lsl (adjustVar start) (wordShiftAmount width - 2)]),
                .ite .test 15 (.reg 15) (.assign (adjustVar dest) (.var 3))
                  (.mustTerminate (.call (some ([adjustVar dest], adjustSets names, .skip, secn, l))
                    (some memCopyLocation) [15, 11, 13, 3] none))], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp (.elemAt n)) args _ =>
      some (arg1 args (assignElemAt conf n l dest) (.skip, l))
  | l, .assign dest (.ffi ffiName) args names =>
      match args with
      | [x, y] =>
          if !conf.callEmptyFfi && ffiName == Flapjack.Basis.Pure.MlString.ofString "" then
            some (.assign (adjustVar dest) (.const 2), l)
          else
            let bytes := (wordSemBytesInWord : BitVec width)
            let offset := width - wordShiftAmount width - conf.lenSize
            let addr1 := realAddr conf (adjustVar x)
            let addr2 := realAddr conf (adjustVar y)
            let empty := ffiName == Flapjack.Basis.Pure.MlString.ofString ""
            some (wordListSeq [
              .assign 1 (.op .add [addr1, .const bytes]),
              .assign 3 (.op .sub [shiftN .lsr (.load addr1) offset, .const bytes]),
              .assign 5 (if empty then .const 0 else .op .add [addr2, .const bytes]),
              .assign 7 (if empty then .const 0 else .op .sub [shiftN .lsr (.load addr2) offset, .const bytes]),
              .ffi ffiName 1 3 5 7 (adjustSets (names.getD .ln)),
              .assign (adjustVar dest) (.const 2)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp .boundsCheckArray) args _ =>
      match args with
      | [base, index] =>
          let header := WordLangExpHOL.load (realAddr conf (adjustVar base))
          some (wordListSeq [
            .assign 1 (shiftN .lsr header (width - conf.lenSize)),
            .assign 3 (shiftVar .ror (adjustVar index) 2),
            boolResult dest .lower 3 (.reg 1)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp (.stringCmp fast cmp)) args names =>
      match args with
      | [first, second] =>
          let bytes := (wordSemBytesInWord : BitVec width)
          let offset := width - conf.lenSize - wordShiftAmount width
          let names := adjustSets (names.getD .ln)
          let call (args : List Nat) := WordLangProgHOL.mustTerminate
            (.call (some ([5, 7], names, .skip, secn, l)) (some stringCmpLoopLocation) args none)
          let compareBytes := if fast then
              WordLangProgHOL.ite .equal 5 (.reg 7) (wordListSeq [
                .assign 11 (.op .add [.var 1, .const bytes]),
                .assign 13 (.op .add [.var 3, .const bytes]), call [11, 13, 7, 7, 7]]) .skip
            else wordListSeq [
              .assign 11 (.op .add [.var 1, .const bytes]),
              .assign 13 (.op .add [.var 3, .const bytes]), .assign 9 (.var 5),
              .ite .lower 7 (.reg 5) (.assign 9 (.var 7)) .skip, call [11, 13, 9, 5, 7]]
          let result := match cmp with
            | .lt => boolResult dest .lower 5 (.reg 7)
            | .gt => boolResult dest .lower 7 (.reg 5)
            | .leq => boolResult dest .notLower 7 (.reg 5)
            | .geq => boolResult dest .notLower 5 (.reg 7)
          some (wordListSeq [
            .assign 1 (realAddr conf (adjustVar first)), .assign 3 (realAddr conf (adjustVar second)),
            .assign 5 (shiftN .lsr (.load (.var 1)) offset),
            .assign 7 (shiftN .lsr (.load (.var 3)) offset), compareBytes, result], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp (.boundsCheckByte leq)) args _ =>
      match args with
      | [base, index] =>
          let header := WordLangExpHOL.load (realAddr conf (adjustVar base))
          let shift := width - conf.lenSize - (if width = 32 then 2 else 3)
          let result := if leq then boolResult dest .notLower 1 (.reg 3)
            else boolResult dest .lower 3 (.reg 1)
          some (wordListSeq [
            .assign 1 (.op .sub [shiftN .lsr header shift, .const ((wordSemBytesInWord : BitVec width))]),
            .assign 3 (shiftVar .ror (adjustVar index) 2), result], l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp (.refByte immutable)) args names =>
      match args with
      | [x, y] => some (.seq (.assign 1 (.const (if immutable then 0 else 16)))
          (.mustTerminate (.call
            (some ([adjustVar dest], adjustSets (names.getD .ln), .skip, secn, l))
            (some refByteLocation) [adjustVar x, adjustVar y, 1] none)), l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp .el) args _ =>
      some (arg2 args (assignEl conf l dest) (.skip, l))
  | l, .assign dest (.memOp .length) args _ =>
      match args with
      | [src] =>
          let header := WordLangExpHOL.load (realAddr conf (adjustVar src))
          some (.assign (adjustVar dest) (shiftN .lsl (shiftN .lsr header (width - conf.lenSize)) 2), l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp .lengthByte) args _ =>
      match args with
      | [src] =>
          let header := WordLangExpHOL.load (realAddr conf (adjustVar src))
          let length := shiftN .lsr header (width - wordShiftAmount width - conf.lenSize)
          some (.assign (adjustVar dest)
            (shiftN .lsl (.op .sub [length, .const ((wordSemBytesInWord : BitVec width))]) 2), l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp .derefByte) args _ =>
      some (arg2 args (assignDerefByte conf l dest) (.skip, l))
  | l, .assign dest (.memOp .updateByte) args _ =>
      some (arg3 args (assignUpdateByte conf l dest) (.skip, l))
  | l, .assign dest (.memOp .ref) args _ =>
      match encodeHeader (width := width) conf 2 args.length with
      | none => some (giveUp, l)
      | some header =>
          let bytes := (wordSemBytesInWord : BitVec width) * BitVec.ofNat width (args.length + 1)
          some (wordListSeq [
            .set .triggerGC (.op .sub [.lookup .triggerGC, .const bytes]),
            .assign 1 (.op .sub [.lookup .endOfHeap, .const bytes]),
            .set .endOfHeap (.var 1),
            .assign 3 (.const header),
            storeEach 1 (3 :: args.map adjustVar) 0,
            .assign (adjustVar dest) (.op .or [
              shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
              .const 1])], l)
  | l, .assign dest (.memOp .refArray) args names =>
      match args with
      | [x, y] =>
          let names := names.getD .ln
          let limit := min (2 ^ conf.lenSize) (2 ^ width / 16)
          some (wordListSeq [
            .ite .test (adjustVar x) (.imm 1) .skip giveUp,
            .move 0 [(1, adjustVar x)],
            allocVar conf limit (sptListInsert [x, y] names),
            .mustTerminate (.call (some ([adjustVar dest], adjustSets names, .skip, secn, l))
              (some refArrayLocation) [adjustVar x, adjustVar y] none)], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp (.copyByte _)) args names =>
      let loc := match args with
        | [_, _, _, _, _] => some byteCopyLocation
        | [_, _, _] => some byteCopyNewLocation
        | _ => none
      match loc with
      | some loc => some (.mustTerminate (.call
          (some ([adjustVar dest], adjustSets (names.getD .ln), .skip, secn, l))
          (some loc) (args.map adjustVar) none), l + 1)
      | none => some (.skip, l)
  | l, .assign dest (.memOp .configGC) args names =>
      match args with
      | [_, _] =>
          let names := adjustSets (names.getD .ln)
          some (wordListSeq [silentFfi conf 3 names, .assign 1 (.const 0), .alloc 1 names,
            silentFfi conf 3 names, .assign (adjustVar dest) (.const 2)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp .xorByte) args names =>
      match args with
      | [first, second] =>
          let bytes := (wordSemBytesInWord : BitVec width)
          some (wordListSeq [
            .assign 1 (realAddr conf (adjustVar first)),
            .assign 3 (realAddr conf (adjustVar second)),
            .assign 5 (shiftN .lsr (.load (.var 3)) (width - conf.lenSize)),
            .assign 1 (.op .add [.var 1, .const bytes]),
            .assign 3 (.op .add [.var 3, .const bytes]),
            .mustTerminate (.call
              (some ([adjustVar dest], adjustSets (names.getD .ln), .skip, secn, l))
              (some xorLoopLocation) [1, 3, 5] none)], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp op) args _ =>
      match op, args with
      | .mutCons tag _, _ =>
          match conf.gcKind with
          | .generational _ => some (giveUp, l)
          | _ => some (compileCons conf l dest tag args)
      | .finaliseCons, [src] => some (.assign (adjustVar dest) (.var (adjustVar src)), l)
      | .finaliseCons, _ => some (.skip, l)
      | .update, args | .updateCons, args =>
          some (arg3 args (assignUpdate conf l dest) (.skip, l))
      | _, _ => some (.skip, l)
  | l, .assign dest (.thunkOp (.allocThunk mode)) args _ =>
      match args with
      | [arg] =>
          let tag := match mode with
            | .evaluated => 14
            | .notEvaluated => 6
          match encodeHeader (width := width) conf tag 1 with
          | none => some (giveUp, l)
          | some header =>
              let bytes := BitVec.ofNat width (2 * (width / 8))
              some (wordListSeq [
                .set .triggerGC (.op .sub [.lookup .triggerGC, .const bytes]),
                .assign 1 (.op .sub [.lookup .endOfHeap, .const bytes]),
                .set .endOfHeap (.var 1), .assign 3 (.const header),
                storeEach 1 [3, adjustVar arg] 0,
                .assign (adjustVar dest) (.op .or [
                  shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
                  .const 1])], l)
      | _ => some (.skip, l)
  | l, .assign dest (.thunkOp (.updateThunk mode)) args _ =>
      match args with
      | [base, value] =>
          let addr := realAddr conf (adjustVar base)
          let bytes := (wordSemBytesInWord : BitVec width)
          match mode with
          | .notEvaluated => some (.seq (.store (.op .add [addr, .const bytes]) (adjustVar value))
              (.assign (adjustVar dest) (.const 2)), l)
          | .evaluated =>
              match encodeHeader (width := width) conf 14 1 with
              | none => some (giveUp, l)
              | some header => some (wordListSeq [
                  .assign 1 addr, .assign 3 (.const header), .store (.var 1) 3,
                  .store (.op .add [.var 1, .const bytes]) (adjustVar value),
                  .assign (adjustVar dest) (.const 2)], l)
      | _ => some (.skip, l)
  | l, .assign dest .install args names =>
      match args with
      | [code, data, codeLen, dataLen] =>
          let code := adjustVar code
          let data := adjustVar data
          let codeLen := adjustVar codeLen
          let dataLen := adjustVar dataLen
          let halt (r : Nat) := WordLangProgHOL.ite .test r (.imm 1) .skip giveUp
          some (wordListSeq [
            halt codeLen, halt dataLen,
            .assign 1 (.lookup .bitmapBuffer),
            .assign 3 (.op .sub [.lookup .bitmapBufferEnd, .var 1]),
            .assign 5 (shiftVar .lsr dataLen 2),
            .assign 3 (shiftVar .lsr 3 (wordShiftAmount width)),
            .ite .lower 3 (.reg 5) giveUp .skip,
            .assign 1 (.lookup .codeBuffer),
            .assign 3 (.op .sub [.lookup .codeBufferEnd, .var 1]),
            .assign 5 (shiftVar .lsr codeLen 2),
            .ite .lower 3 (.reg 5) giveUp .skip,
            .mustTerminate (.call (some ([adjustVar dest], adjustSets (names.getD .ln), .skip, secn, l))
              (some installCodeLocation) [code, data, 1] none)], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.label n) _ _ => some (.locValue (adjustVar dest) n, l)
  -- HOL's final assignment case returns Skip for operations that should
  -- have been lowered by earlier passes, including AllocGlobal and Constant.
  | l, .assign _ _ _ _ => some (.skip, l)
  | l, .force ret loc v =>
      match encodeHeader (width := width) conf 14 1 with
      | none => some (giveUp, l)
      | some _ =>
          let v := adjustVar v
          let unchanged := match ret with
            | none => WordLangProgHOL.return 0 [v]
            | some (dest, _) => .assign (adjustVar dest) (.var v)
          let loaded := WordLangExpHOL.load (.op .add [.var 1, .const ((wordSemBytesInWord : BitVec width))])
          let evaluated := match ret with
            | none => wordListSeq [.assign 1 loaded, .return 0 [1]]
            | some (dest, _) => .assign (adjustVar dest) loaded
          let call := match ret with
            | none => WordLangProgHOL.call none (some loc) [0, v, 5] none
            | some (dest, names) => .call (some ([adjustVar dest], adjustSets names, .skip, secn, l))
                (some loc) [v, 5] none
          some (.ite .test v (.imm 1) unchanged (wordListSeq [
            .assign 1 (realAddr conf v),
            .assign 3 (.op .and [.load (.var 1), .const 60]),
            .ite .equal 3 (.imm 56) evaluated
              (.ite .notEqual 3 (.imm 24) unchanged (wordListSeq [.assign 5 loaded, call]))]), l + 1)
  | l, .call none target args _ => some (.call none target (0 :: args.map adjustVar) none, l)
  | l, .call (some (ns, names)) target args none =>
      some (.call (some (ns.map adjustVar, adjustSets names, .skip, secn, l))
        target (args.map adjustVar) none, l + 1)
  | l, .call (some (ns, names)) target args (some (n, handler)) => do
      let (handler, next) ← compileControl? conf secn (l + 2) handler
      pure (.call (some (ns.map adjustVar, adjustSets names, .skip, secn, l))
        target (args.map adjustVar) (some (adjustVar n, handler, secn, l + 1)), next)
end Flapjack.Compiler.Backend.DataToWord
