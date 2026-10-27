import Flapjack.Compiler.Backend.DataLang.Syntax
import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.DataToWord.Header
import Flapjack.Compiler.Backend.DataToWord.Locations
import Flapjack.Compiler.Backend.DataToWord.Variables
import Flapjack.Compiler.Backend.DataToWord.WordOp
import Flapjack.Pancake.WordLang

/-! Checked control-flow cases of data-to-word compilation. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- Generic Flapjack sequencing helper; HOL's `list_Seq` is restricted to
word-indexed programs, so this broader helper is not tagged as that port. -/
private def listSeq {α : Type} : List (WordLangProgHOL α) → WordLangProgHOL α
  | [] => .skip
  | [x] => x
  | x :: y :: xs => .seq x (listSeq (y :: xs))

/-- Internal storage sequence used by reference allocation. The standalone
width-indexed HOL helper has not yet been reviewed as a port. -/
private def storeEach {width : Nat} (base : Nat) : List Nat → BitVec width → WordLangProgHOL (BitVec width)
  | [], _ => .skip
  | x :: xs, offset => .seq (.store (.op .add [.var base, .const offset]) x)
      (storeEach base xs (offset + BitVec.ofNat width (width / 8)))

/-- Internal support for the checked allocation case; a reviewed port of
`SilentFFI` and its width-indexed statement remains open. -/
private def silentFfi {width : Nat} (conf : Config) (n : Nat) (names : WordLangCutsetsHOL) :
    WordLangProgHOL (BitVec width) :=
  if conf.callEmptyFfi then
    listSeq [.assign n (.const 0),
      .assign 7 (.op .sub [.lookup .nextFree, .lookup .currHeap]),
      .assign 9 (.lookup .heapLength), .ffi (.implode []) 7 n 9 n names]
  else .skip

/-- Internal allocation-failure sequence used by supported cases. -/
private def giveUp {width : Nat} : WordLangProgHOL (BitVec width) :=
  .seq (.assign 1 (.const (-1))) (.alloc 1 (adjustSets (.ln : NumSet)))

/-- Internal word-address construction for supported load cases; the
standalone width-indexed HOL definition remains to be reviewed and tagged. -/
private def realAddr {width : Nat} [NeZero width] (conf : Config) (r : Nat) : WordLangExpHOL (BitVec width) :=
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

/-- Internal shift constructor and source-shaped saturation for variable
shifts. The standalone HOL `ShiftVar` declaration remains to be reviewed. -/
private def shiftN {width : Nat} (op : Shift) (e : WordLangExpHOL (BitVec width)) (n : Nat) :
    WordLangExpHOL (BitVec width) := .shift op e (.const (BitVec.ofNat width n))

private def shiftVar {width : Nat} (op : Shift) (v n : Nat) : WordLangExpHOL (BitVec width) :=
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

/-- Internal pointer-field construction for nonempty constructor allocation;
the standalone HOL helpers remain to be reviewed. -/
private def pointerBits {width : Nat} (conf : Config) (tag len : Nat) : BitVec width :=
  let field (n bits shift : Nat) : BitVec width :=
    let max := 2 ^ bits - 1
    BitVec.ofNat width ((if n < max then n else max) * 2 ^ shift)
  field tag conf.tagBits (1 + conf.lenBits) ||| field len conf.lenBits 1

/-- Internal variable-allocation sequence for the reference-array case;
the standalone width-indexed HOL definition remains to be reviewed. -/
private def allocVar {width : Nat} [NeZero width] (conf : Config) (limit : Nat) (names : NumSet) :
    WordLangProgHOL (BitVec width) :=
  let cutsets := adjustSets names
  let ffiCutsets := (cutsets.1, sptInsert 1 () cutsets.2)
  listSeq [
    .assign 1 (shiftN .lsr (.var 1) 2),
    .ite .lower 1 (.imm (BitVec.ofNat width limit))
      (.assign 1 (shiftN .lsl (.op .add [.var 1, .const 1]) (wordShiftAmount width)))
      (.assign 1 (.const (-1))),
    .assign 3 (.op .sub [.lookup .triggerGC, .lookup .nextFree]),
    .ite .lower 3 (.reg 1)
      (listSeq [silentFfi conf 3 ffiCutsets, .alloc 1 cutsets, silentFfi conf 3 cutsets]) .skip]

/-- Flapjack's partial traversal. Unsupported assignment operations and
thunk cases return `none`; this is not HOL's total `comp`. -/
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
          (listSeq [silentFfi conf 3 cutsets, .assign 1 (.const value),
            .alloc 1 cutsets, silentFfi conf 3 cutsets]) .skip), l)
  | l, .assign dest (.intOp (.const i)) _ _ =>
      let magnitude := BitVec.ofNat width (4 * i.natAbs)
      let value := if i < 0 then -magnitude else magnitude
      some (.assign (adjustVar dest) (.const value), l)
  | l, .assign dest (.globOp .globalsPtr) _ _ =>
      some (.assign (adjustVar dest) (.lookup .globals), l)
  | l, .assign dest (.globOp .setGlobalsPtr) args _ =>
      match args with
      | [src] => some (.seq (.set .globals (.var (adjustVar src)))
          (.seq (.set .globReal (realAddr conf (adjustVar src)))
            (.assign (adjustVar dest) (.const 2))), l)
      | _ => some (.skip, l)
  | l, .assign dest (.globOp (.global n)) _ _ =>
      let offset := BitVec.ofNat width (width / 8) * BitVec.ofNat width (n + 1)
      some (.assign (adjustVar dest) (.load (.op .add [.lookup .globReal, .const offset])), l)
  | l, .assign dest (.globOp (.setGlobal n)) args _ =>
      match args with
      | [src] =>
          let offset := BitVec.ofNat width (width / 8) * BitVec.ofNat width (n + 1)
          some (.seq (.store (.op .add [.lookup .globReal, .const offset]) (adjustVar src))
            (.assign (adjustVar dest) (.const 2)), l)
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
            | some header => some (listSeq [
                .assign 1 (.const 0),
                .ite .test src (.imm 1) .skip (.assign 1 (.load (realAddr conf src))),
                boolResult dest .equal 1 (.imm header)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp (.boolTest _)) args _ =>
      match args with
      | [x, y] => some (boolResult dest .equal (adjustVar x) (.reg (adjustVar y)), l)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp .equal) args names =>
      match args with
      | [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          some (listSeq [
            .assign 1 (.var (adjustVar x)), .assign 3 (.var (adjustVar y)),
            .assign 5 (.op .and [.var 1, .var 3]),
            .ite .test 5 (.imm 1) .skip
              (.ite .equal 1 (.reg 3) .skip
                (.seq (.mustTerminate (.call (some ([1], cutsets, .skip, secn, l))
                  (some equalLocation) [1, 3] none)) (.assign 3 (.const 1)))),
            boolResult dest .equal 1 (.reg 3)], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.blockOp (.equalConst (.int i))) args _ =>
      match args with
      | [src] =>
          let bound : Int := Int.ofNat (2 ^ width / 8)
          if -bound ≤ i ∧ i < bound then
            let magnitude := BitVec.ofNat width (4 * i.natAbs)
            let value := if i < 0 then -magnitude else magnitude
            some (boolResult dest .equal (adjustVar src) (.imm value), l)
          else none
      | _ => some (.skip, l)
  | l, .assign dest (.intOp (.lessConstSmall i)) args _ =>
      match args with
      | [src] => some (boolResult dest .less (adjustVar src) (.imm (BitVec.ofNat width (4 * i))), l)
      | _ => some (.skip, l)
  | l, .assign dest (.intOp .less) args names =>
      match args with
      | [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          some (listSeq [
            .assign 1 (.var (adjustVar x)), .assign 3 (.var (adjustVar y)),
            .assign 5 (.op .or [.var 1, .var 3]),
            .ite .test 5 (.imm 1) .skip
              (.seq (.mustTerminate (.call (some ([1], cutsets, .skip, secn, l))
                (some compareLocation) [1, 3] none)) (.assign 3 (.const 1))),
            boolResult dest .less 1 (.reg 3)], l + 1)
      | _ => some (.skip, l)
  | l, .assign dest (.intOp op) args names =>
      match op, args with
      | .add, [x, y] | .sub, [x, y] =>
          let cutsets := adjustSets (names.getD .ln)
          let (instr, loc) := match op with
            | .add => (WordLangArith.addOverflow 1 (adjustVar x) (adjustVar y) 3, addLocation)
            | _ => (WordLangArith.subOverflow 1 (adjustVar x) (adjustVar y) 3, subLocation)
          some (listSeq [
            .inst (.arith instr),
            .assign 3 (.op .or [.var 3, .var (adjustVar x), .var (adjustVar y)]),
            .ite .test 3 (.imm 1) .skip
              (.mustTerminate (.call (some ([1], cutsets, .skip, secn, l))
                (some loc) [adjustVar x, adjustVar y] none)),
            .move 2 [(adjustVar dest, 1)]], l + 1)
      | .add, _ | .sub, _ => some (.skip, l)
      | _, _ => none
  | l, .assign dest (.wordOp (.wordTest _ test)) args _ =>
      match args, test with
      | [x, y], .equal => some (boolResult dest .equal (adjustVar x) (.reg (adjustVar y)), l)
      | [x, y], .compare .lt => some (boolResult dest .lower (adjustVar x) (.reg (adjustVar y)), l)
      | [x, y], .compare .leq => some (boolResult dest .notLower (adjustVar y) (.reg (adjustVar x)), l)
      | _, _ => some (.skip, l)
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
  | l, .assign dest (.blockOp (.cons tag)) [] _ =>
      if tag < 2 ^ width / 16 then
        some (.assign (adjustVar dest) (.const (BitVec.ofNat width (16 * tag + 2))), l)
      else some (.seq (.assign 1 (.const (-1))) (.alloc 1 (adjustSets (.ln : NumSet))), l)
  | l, .assign dest (.blockOp (.cons tag)) args _ =>
      match encodeHeader (width := width) conf (4 * tag) args.length with
      | none => some (giveUp, l)
      | some header =>
          let bytes := BitVec.ofNat width (width / 8) * BitVec.ofNat width (args.length + 1)
          let mask := BitVec.ofNat width (2 ^ smallShiftLength conf - 1)
          let pointer := (pointerBits conf tag args.length &&& mask) ||| 1
          some (listSeq [
            .assign 1 (.lookup .nextFree), .assign 3 (.const header),
            storeEach 1 (3 :: args.map adjustVar) 0,
            .assign (adjustVar dest) (.op .or [
              shiftN .lsl (.op .sub [.var 1, .lookup .currHeap]) (shiftLength conf - wordShiftAmount width),
              .const pointer]),
            .set .nextFree (.op .add [.var 1, .const bytes])], l)
  | l, .assign dest (.blockOp (.elemAt n)) args _ =>
      match args with
      | [src] =>
          let bytes := BitVec.ofNat width (width / 8)
          let offset := bytes + bytes * BitVec.ofNat width n
          some (.assign (adjustVar dest)
            (.load (.op .add [realAddr conf (adjustVar src), .const offset])), l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp .el) args _ =>
      match args with
      | [base, index] =>
          let index := adjustVar index
          let scaled := if width = 32 then WordLangExpHOL.var index
            else .shift .lsl (.var index) (.const 1)
          let offset := WordLangExpHOL.op .add [.const (BitVec.ofNat width (width / 8)), scaled]
          some (.assign (adjustVar dest) (.load (.op .add [realAddr conf (adjustVar base), offset])), l)
      | _ => some (.skip, l)
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
            (shiftN .lsl (.op .sub [length, .const (BitVec.ofNat width (width / 8))]) 2), l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp .derefByte) args _ =>
      match args with
      | [base, index] =>
          let offset := WordLangExpHOL.op .add [.const (BitVec.ofNat width (width / 8)),
            shiftN .lsr (.var (adjustVar index)) 2]
          some (listSeq [
            .assign 1 (.op .add [realAddr conf (adjustVar base), offset]),
            .inst (.mem .load8 3 (.addr 1 0)),
            .assign (adjustVar dest) (shiftN .lsl (.var 3) 2)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp .updateByte) args _ =>
      match args with
      | [base, index, value] =>
          let offset := WordLangExpHOL.op .add [.const (BitVec.ofNat width (width / 8)),
            shiftN .lsr (.var (adjustVar index)) 2]
          some (listSeq [
            .assign 1 (.op .add [realAddr conf (adjustVar base), offset]),
            .assign 3 (shiftN .lsr (.var (adjustVar value)) 2),
            .inst (.mem .store8 3 (.addr 1 0)),
            .assign (adjustVar dest) (.const 2)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.memOp .ref) args _ =>
      match encodeHeader (width := width) conf 2 args.length with
      | none => some (giveUp, l)
      | some header =>
          let bytes := BitVec.ofNat width (width / 8) * BitVec.ofNat width (args.length + 1)
          some (listSeq [
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
          some (listSeq [
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
  | l, .assign dest (.memOp op) args _ =>
      match op, args with
      | .update, [base, index, value] | .updateCons, [base, index, value] =>
          let index := adjustVar index
          let scaled := if width = 32 then WordLangExpHOL.var index
            else .shift .lsl (.var index) (.const 1)
          let offset := WordLangExpHOL.op .add [.const (BitVec.ofNat width (width / 8)), scaled]
          some (.seq (.store (.op .add [realAddr conf (adjustVar base), offset]) (adjustVar value))
            (.assign (adjustVar dest) (.const 2)), l)
      | .update, _ | .updateCons, _ => some (.skip, l)
      | _, _ => none
  | l, .assign dest (.thunkOp (.updateThunk mode)) args _ =>
      match args with
      | [base, value] =>
          let addr := realAddr conf (adjustVar base)
          let bytes := BitVec.ofNat width (width / 8)
          match mode with
          | .notEvaluated => some (.seq (.store (.op .add [addr, .const bytes]) (adjustVar value))
              (.assign (adjustVar dest) (.const 2)), l)
          | .evaluated =>
              match encodeHeader (width := width) conf 14 1 with
              | none => some (giveUp, l)
              | some header => some (listSeq [
                  .assign 1 addr, .assign 3 (.const header), .store (.var 1) 3,
                  .store (.op .add [.var 1, .const bytes]) (adjustVar value),
                  .assign (adjustVar dest) (.const 2)], l)
      | _ => some (.skip, l)
  | l, .assign dest (.label n) _ _ => some (.locValue (adjustVar dest) n, l)
  | l, .call none target args _ => some (.call none target (0 :: args.map adjustVar) none, l)
  | l, .call (some (ns, names)) target args none =>
      some (.call (some (ns.map adjustVar, adjustSets names, .skip, secn, l))
        target (args.map adjustVar) none, l + 1)
  | l, .call (some (ns, names)) target args (some (n, handler)) => do
      let (handler, next) ← compileControl? conf secn (l + 2) handler
      pure (.call (some (ns.map adjustVar, adjustSets names, .skip, secn, l))
        target (args.map adjustVar) (some (adjustVar n, handler, secn, l + 1)), next)
  | _, _ => none

end Flapjack.Compiler.Backend.DataToWord
