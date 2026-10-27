import Flapjack.Compiler.Backend.DataLang.Syntax
import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.DataToWord.Header
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
  | l, .assign dest (.blockOp (.boolTest _)) args _ =>
      match args with
      | [x, y] => some (boolResult dest .equal (adjustVar x) (.reg (adjustVar y)), l)
      | _ => some (.skip, l)
  | l, .assign dest (.intOp (.lessConstSmall i)) args _ =>
      match args with
      | [src] => some (boolResult dest .less (adjustVar src) (.imm (BitVec.ofNat width (4 * i))), l)
      | _ => some (.skip, l)
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
  | l, .assign dest (.memOp .ref) args _ =>
      match encodeHeader (width := width) conf 2 args.length with
      | none => some (.seq (.assign 1 (.const (-1))) (.alloc 1 (adjustSets (.ln : NumSet))), l)
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
