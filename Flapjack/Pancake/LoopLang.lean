import Flapjack.Pancake.CrepLang
import Flapjack.Basis.Pure.MlString
import Flapjack.FiniteMap.Basic
import Flapjack.Misc.Sptree

/-!
The Loop intermediate language used after Crepe lowering. The constructors
follow CakeML's `loopLangScript.sml`; target-specific instruction selection is
kept for the later RISC-V layer.
-/

namespace Flapjack

inductive LoopExp (α : Type u) where
  | const (value : α)
  | var (name : Nat)
  | lookup (address : BitVec 5)
  | load (address : LoopExp α)
  | op (operator : BinOp) (args : List (LoopExp α))
  | crepOp (operator : CrepOp) (args : List (LoopExp α))
  | cmp (operator : Cmp) (left right : LoopExp α)
  | shift (operator : Shift) (left right : LoopExp α)
  | baseAddr
  | topAddr
  deriving Repr

/-- Faithful Cake `loopLang$exp` over a fixed word width. HOL's generic `'a word`
carrier is instantiated at `BitVec width`, and unlike the executable `LoopExp`
there are no extra `crepOp`/`cmp` cases. -/
@[hol "cakeml/pancake/loopLangScript.sml" "exp"]
inductive HolLoopExp (width : Nat) [NeZero width] where
  | const (value : BitVec width)
  | var (name : Nat)
  | lookup (address : BitVec 5)
  | load (address : HolLoopExp width)
  | op (operator : BinOp) (args : List (HolLoopExp width))
  | shift (operator : Shift) (left right : HolLoopExp width)
  | baseAddr
  | topAddr
  deriving Repr

/-- Executable `LoopExp` view of a faithful `HolLoopExp`. Every HOL constructor
has a direct executable counterpart; the executable language has additional
constructors that are not part of HOL `loopLang$exp`. -/
def holLoopExpToExecutable {width : Nat} [NeZero width] :
    HolLoopExp width → LoopExp (BitVec width)
  | .const value => .const value
  | .var name => .var name
  | .lookup address => .lookup address
  | .load address => .load (holLoopExpToExecutable address)
  | .op operator args => .op operator (args.map holLoopExpToExecutable)
  | .shift operator left right =>
      .shift operator (holLoopExpToExecutable left) (holLoopExpToExecutable right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr

inductive RegImm (α : Type u) where
  | imm (value : α)
  | reg (name : Nat)
  deriving Repr

/-- Faithful Cake `loopLang$loop_arith`; constructor and field shapes match this
executable `LoopArith` name for name (HOL uses `LLongMul`/`LLongDiv`/`LDiv`). -/
@[hol "cakeml/pancake/loopLangScript.sml" "loop_arith"]
inductive LoopArith where
  | longMul (destinationLeft destinationRight sourceLeft sourceRight : Nat)
  | longDiv (destinationLeft destinationRight sourceLeft sourceRight quotient : Nat)
  | div (destination dividend divisor : Nat)
  deriving Repr, DecidableEq

/-- Faithful Cake `loopLang$prog` over a fixed word width. HOL's generic `'a word`
carrier is instantiated at `BitVec width`, `num_set` fields use the exact
`spt`-backed `NumSet` (`miscScript.sml:787`, `unit spt`), `shMem` uses
`CrepMemOp`, whose eight constructors (`load/load8/load16/load32/store/store8/
store16/store32`) match `asm$memop` (`asmScript.sml:125-128`) name for name, and
the FFI name is the exact `MlString` carrier rather than the executable
`FunName = String`. The executable `LoopProg` is a one-parameter superset
(`LoopExp` adds `crepOp`/`cmp`; FFI names are `String`), so the
executable/faithful bridge is tracked by bead `flapjack-pxn.18.5.17.1.1`. -/
@[hol "cakeml/pancake/loopLangScript.sml" "prog"]
inductive HolLoopProg (width : Nat) [NeZero width] where
  | skip
  | assign (name : Nat) (value : HolLoopExp width)
  | primitive (destinations : List Nat) (operator : PrimOp) (arguments : List Nat)
  | arith (operation : LoopArith)
  | store (address : HolLoopExp width) (value : Nat)
  | setGlobal (address : BitVec 5) (value : HolLoopExp width)
  | load32 (address destination : Nat)
  | loadByte (address destination : Nat)
  | store32 (address value : Nat)
  | storeByte (address value : Nat)
  | seq (first second : HolLoopProg width)
  | ite (operator : Cmp) (condition : Nat) (right : RegImm (BitVec width))
      (thenBranch elseBranch : HolLoopProg width) (live : NumSet)
  | loop (liveIn : NumSet) (body : HolLoopProg width) (liveOut : NumSet)
  | break (label : Nat)
  | continue (label : Nat)
  | raise (exception : Nat)
  | return (values : List Nat)
  | shMem (operator : CrepMemOp) (name : Nat) (address : HolLoopExp width)
  | tick
  | mark (body : HolLoopProg width)
  | fail
  | locValue (destination source : Nat)
  | call (returns : Option (List Nat × NumSet)) (target : Option Nat)
      (arguments : List Nat)
      (handler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet))
  | ffi (function : Flapjack.Basis.Pure.MlString.MlString)
      (configuration configurationLength array arrayLength : Nat)
      (live : NumSet)

inductive LoopProg (α : Type u) where
  | skip
  | assign (name : Nat) (value : LoopExp α)
  | primitive (destinations : List Nat) (operator : PrimOp) (arguments : List Nat)
  | arith (operation : LoopArith)
  | store (address : LoopExp α) (value : Nat)
  | setGlobal (address : BitVec 5) (value : LoopExp α)
  | load32 (address destination : Nat)
  | loadByte (address destination : Nat)
  | store32 (address value : Nat)
  | storeByte (address value : Nat)
  | seq (first second : LoopProg α)
  | ite (operator : Cmp) (condition : Nat) (right : RegImm α)
      (thenBranch elseBranch : LoopProg α) (live : List Nat)
  | loop (liveIn : List Nat) (body : LoopProg α) (liveOut : List Nat)
  | break (label : Nat)
  | continue (label : Nat)
  | raise (exception : Nat)
  | return (values : List Nat)
  | shMem (operator : CrepMemOp) (name : Nat) (address : LoopExp α)
  | tick
  | mark (body : LoopProg α)
  | fail
  | locValue (destination source : Nat)
  | call (returns : Option (List Nat × List Nat)) (target : Option Nat)
      (arguments : List Nat)
      (handler : Option (Nat × LoopProg α × LoopProg α × List Nat))
  | ffi (function : FunName) (configuration configurationLength array arrayLength : Nat)
      (live : List Nat)
  deriving Repr

def loopNestedSeq : List (LoopProg α) → LoopProg α
  | [] => .skip
  | statement :: statements => .seq statement (loopNestedSeq statements)

/-! Faithful port of Cake `loop_seqs_def` from
    `cakeml/pancake/pan_passesScript.sml:532`: flatten only `Seq` nodes,
    preserving the left-to-right order of every other Loop statement. -/
def loopSeqs : LoopProg α → List (LoopProg α)
  | .seq first second => loopSeqs first ++ loopSeqs second
  | program => [program]
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! ## Executable/faithful loopLang bridge

Flapjack-specific bridge between the exact HOL `loopLang$prog` carrier
(`HolLoopProg`, tagged over `MlString`/`NumSet`) and the executable `LoopProg`.
It is untagged Flapjack infrastructure: it relates the two representations so
the exact `loopSem$state` carrier can be bridged to production.  The `num_set`
live sets are related by `numSetListRel`, the FFI name by the `MlString` codec,
and every expression subterm by `holLoopExpToExecutable`. -/

/-- Executable/faithful relation for HOL `num_set`: exactly the listed keys are
    present in the `spt`-backed set. -/
def numSetListRel (keys : List Nat) (tree : NumSet) : Prop :=
  keys.Nodup ∧ ∀ key, sptLookup key tree = some () ↔ key ∈ keys

/-- Executable/faithful relation for `loopLang$exp`: the executable expression
    is the projection of the faithful one. -/
def loopExpExecRel {width : Nat} [NeZero width] :
    LoopExp (BitVec width) → HolLoopExp width → Prop :=
  fun expression faithful => expression = holLoopExpToExecutable faithful

/-- Executable/faithful relation for `loopLang$prog`.  Every HOL constructor has
    an executable counterpart; the `num_set` live sets are related by
    `numSetListRel`, the FFI name by the `MlString` codec, and sub-programs
    recursively.  The executable language's extra expression constructors
    (`crepOp`/`cmp`) have no HOL counterpart and are rejected. -/
def loopProgExecRel {width : Nat} [NeZero width] :
    LoopProg (BitVec width) → HolLoopProg width → Prop
  | .skip, .skip => True
  | .assign executableName executableValue, .assign faithfulName faithfulValue =>
      executableName = faithfulName ∧ loopExpExecRel executableValue faithfulValue
  | .primitive executableDestinations executableOperator executableArguments,
    .primitive faithfulDestinations faithfulOperator faithfulArguments =>
      executableDestinations = faithfulDestinations ∧
        executableOperator = faithfulOperator ∧
        executableArguments = faithfulArguments
  | .arith executableOperation, .arith faithfulOperation =>
      executableOperation = faithfulOperation
  | .store executableAddress executableValue, .store faithfulAddress faithfulValue =>
      executableValue = faithfulValue ∧ loopExpExecRel executableAddress faithfulAddress
  | .setGlobal executableAddress executableValue,
    .setGlobal faithfulAddress faithfulValue =>
      executableAddress = faithfulAddress ∧ loopExpExecRel executableValue faithfulValue
  | .load32 executableAddress executableDestination,
    .load32 faithfulAddress faithfulDestination =>
      executableAddress = faithfulAddress ∧ executableDestination = faithfulDestination
  | .loadByte executableAddress executableDestination,
    .loadByte faithfulAddress faithfulDestination =>
      executableAddress = faithfulAddress ∧ executableDestination = faithfulDestination
  | .store32 executableAddress executableValue,
    .store32 faithfulAddress faithfulValue =>
      executableAddress = faithfulAddress ∧ executableValue = faithfulValue
  | .storeByte executableAddress executableValue,
    .storeByte faithfulAddress faithfulValue =>
      executableAddress = faithfulAddress ∧ executableValue = faithfulValue
  | .seq executableFirst executableSecond, .seq faithfulFirst faithfulSecond =>
      loopProgExecRel executableFirst faithfulFirst ∧
        loopProgExecRel executableSecond faithfulSecond
  | .ite executableOperator executableCondition executableRight executableThen
      executableElse executableLive,
    .ite faithfulOperator faithfulCondition faithfulRight faithfulThen
      faithfulElse faithfulLive =>
      executableOperator = faithfulOperator ∧
        executableCondition = faithfulCondition ∧
        executableRight = faithfulRight ∧
        loopProgExecRel executableThen faithfulThen ∧
        loopProgExecRel executableElse faithfulElse ∧
        numSetListRel executableLive faithfulLive
  | .loop executableLiveIn executableBody executableLiveOut,
    .loop faithfulLiveIn faithfulBody faithfulLiveOut =>
      numSetListRel executableLiveIn faithfulLiveIn ∧
        loopProgExecRel executableBody faithfulBody ∧
        numSetListRel executableLiveOut faithfulLiveOut
  | .break executableLabel, .break faithfulLabel => executableLabel = faithfulLabel
  | .continue executableLabel, .continue faithfulLabel => executableLabel = faithfulLabel
  | .raise executableException, .raise faithfulException =>
      executableException = faithfulException
  | .return executableValues, .return faithfulValues => executableValues = faithfulValues
  | .shMem executableOperator executableName executableAddress,
    .shMem faithfulOperator faithfulName faithfulAddress =>
      executableOperator = faithfulOperator ∧
        executableName = faithfulName ∧
        loopExpExecRel executableAddress faithfulAddress
  | .tick, .tick => True
  | .mark executableBody, .mark faithfulBody =>
      loopProgExecRel executableBody faithfulBody
  | .fail, .fail => True
  | .locValue executableDestination executableSource,
    .locValue faithfulDestination faithfulSource =>
      executableDestination = faithfulDestination ∧
        executableSource = faithfulSource
  | .call executableReturns executableTarget executableArguments executableHandler,
    .call faithfulReturns faithfulTarget faithfulArguments faithfulHandler =>
      (match executableReturns, faithfulReturns with
        | none, none => True
        | some (executableRegister, executableLive),
          some (faithfulRegister, faithfulLive) =>
            executableRegister = faithfulRegister ∧ numSetListRel executableLive faithfulLive
        | _, _ => False) ∧
        executableTarget = faithfulTarget ∧
        executableArguments = faithfulArguments ∧
        (match executableHandler, faithfulHandler with
          | none, none => True
          | some (executableNumber, executableFirst, executableSecond, executableLive),
            some (faithfulNumber, faithfulFirst, faithfulSecond, faithfulLive) =>
              executableNumber = faithfulNumber ∧
                loopProgExecRel executableFirst faithfulFirst ∧
                loopProgExecRel executableSecond faithfulSecond ∧
                numSetListRel executableLive faithfulLive
          | _, _ => False)
  | .ffi executableFunction executableConfiguration executableConfigurationLength
      executableArray executableArrayLength executableLive,
    .ffi faithfulFunction faithfulConfiguration faithfulConfigurationLength
      faithfulArray faithfulArrayLength faithfulLive =>
      Flapjack.Basis.Pure.MlString.ofString executableFunction = faithfulFunction ∧
        executableConfiguration = faithfulConfiguration ∧
        executableConfigurationLength = faithfulConfigurationLength ∧
        executableArray = faithfulArray ∧
        executableArrayLength = faithfulArrayLength ∧
        numSetListRel executableLive faithfulLive
  | _, _ => False
termination_by _ faithful => sizeOf faithful
decreasing_by
  all_goals decreasing_trivial

end Flapjack
