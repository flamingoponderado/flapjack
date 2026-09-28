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
the `ite` fields use the eight `Cmp` constructors and `RegImm (BitVec width)`;
the latter maps HOL `asm$reg_imm`'s `Reg` to Lean `.reg` and `Imm` to `.imm`,
with matching `Nat`/word payload types. Lean's `CrepMemOp` is a separate
datatype from HOL `asm$memop`, but its eight nullary constructors match in
order; both `HolLoopProg` and executable `LoopProg` use that same Lean carrier.
The FFI name is the exact `MlString` carrier rather than the executable
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

/-- Exact HOL `nested_seq_def` from `loopLangScript.sml:72` over the
width-indexed HOL `prog` carrier. This has no extra behavior: the empty list
becomes `Skip`, and a nonempty list becomes a left-associated-by-head `Seq`
chain with the recursive tail on the right. -/
@[hol "cakeml/pancake/loopLangScript.sml" "nested_seq_def"
  (words_as_type_indexed_bitvec)]
def loopNestedSeqHOL {width : Nat} [NeZero width] :
    List (HolLoopProg width) → HolLoopProg width
  | [] => .skip
  | statement :: statements => .seq statement (loopNestedSeqHOL statements)

/-- Exact HOL `locals_touched_def` (`loopLangScript.sml:77-85`) over the
width-indexed HOL `exp` carrier: the local variables read by an expression.
`FLAT (MAP locals_touched wexps)` is rendered through `List.attach` so the
recursion is well-founded; `List.attach_map_val` identifies it with the plain
`map`. -/
@[hol "cakeml/pancake/loopLangScript.sml" "locals_touched_def"
  (words_as_type_indexed_bitvec)]
def holLoopLocalsTouched {width : Nat} [NeZero width] : HolLoopExp width → List Nat
  | .const _ => []
  | .var v => [v]
  | .lookup _ => []
  | .load addr => holLoopLocalsTouched addr
  | .op _ wexps => (wexps.attach.map fun ⟨e, _⟩ => holLoopLocalsTouched e).flatten
  | .shift _ wexp1 wexp2 => holLoopLocalsTouched wexp1 ++ holLoopLocalsTouched wexp2
  | .baseAddr => []
  | .topAddr => []

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
live sets are related by `numSetListRel`; the FFI name uses the partial
`MlString.ofString` image, so no total projection of arbitrary HOL byte strings
to Lean `String` is claimed; every expression subterm is related by
`holLoopExpToExecutable`. -/

/-- Executable/faithful relation for HOL `num_set`: exactly the listed keys are
    present in the `spt`-backed set. -/
def numSetListRel (keys : List Nat) (tree : NumSet) : Prop :=
  keys.Nodup ∧ ∀ key, sptLookup key tree = some () ↔ key ∈ keys

/-- A deterministic list projection of the finite HOL `num_set` carrier.
The tree encoding sends left-child keys to `2*k+2`, right-child keys to
`2*k+1`, and a `BS` root to zero. This order is chosen for a simple checked
membership theorem; live-set consumers use it as a set, and uniqueness is
proved separately below. -/
def numSetKeys : NumSet → List Nat
  | .ln => []
  | .ls _ => [0]
  | .bn left right =>
      (numSetKeys left).map (fun key => 2 * key + 2) ++
        (numSetKeys right).map (fun key => 2 * key + 1)
  | .bs left _ right =>
      0 :: ((numSetKeys left).map (fun key => 2 * key + 2) ++
        (numSetKeys right).map (fun key => 2 * key + 1))

private theorem numSetKeys_mem (key : Nat) (tree : NumSet) :
    key ∈ numSetKeys tree ↔ sptMem key tree := by
  induction tree generalizing key with
  | ln => simp [numSetKeys, sptMem_ln]
  | ls value => simp [numSetKeys, sptMem_ls]
  | bn left right ihLeft ihRight =>
      simp [numSetKeys, List.mem_append, List.mem_map, sptMem_bn,
        ihLeft, ihRight, eq_comm]
  | bs left value right ihLeft ihRight =>
      simp [numSetKeys, List.mem_append, List.mem_map, sptMem_bs,
        ihLeft, ihRight, eq_comm]

private theorem nodupMapInjective {α β : Type} (f : α → β)
    (hf : Function.Injective f) : ∀ xs : List α, xs.Nodup → (xs.map f).Nodup
  | [], _ => by simp
  | head :: tail, h => by
      have hcons := List.nodup_cons.mp h
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨other, hother, heq⟩
        have hsame : head = other := hf heq.symm
        cases hsame
        exact hcons.1 hother
      · exact nodupMapInjective f hf tail hcons.2

private theorem numSetKeysMappedNodup (left right : List Nat)
    (hLeft : left.Nodup) (hRight : right.Nodup) :
    ((left.map (fun key => 2 * key + 2)) ++
      (right.map (fun key => 2 * key + 1))).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply nodupMapInjective (fun key : Nat => 2 * key + 2) ?_ left hLeft
    intro a b h
    change 2 * a + 2 = 2 * b + 2 at h
    omega
  · apply nodupMapInjective (fun key : Nat => 2 * key + 1) ?_ right hRight
    intro a b h
    change 2 * a + 1 = 2 * b + 1 at h
    omega
  · intro a ha b hb hab
    simp only [List.mem_map] at ha hb
    obtain ⟨ka, _, rfl⟩ := ha
    obtain ⟨kb, _, hkb⟩ := hb
    omega

private theorem numSetKeysMapped_ne_zero (keys : List Nat) :
    0 ∉ keys.map (fun key => 2 * key + 2) ∧
    0 ∉ keys.map (fun key => 2 * key + 1) := by
  constructor <;> intro hmem <;> simp only [List.mem_map] at hmem
  · obtain ⟨key, _, hkey⟩ := hmem
    omega
  · obtain ⟨key, _, hkey⟩ := hmem
    omega

private theorem numSetKeys_nodup (tree : NumSet) : (numSetKeys tree).Nodup := by
  induction tree with
  | ln => simp [numSetKeys]
  | ls value => simp [numSetKeys]
  | bn left right ihLeft ihRight =>
      exact numSetKeysMappedNodup _ _ ihLeft ihRight
  | bs left value right ihLeft ihRight =>
      apply List.nodup_cons.mpr
      constructor
      · intro hzero
        simp only [List.mem_append] at hzero
        rcases hzero with hleft | hright
        · exact (numSetKeysMapped_ne_zero (numSetKeys left)).1 hleft
        · exact (numSetKeysMapped_ne_zero (numSetKeys right)).2 hright
      · exact numSetKeysMappedNodup _ _ ihLeft ihRight

/-- The structural key list is a faithful finite-list view of a HOL
`num_set`: it has no duplicates and has exactly the `sptLookup` domain. -/
theorem numSetKeysListRel (tree : NumSet) : numSetListRel (numSetKeys tree) tree := by
  refine ⟨numSetKeys_nodup tree, ?_⟩
  intro key
  have hLookup : sptLookup key tree = some () ↔ sptMem key tree := by
    constructor
    · intro h
      exact (sptMem_iff_lookup key tree).2 ⟨(), h⟩
    · intro h
      obtain ⟨value, hvalue⟩ := (sptMem_iff_lookup key tree).1 h
      cases value
      exact hvalue
  rw [hLookup, ← numSetKeys_mem]

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
  | _, _ => false
termination_by _ faithful => sizeOf faithful
decreasing_by
  all_goals decreasing_trivial

/-! The exact compiler's output carrier contains `NumSet` fields while the
   executable Loop IR stores those fields as lists. `numSetKeys` now provides a
   checked deterministic projection and `numSetKeysListRel` proves its
   membership relation. The program-level theorem below covers nested call
   handlers. Decoding an exact `MlString` to production
   `String` and re-encoding it is total. The reverse production-name bridge
   remains premise-bound by `CrepProgNameRanged`. -/

/-- Project all exact HOL Loop constructors to the executable Loop carrier.
`projectLive` is supplied by the caller together with a proof that it
represents each `NumSet`. -/
def holLoopProgToExecutable {width : Nat} [NeZero width]
    (projectLive : NumSet → List Nat) : HolLoopProg width → LoopProg (BitVec width)
  | .skip => .skip
  | .assign name value => .assign name (holLoopExpToExecutable value)
  | .primitive destinations operator arguments => .primitive destinations operator arguments
  | .arith operation => .arith operation
  | .store address value => .store (holLoopExpToExecutable address) value
  | .setGlobal address value => .setGlobal address (holLoopExpToExecutable value)
  | .load32 address destination => .load32 address destination
  | .loadByte address destination => .loadByte address destination
  | .store32 address value => .store32 address value
  | .storeByte address value => .storeByte address value
  | .seq first second =>
      .seq (holLoopProgToExecutable projectLive first)
        (holLoopProgToExecutable projectLive second)
  | .ite operator condition right thenBranch elseBranch live =>
      .ite operator condition right (holLoopProgToExecutable projectLive thenBranch)
        (holLoopProgToExecutable projectLive elseBranch) (projectLive live)
  | .loop liveIn body liveOut =>
      .loop (projectLive liveIn) (holLoopProgToExecutable projectLive body)
        (projectLive liveOut)
  | .break label => .break label
  | .continue label => .continue label
  | .raise exception => .raise exception
  | .return values => .return values
  | .shMem operator name address =>
      .shMem operator name (holLoopExpToExecutable address)
  | .tick => .tick
  | .mark body => .mark (holLoopProgToExecutable projectLive body)
  | .fail => .fail
  | .locValue destination source => .locValue destination source
  | .call returns target arguments handler =>
      let executableReturns := returns.map (fun entry => (entry.1, projectLive entry.2))
      let executableHandler :=
        match handler with
        | none => none
        | some (exception, first, second, live) =>
            some (exception, holLoopProgToExecutable projectLive first,
              holLoopProgToExecutable projectLive second, projectLive live)
      .call executableReturns target arguments executableHandler
  | .ffi function configuration configurationLength array arrayLength live =>
      .ffi (Flapjack.Basis.Pure.MlString.toStringOfBytes function)
        configuration configurationLength array arrayLength (projectLive live)
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [HolLoopProg.call.sizeOf_spec]; omega)

/-- Structural projection using the checked deterministic Spt-key list. -/
def holLoopProgToExecutableCanonical {width : Nat} [NeZero width]
    (program : HolLoopProg width) : LoopProg (BitVec width) :=
  holLoopProgToExecutable numSetKeys program

/-- The structural exact-to-executable projection preserves the complete
faithful Loop relation whenever each supplied live-set list is exact. This is
Flapjack bridge infrastructure, not a separate HOL port. -/
theorem holLoopProgToExecutable_rel {width : Nat} [NeZero width]
    (projectLive : NumSet → List Nat)
    (hLive : ∀ live, numSetListRel (projectLive live) live)
    (program : HolLoopProg width) :
    loopProgExecRel (holLoopProgToExecutable projectLive program) program := by
  let mProg : HolLoopProg width → Prop :=
    fun p => loopProgExecRel (holLoopProgToExecutable projectLive p) p
  let mPair : HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ numSetListRel (projectLive p.2) p.2
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1 ∧ numSetListRel (projectLive p.2.2) p.2.2
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  change mProg program
  refine HolLoopProg.rec
      (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
      (motive_4 := mTriple) (motive_5 := mPair)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ program <;>
    simp_all [mProg, mPair, mTriple, mQuad, mHandler,
      holLoopProgToExecutable, loopProgExecRel, loopExpExecRel,
      Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
  case refine_23 =>
    intro returns target arguments handler hHandler
    cases returns with
    | none =>
        cases handler with
        | none => simp [holLoopProgToExecutable, loopProgExecRel]
        | some value =>
            rcases value with ⟨exception, first, second, live⟩
            simp [holLoopProgToExecutable, loopProgExecRel, hLive, hHandler]
    | some value =>
        rcases value with ⟨returnNames, returnLive⟩
        cases handler with
        | none => simp [holLoopProgToExecutable, loopProgExecRel, hLive]
        | some value =>
            rcases value with ⟨exception, first, second, live⟩
            simp [holLoopProgToExecutable, loopProgExecRel, hLive, hHandler]

/-- The canonical Spt-backed projection is related to every exact Loop
constructor by `numSetKeysListRel`. -/
theorem holLoopProgToExecutableCanonical_rel {width : Nat} [NeZero width]
    (program : HolLoopProg width) :
    loopProgExecRel (holLoopProgToExecutableCanonical program) program := by
  simpa [holLoopProgToExecutableCanonical] using
    holLoopProgToExecutable_rel numSetKeys numSetKeysListRel program

/-! ### Introduction lemmas for `loopProgExecRel`

Flapjack bridge infrastructure (no `@[hol]` tag): introduction/closure rules for
the executable/faithful program relation, so code tables built from the exact
`loopLang$prog` carrier can be related to production programs through every
non-`num_set` constructor and recursively through `seq`/`mark`.  Constructors
carrying `num_set` live sets are intentionally not covered here, since the
executable side stores an explicit `List Nat` and the enumeration bridge is a
separate prerequisite. -/

theorem loopProgExecRel_skip {width : Nat} [NeZero width] :
    loopProgExecRel (width := width) (.skip : LoopProg (BitVec width)) .skip := by
  simp [loopProgExecRel]

theorem loopProgExecRel_assign {width : Nat} [NeZero width] (name : Nat)
    (value : HolLoopExp width) :
    loopProgExecRel (width := width) (.assign name (holLoopExpToExecutable value))
      (.assign name value) := by
  simp [loopProgExecRel, loopExpExecRel]

theorem loopProgExecRel_primitive {width : Nat} [NeZero width] (destinations : List Nat)
    (operator : PrimOp) (arguments : List Nat) :
    loopProgExecRel (width := width) (.primitive destinations operator arguments)
      (.primitive destinations operator arguments) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_arith {width : Nat} [NeZero width] (operation : LoopArith) :
    loopProgExecRel (width := width) (.arith operation) (.arith operation) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_load32 {width : Nat} [NeZero width] (address destination : Nat) :
    loopProgExecRel (width := width) (.load32 address destination)
      (.load32 address destination) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_loadByte {width : Nat} [NeZero width] (address destination : Nat) :
    loopProgExecRel (width := width) (.loadByte address destination)
      (.loadByte address destination) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_store32 {width : Nat} [NeZero width] (address value : Nat) :
    loopProgExecRel (width := width) (.store32 address value)
      (.store32 address value) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_storeByte {width : Nat} [NeZero width] (address value : Nat) :
    loopProgExecRel (width := width) (.storeByte address value)
      (.storeByte address value) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_break {width : Nat} [NeZero width] (label : Nat) :
    loopProgExecRel (width := width) (.break label) (.break label) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_continue {width : Nat} [NeZero width] (label : Nat) :
    loopProgExecRel (width := width) (.continue label) (.continue label) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_raise {width : Nat} [NeZero width] (exception : Nat) :
    loopProgExecRel (width := width) (.raise exception) (.raise exception) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_return {width : Nat} [NeZero width] (values : List Nat) :
    loopProgExecRel (width := width) (.return values) (.return values) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_tick {width : Nat} [NeZero width] :
    loopProgExecRel (width := width) (.tick : LoopProg (BitVec width)) .tick := by
  simp [loopProgExecRel]

theorem loopProgExecRel_fail {width : Nat} [NeZero width] :
    loopProgExecRel (width := width) (.fail : LoopProg (BitVec width)) .fail := by
  simp [loopProgExecRel]

theorem loopProgExecRel_locValue {width : Nat} [NeZero width] (destination source : Nat) :
    loopProgExecRel (width := width) (.locValue destination source)
      (.locValue destination source) := by
  simp [loopProgExecRel]

theorem loopProgExecRel_seq {width : Nat} [NeZero width]
    {executableFirst : LoopProg (BitVec width)} {faithfulFirst : HolLoopProg width}
    {executableSecond : LoopProg (BitVec width)} {faithfulSecond : HolLoopProg width}
    (hFirst : loopProgExecRel executableFirst faithfulFirst)
    (hSecond : loopProgExecRel executableSecond faithfulSecond) :
    loopProgExecRel (.seq executableFirst executableSecond)
      (.seq faithfulFirst faithfulSecond) := by
  simp only [loopProgExecRel]
  exact ⟨hFirst, hSecond⟩

theorem loopProgExecRel_mark {width : Nat} [NeZero width]
    {executableBody : LoopProg (BitVec width)} {faithfulBody : HolLoopProg width}
    (h : loopProgExecRel executableBody faithfulBody) :
    loopProgExecRel (.mark executableBody) (.mark faithfulBody) := by
  simpa only [loopProgExecRel] using h

end Flapjack
