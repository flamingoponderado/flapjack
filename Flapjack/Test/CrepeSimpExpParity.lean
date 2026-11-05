import Flapjack.Test.CrepArithExactParity
import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepRuntimeTarget
import Flapjack.Pancake.Proofs.CrepArith
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.RiscV.PanMemory

namespace Flapjack.Test.CrepeSimpExpParity

/-! Exact carrier replay of the direct HOL `simp_exp` Var/Const EVAL rows. The
matching native `eval_def` preservation cases, including the proof-script-local
code-map update and full word_lab result, are kernel-checked in
`CrepArith.HOLStateMapc`. -/
example : crepSimpExpHOL (.var 7 : CrepExpHOL 8) = .var 7 := by
  simp [crepSimpExpHOL]

example (value : BitVec 8) :
    crepSimpExpHOL (.const value) = .const value := by
  simp [crepSimpExpHOL]

-- Additional 64-bit rows from `crep_simp_exp_probe.out`.
example : crepSimpExpHOL (.const (11 : BitVec 64)) = .const 11 := by
  simp [crepSimpExpHOL]
example : crepSimpExpHOL (.var 7 : CrepExpHOL 64) = .var 7 := by
  simp [crepSimpExpHOL]
#guard match crepSimpExpHOL (.crepOp .mul [.var 2, .const (8 : BitVec 64)]) with
  | .shift .lsl (.var 2) (.const 3) => true | _ => false

-- The HOL probe varies all fields except locals.
private def exactLocals (state : CrepSemHOLState 64 Unit) (value : BitVec 64) :
    CrepSemHOLState 64 Unit :=
  { state with locals := HolFiniteMapExact.empty.update (2, .word value) }

private def mulEight : CrepExpHOL 64 := .crepOp .mul [.var 2, .const 8]
private def nestedMul : CrepExpHOL 64 := .crepOp .mul [mulEight, .const 3]

example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 5) mulEight = some (.word 40) := by
  simp [evalCrepSemHOLExp, exactLocals, HolFiniteMapExact.update, FUPDATE,
    mulEight, crepOpCrepWord]
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 5) (crepSimpExpHOL mulEight) = some (.word 40) := by
  simp [mulEight, Flapjack.Test.CrepArithExactParity.simpMul,
    crepSimpExpHOL, crepDestConstHOL, crepMulConstHOL, crepDest2ExpHOL, evalCrepSemHOLExp,
    exactLocals, HolFiniteMapExact.update, FUPDATE, mulEight, wordShiftHOL]

-- Preserve the earlier 7 * 8 and (7 * 8) * 3 evaluation checks.
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 7) mulEight = some (.word 56) := by
  simp [evalCrepSemHOLExp, exactLocals, HolFiniteMapExact.update, FUPDATE,
    mulEight, crepOpCrepWord]
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 7) (crepSimpExpHOL mulEight) = some (.word 56) := by
  simp [mulEight, Flapjack.Test.CrepArithExactParity.simpMul,
    crepSimpExpHOL, crepDestConstHOL, crepMulConstHOL, crepDest2ExpHOL, evalCrepSemHOLExp,
    exactLocals, HolFiniteMapExact.update, FUPDATE, mulEight, wordShiftHOL]
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 7) nestedMul = some (.word 168) := by
  simp [evalCrepSemHOLExp, exactLocals, HolFiniteMapExact.update, FUPDATE,
    nestedMul, mulEight, crepOpCrepWord]
example (state : CrepSemHOLState 64 Unit) :
    evalCrepSemHOLExp (exactLocals state 7) (crepSimpExpHOL nestedMul) = some (.word 168) := by
  simp [mulEight, nestedMul, Flapjack.Test.CrepArithExactParity.simpMul,
    crepSimpExpHOL, crepDestConstHOL, crepMulConstHOL, crepDest2ExpHOL, evalCrepSemHOLExp,
    exactLocals, HolFiniteMapExact.update, FUPDATE, nestedMul, mulEight,
    wordShiftHOL, crepOpCrepWord]

/-! HOL words use a finite Boolean-function carrier. This direct check
    exercises its `Fin n` encoding and conversion to the production BitVec
    representation independently of the expression evaluator bridge. -/
def holBits4 : Fin 4 → Bool := fun index => index.val == 0 || index.val == 2

#guard holWordBitsToBitVec holBits4 == BitVec.ofNat 4 5
#guard holWordBitsToBitVec (holBits4 + holBits4) == BitVec.ofNat 4 10
#guard holWordBitsToBitVec (holBits4 * holBits4) == BitVec.ofNat 4 9

@[instance_reducible] private def fin4WordDimension :
    HolFiniteDimension (Fin 4) := inferInstance

/-! HOL word addition and multiplication are defined by `n2w` after natural
    arithmetic on `w2n`; the generic source-shaped adapters reduce to the same
    BitVec operations under the explicit finite-index enumeration. -/
#guard holWordToBitVec fin4WordDimension
    (holFiniteWordSourceAdd fin4WordDimension holBits4 holBits4) ==
      BitVec.ofNat 4 10
#guard holWordToBitVec fin4WordDimension
    (holFiniteWordSourceMul fin4WordDimension holBits4 holBits4) ==
      BitVec.ofNat 4 9
#guard holWordToBitVec fin4WordDimension
    (holFiniteWordSourceSub fin4WordDimension holBits4 (fun _ => true)) ==
      BitVec.ofNat 4 6

/-! These kernel checks mirror the original HOL `n2w_def` probe for zero,
    one, and the high set bit. Numeric FCP index 0 is the least-significant
    bit, as stated generally by HOL `word_index_n2w`. -/
#guard holWordBitsToBitVec (fun i : Fin 8 => Nat.testBit 0 i.val) ==
  BitVec.ofNat 8 0
#guard holWordBitsToBitVec (fun i : Fin 8 => Nat.testBit 1 i.val) ==
  BitVec.ofNat 8 1
#guard holWordBitsToBitVec (fun i : Fin 8 => Nat.testBit 128 i.val) ==
  BitVec.ofNat 8 128

example : Nat.testBit 0 0 = false := by decide
example : Nat.testBit 1 0 = true := by decide
example : Nat.testBit 1 1 = false := by decide
example : Nat.testBit 128 7 = true := by decide
example : Nat.testBit 128 6 = false := by decide

example : bitVecToHolWordBits (holWordBitsToBitVec holBits4) = holBits4 :=
  bitVecToHolWordBits_holWordBitsToBitVec holBits4

example :
    holWordBitsToBitVec (bitVecToHolWordBits (BitVec.ofNat 4 5)) =
      BitVec.ofNat 4 5 :=
  holWordBitsToBitVec_bitVecToHolWordBits (BitVec.ofNat 4 5)

/-! The general finite-dimension adapter also works when the dimension is not
    represented by `Fin` in the source theorem. Here `Bool` is explicitly
    enumerated as two indices and its word carrier is transported to BitVec. -/
@[instance_reducible] def boolWordDimension : HolFiniteDimension Bool where
  width := 2
  width_pos := by decide
  encode := fun index => if index then 1 else 0
  decode := fun index => index.val == 1
  encode_decode := by decide
  decode_encode := by decide

local instance : HolFiniteDimension Bool := boolWordDimension

/-! The arbitrary-index n2w adapter is pointwise `BIT` at the number assigned
    by the dimension encoding, matching HOL's FCP `finite_index` convention.
    The dimension decoder itself satisfies HOL's unique-in-range property. -/
#guard holFiniteWordN2W boolWordDimension 1 false == true
#guard holFiniteWordN2W boolWordDimension 1 true == false
#guard holFiniteWordN2W boolWordDimension 2 true == true

example (value : Bool) :
    ∃ index, index < boolWordDimension.width ∧
      holFiniteIndex boolWordDimension index = value ∧
      ∀ other, other < boolWordDimension.width →
        holFiniteIndex boolWordDimension other = value → other = index :=
  holFiniteIndex_bijective boolWordDimension value

example (value index : Nat) (hindex : index < boolWordDimension.width) :
    holFiniteWordN2W boolWordDimension value
        (holFiniteIndex boolWordDimension index) = Nat.testBit value index :=
  holFiniteWordN2W_at_finiteIndex boolWordDimension value index hindex

example (word : Bool → Bool) :
    holFiniteWordW2N boolWordDimension word =
      finWordSBitSum boolWordDimension.width
        (fun index => word (holFiniteIndex boolWordDimension index.val)) :=
  holFiniteWordW2N_eq_finiteIndexSBitSum boolWordDimension word

@[instance_reducible] def boolWordDimensionSwapped : HolFiniteDimension Bool where
  width := 2
  width_pos := by decide
  encode := fun index => if index then 0 else 1
  decode := fun index => index.val == 0
  encode_decode := by decide
  decode_encode := by decide

example (value : Bool) :
    ∃ index, index < boolWordDimensionSwapped.width ∧
      holFiniteIndex boolWordDimensionSwapped index = value ∧
      ∀ other, other < boolWordDimensionSwapped.width →
        holFiniteIndex boolWordDimensionSwapped other = value → other = index :=
  holFiniteIndex_bijective boolWordDimensionSwapped value

example (value index : Nat) (hindex : index < boolWordDimensionSwapped.width) :
    holFiniteWordN2W boolWordDimensionSwapped value
        (holFiniteIndex boolWordDimensionSwapped index) = Nat.testBit value index :=
  holFiniteWordN2W_at_finiteIndex boolWordDimensionSwapped value index hindex

/-! Both witnesses satisfy HOL's finite_index bijection property, while they
    encode different dictionaries: `n2w 1` changes when the index order is
    permuted. The all-width proof works under either dictionary; the exact HOL
    instance for a concrete index type still needs to be identified. -/
example :
    bitVecToHolWord boolWordDimension (BitVec.ofNat 2 1) ≠
      bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 1) := by
  intro h
  have hFalse := congrFun h false
  have hleft :
      bitVecToHolWord boolWordDimension (BitVec.ofNat 2 1) false = true := by decide
  have hright :
      bitVecToHolWord boolWordDimensionSwapped (BitVec.ofNat 2 1) false = false := by decide
  rw [hleft, hright] at hFalse
  cases hFalse

def boolDimensionWord : Bool → Bool := id
def boolDimensionOne : Bool → Bool :=
  bitVecToHolWord boolWordDimension (BitVec.ofNat 2 1)

/-! The generic finite-word comparison instance handles signed order from the
    source word encoding: the 2-bit value 2 (two's-complement -2) is below 1. -/
#guard PanCmp.less boolDimensionWord boolDimensionOne
#guard holWordToBitVec boolWordDimension
  (evalPanCmp .less boolDimensionWord boolDimensionOne) == BitVec.ofNat 2 1

#guard wordOp .add [] == some (0 : Bool → Bool)
#guard wordOp .and [] == some (Complement.complement (0 : Bool → Bool))
#guard wordOp .or [] == some (0 : Bool → Bool)
#guard wordOp .xor [] == some (0 : Bool → Bool)
#guard wordOp .sub [boolDimensionWord] == none
#guard wordOp .sub [boolDimensionWord, boolDimensionWord, boolDimensionWord] == none

example (operator : BinOp) (values : List (Bool → Bool)) :
    wordOp operator values =
      (wordOpHOL operator (values.map (holWordToBitVec boolWordDimension))).map
        (bitVecToHolWord boolWordDimension) :=
  holFiniteWord_wordOp_toBitVec boolWordDimension operator values

/-! The source `word_sh` contract is width-generic. This theorem checks all
    four operators for arbitrary Bool-index operands; the HOL-generated probe
    below records the zero, maximum-valid, width, and above-width boundaries. -/
example (operator : Shift) (left right : Bool → Bool) :
    evalPanShiftFull operator left right =
      (evalPanShiftFull operator (holWordToBitVec boolWordDimension left)
        (holWordToBitVec boolWordDimension right)).map
          (bitVecToHolWord boolWordDimension) :=
  holFiniteWord_evalPanShift_toBitVec boolWordDimension operator left right

def boolDimensionZero : Bool → Bool :=
  bitVecToHolWord boolWordDimension (BitVec.ofNat 2 0)

#guard (evalPanShiftFull .lsl boolDimensionWord boolDimensionZero).isSome
#guard (evalPanShiftFull .lsl boolDimensionWord boolDimensionWord).isSome == false

#guard holFiniteWordSBitSum boolWordDimension boolDimensionWord == 2

example : holFiniteWordW2N boolWordDimension boolDimensionWord = 2 := by
  rw [holFiniteWordW2N_eq_SBitSum]
  rfl

example : bitVecToHolWord boolWordDimension
    (holWordToBitVec boolWordDimension boolDimensionWord) = boolDimensionWord :=
  bitVecToHolWord_holWordToBitVec boolWordDimension boolDimensionWord

example : holWordToBitVec boolWordDimension
    (bitVecToHolWord boolWordDimension (BitVec.ofNat 2 2)) = BitVec.ofNat 2 2 :=
  holWordToBitVec_bitVecToHolWord boolWordDimension (BitVec.ofNat 2 2)

def boolDimensionHolState : CrepHolState (Bool → Bool) Unit where
  locals := fun name => if name == 0 then some (.word boolDimensionWord) else none
  globals := fun address => if address == 0 then some (.word boolDimensionWord) else none
  code := fun _ => none
  memory := fun _ => .word boolDimensionWord
  memaddrs := fun _ => true
  shMemaddrs := fun _ => false
  clock := 10
  bigEndian := false
  ffi := natCrepRuntimeFfiState
  baseAddress := boolDimensionWord
  topAddress := boolDimensionWord

#guard evalCrepRuntimeExp
    (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension) (.var 0) ==
      some boolDimensionWord
#guard evalCrepRuntimeExp
    (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension) (.loadGlob 0) ==
      some boolDimensionWord

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension) (.var 0) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState (.var 0) :=
  evalCrepRuntimeExp_finiteDimension_var boolWordDimension boolDimensionHolState 0

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension) (.loadGlob 0) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState (.loadGlob 0) :=
  evalCrepRuntimeExp_finiteDimension_loadGlob
    boolWordDimension boolDimensionHolState 0

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.op .add [.const boolDimensionWord, .const boolDimensionWord]) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.op .add [.const boolDimensionWord, .const boolDimensionWord]) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

/-! The Op case of `simp_exp_correct1` applies to every word operation and
    obtains one induction hypothesis for each argument expression. Exercise
    the exact HOL-word source evaluator with a successful two-argument Add;
    the recursive children use the tagged Const case above. -/
example :
    evalCrepHolFiniteWordSourceExp boolWordDimension boolDimensionHolState
        (.op .add [.const boolDimensionWord, .const boolDimensionWord]) ≠ none := by
  simp [evalCrepHolFiniteWordSourceExp, holFiniteWordSourceMemoryModel,
    wordOpHOL, wordOp]

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.cmp .equal (.const boolDimensionWord) (.const boolDimensionWord)) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.cmp .equal (.const boolDimensionWord) (.const boolDimensionWord)) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.shift .lsl (.const boolDimensionWord) (.const boolDimensionWord)) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.shift .lsl (.const boolDimensionWord) (.const boolDimensionWord)) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.crepOp .mul [.const boolDimensionWord, .const boolDimensionWord]) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.loadByte (.const boolDimensionWord)) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.loadByte (.const boolDimensionWord)) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

example :
    evalCrepRuntimeExp
        (boolDimensionHolState.toHolFiniteWordRuntime boolWordDimension)
        (.load32 (.const boolDimensionWord)) =
      evalCrepHolFiniteDimensionExp boolWordDimension boolDimensionHolState
        (.load32 (.const boolDimensionWord)) := by
  exact evalCrepRuntimeExp_finiteDimension_eq boolWordDimension
    boolDimensionHolState _

section SwappedFiniteIndex

local instance : HolFiniteDimension Bool := boolWordDimensionSwapped

end SwappedFiniteIndex

def holWordBitsState4 : CrepHolState (Fin 4 → Bool) Unit where
  locals := fun _ => none
  globals := fun _ => none
  code := fun _ => none
  memory := fun _ => .word holBits4
  memaddrs := fun _ => false
  shMemaddrs := fun _ => false
  clock := 0
  bigEndian := false
  ffi := natCrepRuntimeFfiState
  baseAddress := holBits4
  topAddress := holBits4

def holWordBits64 (value : Nat) : Fin 64 → Bool :=
  bitVecToHolWordBits (BitVec.ofNat 64 value)

def holWordBitsState64 : CrepHolState (Fin 64 → Bool) Unit where
  locals := fun _ => none
  globals := fun _ => none
  code := fun _ => none
  memory := fun _ => .word (holWordBits64 0x0807060504030201)
  memaddrs := fun address => address == holWordBits64 8
  shMemaddrs := fun _ => false
  clock := 0
  bigEndian := false
  ffi := natCrepRuntimeFfiState
  baseAddress := holWordBits64 0
  topAddress := holWordBits64 0

def holWordBitsMemoryEverywhereState64 : CrepHolState (Fin 64 → Bool) Unit :=
  { holWordBitsState64 with memaddrs := fun _ => true }

/-! Successful load cases reuse a 64-bit little-endian memory cell. The domain
    is total here so the constructor cases exercise the byte operations without
    adding an address-domain side condition. -/
#guard evalCrepHolFiniteWordSourceExp
    (instFinHolFiniteDimension (width := 64)) holWordBitsMemoryEverywhereState64
    (.load32 (.const (0 : Fin 64 → Bool))) == some (holWordBits64 0x04030201)
#guard evalCrepHolFiniteWordSourceExp
    (instFinHolFiniteDimension (width := 64)) holWordBitsMemoryEverywhereState64
    (.loadByte (.const (0 : Fin 64 → Bool))) == some (holWordBits64 1)

def holWordBitsState64WithLocal : CrepHolState (Fin 64 → Bool) Unit :=
  { holWordBitsState64 with
    locals := fun name =>
      if name == 2 then some (.word (holWordBits64 5)) else none }

def holWordBitsCmpResult (operator : Cmp) (left right : Nat) :
    Option (PanWordLab (Fin 64 → Bool)) :=
  (evalCrepRuntimeExp
    (holWordBitsState64.toHolFiniteWordSourceRuntime
      (instFinHolFiniteDimension (width := 64)))
    (.cmp operator (.const (holWordBits64 left)) (.const (holWordBits64 right)))).map
      PanWordLab.word

/-! The corresponding original HOL probe exercises all eight `word_cmp`
    constructors through `crepSem$eval`. These guards run the production
    source runtime on the same RV64 word cases, including signed-vs-unsigned
    order and overlapping/disjoint bit tests. -/
#guard holWordBitsCmpResult .equal 5 5 == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .equal 5 6 == some (.word (holWordBits64 0))
#guard holWordBitsCmpResult .lower 3 5 == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .less 0xFFFFFFFFFFFFFFFF 1 ==
  some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .notEqual 5 6 == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .notLower 5 3 == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .notLess 1 0xFFFFFFFFFFFFFFFF ==
  some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .test 0xF0 0x10 == some (.word (holWordBits64 0))
#guard holWordBitsCmpResult .test 0xF0 0x0F == some (.word (holWordBits64 1))
#guard holWordBitsCmpResult .notTest 0xF0 0x10 == some (.word (holWordBits64 1))

/-! Direct `word_sh_def` parity against the HOL observations in
`crep_eval_shift_rv64_probe.out`, including the zero-amount and width-bound
cases. -/
#guard wordShiftHOL .lsl (BitVec.ofNat 64 1) 3 == some (BitVec.ofNat 64 8)
#guard wordShiftHOL .lsr (BitVec.ofNat 64 16) 2 == some (BitVec.ofNat 64 4)
#guard wordShiftHOL .asr (BitVec.ofNat 64 0x8000000000000000) 4 ==
  some (BitVec.ofNat 64 0xF800000000000000)
#guard wordShiftHOL .ror (BitVec.ofNat 64 1) 1 ==
  some (BitVec.ofNat 64 0x8000000000000000)
#guard wordShiftHOL .lsl (BitVec.ofNat 64 7) 0 == some (BitVec.ofNat 64 7)
#guard wordShiftHOL .lsl (BitVec.ofNat 64 7) 64 == none

#guard evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime (.const holBits4) ==
  some holBits4
#guard evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime
    (.crepOp .mul [.const holBits4, .const holBits4]) ==
  some (bitVecToHolWordBits (BitVec.ofNat 4 9))

example :
    evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime
        (.loadByte (.const holBits4)) =
      evalCrepHolWordBitsExp holWordBitsState4 (.loadByte (.const holBits4)) :=
  evalCrepRuntimeExp_toHolWordBits_eq holWordBitsState4
    (.loadByte (.const holBits4))

example :
    evalCrepRuntimeExp holWordBitsState4.toHolWordBitsRuntime
        (.load32 (.const holBits4)) =
      evalCrepHolWordBitsExp holWordBitsState4 (.load32 (.const holBits4)) :=
  evalCrepRuntimeExp_toHolWordBits_eq holWordBitsState4
    (.load32 (.const holBits4))

example :
    crepRuntimeLoadByte
        (CrepHolState.toHolFiniteWordSourceRuntime
          (instFinHolFiniteDimension (width := 64)) holWordBitsState64)
        (holWordBits64 9) =
      crepHolEvalMemLoadByte
        (holFiniteWordSourceMemoryModel
          (instFinHolFiniteDimension (width := 64)) false)
        (holWordBits64 8) holWordBitsState64 (holWordBits64 9) :=
  crepHolFiniteWordSourceRuntime_loadByte holWordBitsState64 (holWordBits64 9)

example :
    crepRuntimeLoad32
        (CrepHolState.toHolFiniteWordSourceRuntime
          (instFinHolFiniteDimension (width := 64)) holWordBitsState64)
        (holWordBits64 8) =
      crepHolEvalMemLoad32
        (holFiniteWordSourceMemoryModel
          (instFinHolFiniteDimension (width := 64)) false)
        (holWordBits64 8) holWordBitsState64 (holWordBits64 8) :=
  crepHolFiniteWordSourceRuntime_load32 holWordBitsState64 (holWordBits64 8)

private def holWord64 (value : Nat) : Fin 64 → Bool :=
  bitVecToHolWordBits (BitVec.ofNat 64 value)

private def holWord64EvalState : CrepHolState (Fin 64 → Bool) Unit where
  locals := fun _ => none
  globals := fun _ => none
  code := fun _ => none
  memory := fun _ => .word (holWord64 0)
  memaddrs := fun _ => false
  shMemaddrs := fun _ => false
  clock := 10
  bigEndian := false
  ffi := natCrepRuntimeFfiState
  baseAddress := holWord64 0
  topAddress := holWord64 0

example :
    (evalCrepRuntimeExp
      (holWord64EvalState.toHolFiniteWordSourceRuntime
        (instFinHolFiniteDimension (width := 64)))
      (.const (holWord64 5))).map PanWordLab.word =
      some (.word (holWord64 5)) := by
  calc
    _ = evalCrepHolFiniteWordSourceExpWordLab
        (instFinHolFiniteDimension (width := 64)) holWord64EvalState
        (.const (holWord64 5)) :=
          evalCrepRuntimeExp_sourceWordLab_eq
            (instFinHolFiniteDimension (width := 64)) holWord64EvalState _
    _ = some (.word (holWord64 5)) := by
      simp [evalCrepHolFiniteWordSourceExpWordLab,
        evalCrepHolFiniteWordSourceExp]

end Flapjack.Test.CrepeSimpExpParity
