module

public import Flapjack.Pancake.Semantics.CrepSem.HOLState
public import Flapjack.Pancake.Semantics.CrepProps

-- Checks below run compiled code from these modules.
public meta import Flapjack.AstHOL
public meta import Flapjack.Pancake.CrepLang
public meta import Flapjack.Pancake.CrepLang.Exp
public meta import Flapjack.Pancake.Semantics.PanSem
public meta import Flapjack.Pancake.WordLang
public meta import Flapjack.Pancake.Semantics.CrepProps
public meta import Flapjack.Pancake.Semantics.CrepSem.HOLState
@[expose] public section

/-!
Direct original-HOL evaluator rows for the exact executable `crepSem$eval_def`
port. Expected values are transcribed from `crep_eval_probe.out`,
`crep_eval_op_rv64_probe.out`, `crep_eval_crepop_mul_rv64_probe.out`,
`crep_eval_cmp_rv64_probe.out`, `crep_eval_shift_rv64_probe.out`,
`crep_eval_load_32_probe.out`, and `crep_eval_load_byte_probe.out`.
-/

namespace Flapjack.Test.CrepSemEvalExactParity

open Flapjack

def word8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n
def word64 (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

def exactLocals8 : HolFiniteMapExact Nat (HolWordLab 8) :=
  HolFiniteMapExact.update HolFiniteMapExact.empty (1, .word (word8 7))

def exactGlobals8 : HolFiniteMapExact (BitVec 5) (HolWordLab 8) :=
  HolFiniteMapExact.update HolFiniteMapExact.empty (4, .word (word8 11))

def exactDomain8 (address : BitVec 8) : Prop := address = word8 3

def exactFfi : HolFfiState Unit :=
  { oracle := fun _ state _ _ => .ret state []
    ffiState := ()
    ioEvents := [] }

def exactState8 : CrepSemHOLState 8 Unit where
  locals := exactLocals8
  globals := exactGlobals8
  code := HolFiniteMapExact.empty
  memory := fun address => if address == word8 3 then .word (word8 9) else .word 0
  memaddrs := exactDomain8
  shMemaddrs := fun _ => False
  clock := 0
  be := false
  ffi := exactFfi
  baseAddr := word8 12
  topAddr := word8 13

local instance : DecidablePred exactState8.memaddrs := by
  intro address
  change Decidable (address = word8 3)
  infer_instance

def exactDomain64 (address : BitVec 64) : Prop := address = word64 8

def exactState64 : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => .word (word64 0x1122334455667788)
  memaddrs := exactDomain64
  shMemaddrs := fun _ => False
  clock := 0
  be := false
  ffi := exactFfi
  baseAddr := word64 0
  topAddr := word64 0

-- Width-24 state from the LoadByte and Load32 HOL probes. All other state
-- fields are irrelevant to these expression evaluations.
def exactDomain24 (address : BitVec 24) : Prop := address = 4

def exactState24 (bigEndian : Bool) : CrepSemHOLState 24 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun address => if address == 4 then .word 0x332211 else .word 0
  memaddrs := exactDomain24
  shMemaddrs := fun _ => False
  clock := 0
  be := bigEndian
  ffi := exactFfi
  baseAddr := 0
  topAddr := 0

local instance : DecidablePred exactDomain24 := by
  intro address
  unfold exactDomain24
  infer_instance

-- The explicit decider is related to the HOL-facing evaluator by
-- `evalCrepSemHOLExpWithDecider_eq`.
def evalExact24 (bigEndian : Bool) (expression : CrepExpHOL 24) :=
  evalCrepSemHOLExpWithDecider (exactState24 bigEndian)
    (fun address => (show Decidable (address = (4 : BitVec 24)) from inferInstance)) expression

#guard evalExact24 false (.loadByte (.const 5)) == some (.word 0x33)
#guard evalExact24 true (.loadByte (.const 5)) == some (.word 0x11)
#guard evalExact24 false (.load32 (.const 4)) == some (.word 0x113322)

local instance : DecidablePred exactState64.memaddrs := by
  intro address
  change Decidable (address = word64 8)
  infer_instance

/- Executable regression spelling for the public exact evaluator: the
explicit decidability witness keeps this check computational while theorem
statements use the no-decider HOL-facing declaration. -/
def evalExact8 (expression : CrepExpHOL 8) :=
  evalCrepSemHOLExpWithDecider exactState8 (fun _ => inferInstance) expression

def evalExact8AtClock (clock : Nat) (expression : CrepExpHOL 8) :=
  evalCrepSemHOLExpWithDecider { exactState8 with clock := clock }
    (fun _ => inferInstance) expression

def evalExact64 (expression : CrepExpHOL 64) :=
  evalCrepSemHOLExpWithDecider exactState64 (fun _ => inferInstance) expression

#guard evalExact8 (.const (word8 5)) == some (.word (word8 5))
#guard evalExact8 (.var 1) == some (.word (word8 7))
#guard evalExact8 (.var 2) == none
#guard evalExact8 (.load (.const (word8 3))) == some (.word (word8 9))
#guard evalExact8 (.load (.const (word8 8))) == none
#guard evalExact8 (.loadGlob 4) == some (.word (word8 11))
#guard evalExact8 (.loadGlob 8) == none
#guard evalExact8 .baseAddr == some (.word (word8 12))
#guard evalExact8 .topAddr == some (.word (word8 13))
#guard evalExact8
    (.op .add [.const (word8 3), .const (word8 4)]) == some (.word (word8 7))
#guard evalExact8
    (.op .sub [.const (word8 7), .const (word8 2)]) == some (.word (word8 5))
#guard evalExact8 (.op .add []) == some (.word (word8 0))
#guard evalExact8 (.op .sub [.const (word8 3)]) == none
#guard evalExact8
    (.crepOp .mul [.const (word8 6), .const (word8 7)]) == some (.word (word8 42))
#guard evalExact8 (.crepOp .mul [.const (word8 3)]) == none
#guard evalExact8
    (.cmp .equal (.const (word8 5)) (.const (word8 5))) == some (.word (word8 1))
#guard evalExact8
    (.cmp .equal (.const (word8 5)) (.const (word8 6))) == some (.word (word8 0))
#guard evalExact8
    (.shift .lsl (.const (word8 1)) (.const (word8 3))) == some (.word (word8 8))
#guard evalExact8
    (.shift .lsl (.const (word8 1)) (.const (word8 8))) == none
#guard evalExact64 (.load32 (.const (word64 8))) ==
    some (.word (word64 0x55667788))
#guard evalExact64 (.loadByte (.const (word64 8))) ==
    some (.word (word64 136))

-- `crep_eval_cmp_rv64_probe.out`: all comparison constructors and both
-- overlapping and disjoint bit tests, on the exact HOL evaluator carrier.
#guard evalExact64 (.cmp .equal (.const 5) (.const 5)) == some (.word 1)
#guard evalExact64 (.cmp .equal (.const 5) (.const 6)) == some (.word 0)
#guard evalExact64 (.cmp .lower (.const 3) (.const 5)) == some (.word 1)
#guard evalExact64 (.cmp .less (.const 0xFFFFFFFFFFFFFFFF) (.const 1)) == some (.word 1)
#guard evalExact64 (.cmp .notEqual (.const 5) (.const 6)) == some (.word 1)
#guard evalExact64 (.cmp .notLower (.const 5) (.const 3)) == some (.word 1)
#guard evalExact64 (.cmp .notLess (.const 1) (.const 0xFFFFFFFFFFFFFFFF)) == some (.word 1)
#guard evalExact64 (.cmp .test (.const 0xF0) (.const 0x10)) == some (.word 0)
#guard evalExact64 (.cmp .test (.const 0xF0) (.const 0x0F)) == some (.word 1)
#guard evalExact64 (.cmp .notTest (.const 0xF0) (.const 0x10)) == some (.word 1)

-- `crep_eval_shift_rv64_probe.out`: all shift operators and their bounds.
#guard evalExact64 (.shift .lsl (.const 1) (.const 3)) == some (.word 8)
#guard evalExact64 (.shift .lsr (.const 16) (.const 2)) == some (.word 4)
#guard evalExact64 (.shift .asr (.const 0x8000000000000000) (.const 4)) ==
  some (.word 0xF800000000000000)
#guard evalExact64 (.shift .ror (.const 1) (.const 1)) ==
  some (.word 0x8000000000000000)
#guard evalExact64 (.shift .lsl (.const 7) (.const 0)) == some (.word 7)
#guard evalExact64 (.shift .lsl (.const 7) (.const 64)) == none

-- Preserve the previous total-domain source evaluator load observations.
def exactEverywhere64 : CrepSemHOLState 64 Unit :=
  { exactState64 with
    memory := fun _ => .word 0x0807060504030201
    memaddrs := fun _ => True }

def evalExactEverywhere64 (expression : CrepExpHOL 64) :=
  evalCrepSemHOLExpWithDecider exactEverywhere64 (fun _ => isTrue True.intro) expression

#guard evalExactEverywhere64 (.load32 (.const 0)) == some (.word 0x04030201)
#guard evalExactEverywhere64 (.loadByte (.const 0)) == some (.word 1)

-- Eight-bit rows from `hol_word_arithmetic_probe.out`.
#guard (3 : BitVec 8) + 5 == 8
#guard (3 : BitVec 8) * 5 == 15
#guard (3 : BitVec 8) - 5 == 254

-- Original `word_op_finite_probe.out` list-fold and arity rows.
#guard wordOpHOL .add ([3, 5] : List (BitVec 8)) == some 8
#guard wordOpHOL .add ([] : List (BitVec 8)) == some 0
#guard wordOpHOL .and ([] : List (BitVec 8)) == some 255
#guard wordOpHOL .or ([] : List (BitVec 8)) == some 0
#guard wordOpHOL .xor ([] : List (BitVec 8)) == some 0
#guard wordOpHOL .sub ([3, 5] : List (BitVec 8)) == some 254
#guard wordOpHOL .sub ([3] : List (BitVec 8)) == none
#guard wordOpHOL .sub ([1, 2, 3] : List (BitVec 8)) == none
#guard wordOpHOL .add ([3] : List (BitVec 8)) == some 3
#guard wordOpHOL .add ([1, 2, 3] : List (BitVec 8)) == some 6
#guard wordOpHOL .and ([12, 10] : List (BitVec 8)) == some 8
#guard wordOpHOL .and ([15, 6, 3] : List (BitVec 8)) == some 2
#guard wordOpHOL .or ([12, 3] : List (BitVec 8)) == some 15
#guard wordOpHOL .or ([1, 2, 4] : List (BitVec 8)) == some 7
#guard wordOpHOL .xor ([15, 10] : List (BitVec 8)) == some 5
#guard wordOpHOL .xor ([1, 2, 4] : List (BitVec 8)) == some 7
#guard wordOpHOL .sub ([] : List (BitVec 8)) == none

-- Original `word_sh_finite_probe.out` word and amount cases.
#guard wordShiftHOL .lsl (3 : BitVec 8) 0 == some 3
#guard wordShiftHOL .lsl (3 : BitVec 8) 1 == some 6
#guard wordShiftHOL .lsr (128 : BitVec 8) 7 == some 1
#guard wordShiftHOL .asr (128 : BitVec 8) 1 == some 192
#guard wordShiftHOL .ror (3 : BitVec 8) 1 == some 129
#guard wordShiftHOL .lsl (3 : BitVec 8) 8 == none
#guard wordShiftHOL .lsl (3 : BitVec 8) 9 == none

-- The source `n2w` probe's low and high bit observations.
#guard !(BitVec.ofNat 8 0).getLsbD 0
#guard (BitVec.ofNat 8 1).getLsbD 0
#guard !(BitVec.ofNat 8 1).getLsbD 1
#guard (BitVec.ofNat 8 128).getLsbD 7
#guard !(BitVec.ofNat 8 128).getLsbD 6

#guard evalExact8AtClock 5
    (.op .sub [.const (word8 7), .const (word8 2)]) ==
  evalExact8 (.op .sub [.const (word8 7), .const (word8 2)])

/-- HOL `eval_upd_clock_eq` row: replacing the clock leaves evaluation unchanged. -/
example : evalCrepSemHOLExp { exactState8 with clock := 5 }
    (.op .sub [.const (word8 7), .const (word8 2)]) =
  evalCrepSemHOLExp exactState8 (.op .sub [.const (word8 7), .const (word8 2)]) :=
  evalCrepSemHOLExp_upd_clock_eq exactState8 _ 5

/-- HOL `eval_load_shape_el_rel` row: the `n`-th generated load of
    `loadShapeBytesHOLW` evaluates like the strided direct load. -/
example :
    evalCrepSemHOLExp exactState8
        ((loadShapeBytesHOLW (width := 8) (0 : BitVec 8) 2
            (.const (word8 4)))[1]'(by simp [length_loadShapeHOLW])) =
      evalCrepSemHOLExp exactState8
        (.load (.op .add [.const (word8 4),
          .const ((0 : BitVec 8) + BitVec.ofNat 8 (8 / 8) * BitVec.ofNat 8 1)])) :=
  eval_loadShapeBytesHOLW_getElem exactState8 (0 : BitVec 8) 2 (.const (word8 4)) 1
    (by decide)

end Flapjack.Test.CrepSemEvalExactParity
