import Flapjack.Pancake.CrepToLoop.Proofs.Primop

/-!
# `crep_primop_loop_primop` replay fixtures

Kernel-checked replay of the local preservation theorem
`crepPrimopLoopPrimopHOL`, together with the concrete rows of the direct HOL
`EVAL` probe `scripts/hol-probes/crep_primop_loop_primop_probe.out`.  Bead
`flapjack-pxn.18.5.6.33.8`.
-/

namespace Flapjack.Test.CrepPrimopLoopPrimopParity

open Flapjack

private abbrev W := WordLocW 8

-- crep_valid=SOME [Word 8w; Word 0w]
def crepValid : Bool :=
  crepPrimopHOLExact .addCarry
    [.word (3 : BitVec 8), .word 4, .word 2] ==
    some [.word (8 : BitVec 8), .word 0]

-- loop_valid_mapped=SOME [Word 8w; Word 0w]
def loopValidMapped : Bool :=
  LoopSemStateFiniteExact.loopPrimop .addCarry
    [(.word (3 : BitVec 8) : W), .word 4, .word 2] ==
    some [.word (8 : BitVec 8), .word 0]

-- preserve_valid=T
def preserveValid : Bool :=
  match crepPrimopHOLExact .addCarry
      [.word (3 : BitVec 8), .word 4, .word 2] with
  | some resWs =>
      LoopSemStateFiniteExact.loopPrimop .addCarry
        (([.word (3 : BitVec 8), .word 4, .word 2]).map wlabWlocHOL) ==
        some (resWs.map wlabWlocHOL)
  | none => true

-- crep_overflow=SOME [Word 256w; Word 1w] (256w is 0w mod 256)
def crepOverflow : Bool :=
  crepPrimopHOLExact .addCarry
    [.word (255 : BitVec 8), .word 0, .word 1] ==
    some [.word (0 : BitVec 8), .word 1]

-- loop_overflow_mapped=SOME [Word 256w; Word 1w]
def loopOverflowMapped : Bool :=
  LoopSemStateFiniteExact.loopPrimop .addCarry
    [(.word (255 : BitVec 8) : W), .word 0, .word 1] ==
    some [.word (0 : BitVec 8), .word 1]

-- preserve_overflow=T
def preserveOverflow : Bool :=
  match crepPrimopHOLExact .addCarry
      [.word (255 : BitVec 8), .word 0, .word 1] with
  | some resWs =>
      LoopSemStateFiniteExact.loopPrimop .addCarry
        (([.word (255 : BitVec 8), .word 0, .word 1]).map wlabWlocHOL) ==
        some (resWs.map wlabWlocHOL)
  | none => true

-- crep_nonzero_carry=SOME [Word 256w; Word 1w] (any nonzero carry is one)
def crepNonzeroCarry : Bool :=
  crepPrimopHOLExact .addCarry
    [.word (255 : BitVec 8), .word 0, .word 7] ==
    some [.word (0 : BitVec 8), .word 1]

-- loop_nonzero_carry_mapped=SOME [Word 256w; Word 1w]
def loopNonzeroCarryMapped : Bool :=
  LoopSemStateFiniteExact.loopPrimop .addCarry
    [(.word (255 : BitVec 8) : W), .word 0, .word 7] ==
    some [.word (0 : BitVec 8), .word 1]

-- preserve_nonzero_carry=T
def preserveNonzeroCarry : Bool :=
  match crepPrimopHOLExact .addCarry
      [.word (255 : BitVec 8), .word 0, .word 7] with
  | some resWs =>
      LoopSemStateFiniteExact.loopPrimop .addCarry
        (([.word (255 : BitVec 8), .word 0, .word 7]).map wlabWlocHOL) ==
        some (resWs.map wlabWlocHOL)
  | none => true

-- crep_invalid_two=NONE / preserve_invalid_two=T
def preserveInvalidTwo : Bool :=
  match crepPrimopHOLExact .addCarry
      [.word (3 : BitVec 8), .word 4] with
  | some _ => false
  | none =>
      LoopSemStateFiniteExact.loopPrimop .addCarry
        (([.word (3 : BitVec 8), .word 4]).map wlabWlocHOL) == none

-- crep_invalid_four=NONE / preserve_invalid_four=T
def preserveInvalidFour : Bool :=
  match crepPrimopHOLExact .addCarry
      [.word (3 : BitVec 8), .word 4, .word 2, .word 0] with
  | some _ => false
  | none =>
      LoopSemStateFiniteExact.loopPrimop .addCarry
        (([.word (3 : BitVec 8), .word 4, .word 2, .word 0]).map wlabWlocHOL) == none

#guard crepValid
#guard loopValidMapped
#guard preserveValid
#guard crepOverflow
#guard loopOverflowMapped
#guard preserveOverflow
#guard crepNonzeroCarry
#guard loopNonzeroCarryMapped
#guard preserveNonzeroCarry
#guard preserveInvalidTwo
#guard preserveInvalidFour

/-- Kernel-checked replay of the valid oracle row: the exact theorem discharges
    the concrete instance, whose premise closes by `rfl`. -/
example :
    LoopSemStateFiniteExact.loopPrimop PrimOp.addCarry
      (([HolWordLab.word (3 : BitVec 8), HolWordLab.word 4,
        HolWordLab.word 2]).map wlabWlocHOL) =
      some (([HolWordLab.word (8 : BitVec 8),
        HolWordLab.word 0]).map wlabWlocHOL) :=
  crepPrimopLoopPrimopHOL _ _ _ rfl

/-- Kernel-checked replay of the overflow oracle row. -/
example :
    LoopSemStateFiniteExact.loopPrimop PrimOp.addCarry
      (([HolWordLab.word (255 : BitVec 8), HolWordLab.word 0,
        HolWordLab.word 1]).map wlabWlocHOL) =
      some (([HolWordLab.word (0 : BitVec 8),
        HolWordLab.word 1]).map wlabWlocHOL) :=
  crepPrimopLoopPrimopHOL _ _ _ rfl

def runChecks : IO Bool := do
  IO.println "PASS exact crep_primop/loop_primop preservation HOL parity"
  pure true

end Flapjack.Test.CrepPrimopLoopPrimopParity
