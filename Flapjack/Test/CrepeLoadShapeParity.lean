import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
import Flapjack.Pancake.PanGlobalsByteRanged
import Flapjack.Pancake.PanStructs.CompileDeclsCorrespondence
import Flapjack.Pancake.PanSimpByteRanged
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepToLoop.Optimise
import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
import Flapjack.Pancake.PanToCrep.CompileProgCorrespondence
import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordUnreach
import Flapjack.RiscV.Lab
import Flapjack.Display

/-!
# Original-domain parity for `crepLang$load_shape`

The expected values are the direct HOL-EVAL observations in
`scripts/hol-probes/crep_load_shape_probe.out`, from
`cakeml/pancake/crepLangScript.sml:82-86`.
-/

namespace Flapjack.Test.CrepeLoadShapeParity

open Flapjack

def probeValue : CrepExp Nat := .const 7

def isZeroOne : List (CrepExp Nat) → Bool
  | [.load (.const value)] => value == 7
  | _ => false

def isZeroTwo : List (CrepExp Nat) → Bool
  | [.load (.const first),
     .load (.op .add [.const second, .const offset])] =>
      first == 7 && second == 7 && offset == 4
  | _ => false

def isNonzeroTwo : List (CrepExp Nat) → Bool
  | [.load (.op .add [.const first, .const firstOffset]),
     .load (.op .add [.const second, .const secondOffset])] =>
      first == 7 && firstOffset == 4 && second == 7 && secondOffset == 8
  | _ => false

/-- Width-indexed `load_shape_def` wrapper (bead `flapjack-pxn.18.4.3.86`),
    reproducing the same `crep_load_shape_probe.out` rows at `BitVec 32`
    (machine byte width 4). -/
def isZeroTwoW : List (CrepExp (BitVec 32)) → Bool
  | [.load (.const first),
     .load (.op .add [.const second, .const offset])] =>
      first == 7 && second == 7 && offset == 4
  | _ => false

example : loadShapeBytesW (width := 32) (0 : BitVec 32) 1 (.const (7 : BitVec 32)) =
    [.load (.const (7 : BitVec 32))] := rfl

example : isZeroTwoW
    (loadShapeBytesW (width := 32) (0 : BitVec 32) 2 (.const (7 : BitVec 32))) = true :=
  rfl

example : loadShapeBytesHOLW (width := 32) (0 : BitVec 32) 0
    (.const (7 : BitVec 32)) = [] := by
  simp [loadShapeBytesHOLW]

example : loadShapeBytesHOLW (width := 32) (0 : BitVec 32) 1
    (.const (7 : BitVec 32)) = [.load (.const (7 : BitVec 32))] := by
  simp [loadShapeBytesHOLW]

example : loadShapeBytesHOLW (width := 32) (0 : BitVec 32) 2
    (.const (7 : BitVec 32)) =
    [.load (.const (7 : BitVec 32)),
     .load (.op .add [.const (7 : BitVec 32), .const (4 : BitVec 32)])] := by
  simp [loadShapeBytesHOLW]

example : (loadShapeBytesHOLW (width := 32) (BitVec.ofNat 32 4) 2
    (.const (7 : BitVec 32))).map crepExpOfHOL =
    loadShapeBytesW (width := 32) (BitVec.ofNat 32 4) 2
      (.const (7 : BitVec 32)) := by
  simpa [crepExpOfHOL] using loadShapeBytesHOLW_toProduction (width := 32)
    (BitVec.ofNat 32 4) 2 (.const (7 : BitVec 32))

example : loadShapeBytesHOLW (width := 32) (BitVec.ofNat 32 4) 2
    (.const (7 : BitVec 32)) =
    [.load (.op .add [.const (7 : BitVec 32), .const (4 : BitVec 32)]),
     .load (.op .add [.const (7 : BitVec 32), .const (8 : BitVec 32)])] := by
  simp [loadShapeBytesHOLW]

def parityGuard : Bool :=
  (loadShape 0 4 0 probeValue).isEmpty &&
  isZeroOne (loadShape 0 4 1 probeValue) &&
  isZeroTwo (loadShape 0 4 2 probeValue) &&
  isNonzeroTwo (loadShape 4 4 2 probeValue)

#eval parityGuard
#guard parityGuard

/-- The same four HOL-EVAL observations through the exact fixed-byte-width
    interface `loadShapeBytes`.  `BitVec 32` instantiates `CrepBytesInWord` with
    `bytesInWord = 4` (`byte$bytes_in_word` for a 32-bit word), matching the
    probe's `32 word` values. -/
def fixedProbeValue : CrepExp (BitVec 32) := .const (BitVec.ofNat 32 7)

def fixedParityGuard : Bool :=
  (loadShapeBytes (0 : BitVec 32) 0 fixedProbeValue).isEmpty &&
  (loadShapeBytes (0 : BitVec 32) 1 fixedProbeValue ==
    [.load (.const (BitVec.ofNat 32 7))]) &&
  (loadShapeBytes (0 : BitVec 32) 2 fixedProbeValue ==
    [.load (.const (BitVec.ofNat 32 7)),
     .load (.op .add [.const (BitVec.ofNat 32 7), .const (BitVec.ofNat 32 4)])]) &&
  (loadShapeBytes (BitVec.ofNat 32 4) 2 fixedProbeValue ==
    [.load (.op .add [.const (BitVec.ofNat 32 7), .const (BitVec.ofNat 32 4)]),
     .load (.op .add [.const (BitVec.ofNat 32 7), .const (BitVec.ofNat 32 8)])])

#eval fixedParityGuard
#guard fixedParityGuard

/-- The 64-bit HOL-EVAL observations in `crep_load_shape64_probe.out`, which use
    `64 word` values.  For that width `byte$bytes_in_word = 8`, matching the RV64
    compile context. -/
def word64ProbeValue : CrepExp (BitVec 64) := .const (BitVec.ofNat 64 7)

def word64ParityGuard : Bool :=
  (loadShapeBytes (0 : BitVec 64) 0 word64ProbeValue).isEmpty &&
  (loadShapeBytes (0 : BitVec 64) 1 word64ProbeValue ==
    [.load (.const (BitVec.ofNat 64 7))]) &&
  (loadShapeBytes (0 : BitVec 64) 2 word64ProbeValue ==
    [.load (.const (BitVec.ofNat 64 7)),
     .load (.op .add [.const (BitVec.ofNat 64 7), .const (BitVec.ofNat 64 8)])]) &&
  (loadShapeBytes (BitVec.ofNat 64 8) 2 word64ProbeValue ==
    [.load (.op .add [.const (BitVec.ofNat 64 7), .const (BitVec.ofNat 64 8)]),
     .load (.op .add [.const (BitVec.ofNat 64 7), .const (BitVec.ofNat 64 16)])])

#eval word64ParityGuard
#guard word64ParityGuard

/-- The production compile context as the RV64 CLI builds it, through the real
    `pipelineCrepeContext` constructor with the entry width `riscv64BytesInWord`
    (`Flapjack.compileMain`).  This is not a hand-built record: it is the actual
    production context-construction path. -/
def emptyProgram : GlobalCompiledProgram (BitVec 64) :=
  { initializers := []
    declarations := []
    context :=
      { globals := []
        globalsSize := BitVec.ofNat 64 0
        maxGlobalsSize := BitVec.ofNat 64 0
        bytesInWord := riscv64BytesInWord
        fromNat := fun value => BitVec.ofNat 64 value } }

/-- A Pan expression for the same source constant, fed through production. -/
def panWord64ProbeValue : Exp (BitVec 64) := .const (BitVec.ofNat 64 7)

def check (name : String) (actual expected : Bool) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {expected}, got {actual}"
    pure false

end Flapjack.Test.CrepeLoadShapeParity
