import Flapjack.Pancake.PanLang.Exp

/-!
# Generated `panLang` datatype size parity

HOL's `Datatype` command generates `shape_size`/`shape1_size`
(`cakeml/pancake/panLangScript.sml:35-39`) and
`exp_size`/`exp1_size`/`exp2_size`/`exp3_size` (`:53-69`).  Those equations are
not textual HOL declarations, so the Lean transcriptions
`Flapjack.Pancake.PanLang.shapeSizeHOL`, `shape1SizeHOL`, `mlstringSizeHOL`,
`expSizeHOL`, `exp1SizeHOL`, `exp2SizeHOL`, and `exp3SizeHOL` cannot carry an
`@[hol]` tag; the tagged `MEM_IMP_shape_size`/`MEM_IMP_exp_size` theorems are
stated over them.

This module pins the equations against the real CakeML `panLangTheory`: the
fixtures below match the `print_thm`/`print_eval` rows in
`scripts/hol-probes/pan_lang_size_probe.out`, which is produced by a probe that
imports `panLangTheory` compiled from the same source commit.  Every explicit
equation is definitional in the Lean transcription, and the concrete rows match
the probe's `EVAL` results.
-/

namespace Flapjack.Test.PanLangGeneratedSizeParity

open Flapjack.Pancake.PanLang

abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

/-- The probe source regenerated into `pan_lang_size_probe.out`. -/
def originalProbeSource : String :=
  "scripts/hol-probes/pan_lang_size_probe.out (real panLangTheory)"

/-! ### `shape_size` / `shape1_size` / `mlstring_size` clauses -/

example : shapeSizeHOL .one = 0 := rfl

example (shapes : List ShapeHOL) :
    shapeSizeHOL (.comb shapes) = 1 + shape1SizeHOL shapes := rfl

example (name : MlS) : shapeSizeHOL (.named name) = 1 + mlstringSizeHOL name := rfl

example : shape1SizeHOL ([] : List ShapeHOL) = 0 := rfl

example (shape : ShapeHOL) (shapes : List ShapeHOL) :
    shape1SizeHOL (shape :: shapes) = 1 + shapeSizeHOL shape + shape1SizeHOL shapes := rfl

example (a : List Flapjack.Basis.Pure.MlString.HolChar) :
    mlstringSizeHOL (.implode a) = 1 + listSizeHOL holCharSize a := rfl

/-! ### `exp_size` / `exp1_size` / `exp2_size` / `exp3_size` clauses -/

section
variable {width : Nat} [NeZero width] {α : Type} (f : α → Nat)

example (value : BitVec width) : expSizeHOL (width := width) f (.const value) = 1 + value.toNat := rfl

example (kind : VarKind) (name : MlS) :
    expSizeHOL (width := width) f (.var kind name) = 1 + (varkindSizeHOL kind + mlstringSizeHOL name) := rfl

example (fields : List (ExpHOL width)) :
    expSizeHOL (width := width) f (.rstruct fields) = 1 + exp3SizeHOL (width := width) f fields := rfl

example (index : Nat) (value : ExpHOL width) :
    expSizeHOL (width := width) f (.rfield index value) = 1 + (index + expSizeHOL (width := width) f value) := rfl

example (name : MlS) (fields : List (MlS × ExpHOL width)) :
    expSizeHOL (width := width) f (.nstruct name fields) = 1 + (mlstringSizeHOL name + exp1SizeHOL (width := width) f fields) := rfl

example (name : MlS) (value : ExpHOL width) :
    expSizeHOL (width := width) f (.nfield name value) = 1 + (mlstringSizeHOL name + expSizeHOL (width := width) f value) := rfl

example (shape : ShapeHOL) (address : ExpHOL width) :
    expSizeHOL (width := width) f (.load shape address) = 1 + (shapeSizeHOL shape + expSizeHOL (width := width) f address) := rfl

example (address : ExpHOL width) : expSizeHOL (width := width) f (.load32 address) = 1 + expSizeHOL (width := width) f address := rfl

example (address : ExpHOL width) : expSizeHOL (width := width) f (.loadByte address) = 1 + expSizeHOL (width := width) f address := rfl

example (operator : BinOp) (args : List (ExpHOL width)) :
    expSizeHOL (width := width) f (.op operator args) = 1 + (binopSizeHOL operator + exp3SizeHOL (width := width) f args) := rfl

example (operator : PanOp) (args : List (ExpHOL width)) :
    expSizeHOL (width := width) f (.panop operator args) = 1 + (panopSizeHOL operator + exp3SizeHOL (width := width) f args) := rfl

example (operator : Cmp) (left right : ExpHOL width) :
    expSizeHOL (width := width) f (.cmp operator left right) =
      1 + (cmpSizeHOL operator + (expSizeHOL (width := width) f left + expSizeHOL (width := width) f right)) := rfl

example (operator : Shift) (left right : ExpHOL width) :
    expSizeHOL (width := width) f (.shift operator left right) =
      1 + (shiftSizeHOL operator + (expSizeHOL (width := width) f left + expSizeHOL (width := width) f right)) := rfl

example : expSizeHOL (width := width) f (.baseAddr : ExpHOL width) = 0 := rfl
example : expSizeHOL (width := width) f (.topAddr : ExpHOL width) = 0 := rfl
example : expSizeHOL (width := width) f (.bytesInWord : ExpHOL width) = 0 := rfl

example : exp1SizeHOL (width := width) f ([] : List (MlS × ExpHOL width)) = 0 := rfl

example (pair : MlS × ExpHOL width) (rest : List (MlS × ExpHOL width)) :
    exp1SizeHOL (width := width) f (pair :: rest) = 1 + (exp2SizeHOL (width := width) f pair + exp1SizeHOL (width := width) f rest) := rfl

example (name : MlS) (value : ExpHOL width) :
    exp2SizeHOL (width := width) f (name, value) = 1 + (mlstringSizeHOL name + expSizeHOL (width := width) f value) := rfl

example : exp3SizeHOL (width := width) f ([] : List (ExpHOL width)) = 0 := rfl

example (e : ExpHOL width) (es : List (ExpHOL width)) :
    exp3SizeHOL (width := width) f (e :: es) = 1 + (expSizeHOL (width := width) f e + exp3SizeHOL (width := width) f es) := rfl

end

/-! ### Concrete rows matching the probe's `EVAL` results -/

/-- Probe rows `shape_size_one`, `shape_size_comb`, `shape_size_named`. -/
def shapeGuard : Bool :=
  shapeSizeHOL .one == 0 &&
  shapeSizeHOL (.comb [.one, .one]) == 3 &&
  shapeSizeHOL (.named (ml "A")) == 3

/-- Probe rows `exp_size_const`, `exp_size_var`, `exp_size_rstruct`,
    `exp_size_nstruct`. -/
def expGuard : Bool :=
  expSizeHOL (width := 8) (fun (_ : Nat) => 0) (.const (7 : BitVec 8)) == 8 &&
  expSizeHOL (width := 8) (fun (_ : Nat) => 0) (.var .local (ml "x")) == 3 &&
  expSizeHOL (width := 8) (fun (_ : Nat) => 0)
      (.rstruct [.const (1 : BitVec 8), .const (2 : BitVec 8)]) == 8 &&
  expSizeHOL (width := 8) (fun (_ : Nat) => 0)
      (.nstruct (ml "S") [(ml "f", .const (3 : BitVec 8))]) == 11

/-- Probe rows `exp_size_load`, `exp_size_load32`, `exp_size_op`,
    `exp_size_cmp`, `exp_size_base`. -/
def controlGuard : Bool :=
  expSizeHOL (width := 8) (fun (_ : Nat) => 0) (.load .one (.const (7 : BitVec 8))) == 9 &&
  expSizeHOL (width := 8) (fun (_ : Nat) => 0) (.load32 (.const (7 : BitVec 8))) == 9 &&
  expSizeHOL (width := 8) (fun (_ : Nat) => 0)
      (.op .add [.const (1 : BitVec 8), .const (2 : BitVec 8)]) == 8 &&
  expSizeHOL (width := 8) (fun (_ : Nat) => 0)
      (.cmp .equal (.const (1 : BitVec 8)) (.const (2 : BitVec 8))) == 6 &&
  expSizeHOL (width := 8) (fun (_ : Nat) => 0) (.baseAddr : ExpHOL 8) == 0

def parityGuard : Bool := shapeGuard && expGuard && controlGuard

#guard originalProbeSource ==
  "scripts/hol-probes/pan_lang_size_probe.out (real panLangTheory)"
#guard shapeGuard
#guard expGuard
#guard controlGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS generated panLang shape_size/exp_size match real panLangTheory probe"
    pure true
  else
    IO.println "FAIL generated panLang shape_size/exp_size match real panLangTheory probe"
    pure false

end Flapjack.Test.PanLangGeneratedSizeParity
