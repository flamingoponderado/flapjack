import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanGlobals.CompileExpExact

namespace Flapjack.Test.PanGlobalsCompileExpExactParity

/-! Direct parity for the exact `pan_globals$compile_exp_def` port
    (`pan_globalsScript.sml:18-46`) over the exact `ExpHOL`/`MlS`/`ShapeHOL`
    carrier and the finite-support `PanGlobalsContextExact`.

    Replays the five direct HOL-EVAL rows of
    `scripts/hol-probes/pan_globals_compile_exp_probe.out`
    (`local`, `global_hit`, `global_miss`, `top_addr`, `nested`) at width 8 with
    the probe context `globals = {g := (One, 8w)}`, `globals_size = 1w`,
    `max_globals_size = 16w`. -/

open Flapjack
open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL)
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)

/-- The probe context of `pan_globals_compile_exp_probeScript.sml` at width 8:
    `globals = FEMPTY |+ («g», (One, 8w))`, `globals_size = 1w`,
    `max_globals_size = 16w`. -/
def exactProbeContext : PanGlobalsContextExact 8 where
  globals :=
    { lookup := fun key => if key = ofString "g" then some (.one, 8) else none
      finiteSupport := by
        refine ⟨[ofString "g"], ?_⟩
        intro key hkey
        by_cases h : key = ofString "g"
        · simp [h]
        · simp [h] at hkey }
  globalsSize := 1
  maxGlobalsSize := 16

/-- The `local` probe row: `Var Local «x»` is the identity. -/
@[simp] theorem global_compile_exp_exact_local :
    compileExpExactHOL exactProbeContext
        (.var .local (ofString "x") : ExpHOL 8) =
      .var .local (ofString "x") :=
  compileExpExactHOL.eq_2 _ _

/-- The `global_hit` probe row:
    `Load One (Op Sub [TopAddr; Const 8w])`. -/
@[simp] theorem global_compile_exp_exact_global_hit :
    compileExpExactHOL exactProbeContext
        (.var .global (ofString "g") : ExpHOL 8) =
      .load .one (.op .sub [.topAddr, .const (8 : BitVec 8)]) := by
  rw [compileExpExactHOL.eq_3]
  rfl

/-- The `global_miss` probe row: `Const 0w`. -/
@[simp] theorem global_compile_exp_exact_global_miss :
    compileExpExactHOL exactProbeContext
        (.var .global (ofString "missing") : ExpHOL 8) =
      .const (0 : BitVec 8) := by
  rw [compileExpExactHOL.eq_3]
  rfl

/-- The `top_addr` probe row: `Op Sub [TopAddr; Const 16w]`. -/
@[simp] theorem global_compile_exp_exact_top_addr :
    compileExpExactHOL exactProbeContext (.topAddr : ExpHOL 8) =
      .op .sub [.topAddr, .const (16 : BitVec 8)] :=
  compileExpExactHOL.eq_16 _

/-- The `nested` probe row:
    `Op Add [Load One (Op Sub [TopAddr; Const 8w]); Op Sub [TopAddr; Const 16w]]`. -/
@[simp] theorem global_compile_exp_exact_nested :
    compileExpExactHOL exactProbeContext
        (.op .add [.var .global (ofString "g"), .topAddr] : ExpHOL 8) =
      .op .add
        [.load .one (.op .sub [.topAddr, .const (8 : BitVec 8)]),
         .op .sub [.topAddr, .const (16 : BitVec 8)]] := by
  rw [compileExpExactHOL.eq_11]
  rw [compileExpExactHOLList.eq_2]
  rw [compileExpExactHOLList.eq_2]
  rw [compileExpExactHOLList.eq_1]
  rw [compileExpExactHOL.eq_3]
  rw [compileExpExactHOL.eq_16]
  rfl

/-- The five `pan_globals_compile_exp_probe.out` rows evaluated through the
    exact carrier, as a single Bool fixture. -/
def parityGuard : Bool :=
  (match compileExpExactHOL exactProbeContext
      (.var .local (ofString "x") : ExpHOL 8) with
   | .var .local name => toStringOfBytes name == "x"
   | _ => false) &&
  (match compileExpExactHOL exactProbeContext
      (.var .global (ofString "g") : ExpHOL 8) with
   | .load .one (.op .sub [.topAddr, .const address]) =>
       address == (8 : BitVec 8)
   | _ => false) &&
  (match compileExpExactHOL exactProbeContext
      (.var .global (ofString "missing") : ExpHOL 8) with
   | .const value => value == (0 : BitVec 8)
   | _ => false) &&
  (match compileExpExactHOL exactProbeContext (.topAddr : ExpHOL 8) with
   | .op .sub [.topAddr, .const address] => address == (16 : BitVec 8)
   | _ => false) &&
  (match compileExpExactHOL exactProbeContext
      (.op .add [.var .global (ofString "g"), .topAddr] : ExpHOL 8) with
   | .op .add [.load .one (.op .sub [.topAddr, .const first]),
               .op .sub [.topAddr, .const second]] =>
       first == (8 : BitVec 8) && second == (16 : BitVec 8)
   | _ => false)

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let result := parityGuard
  IO.println (if result then
    "PASS pan_globals compile_exp_def exact-carrier parity (5 HOL rows)"
    else "FAIL pan_globals compile_exp_def exact-carrier parity (5 HOL rows)")
  pure result

end Flapjack.Test.PanGlobalsCompileExpExactParity
