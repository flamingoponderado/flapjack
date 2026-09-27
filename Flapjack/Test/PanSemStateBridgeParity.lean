import Flapjack.Pancake.Semantics.PanSem.StateBridge

/-!
# Regression examples for the production/exact `PanSemState` bridge

Kernel-checked examples for `Flapjack/Pancake/Semantics/PanSem/StateBridge.lean`:
the value, code-entry and struct-context codecs and the forward/reverse state
relation codecs on concrete inputs.  Everything here is untagged infrastructure.
-/

namespace Flapjack.Test.PanSemStateBridgeParity

open Flapjack
open Flapjack.Pancake.PanLang

abbrev W := BitVec 64

/-- Word projection of a `ValueHOL` for guard comparison. -/
def valueWord? : ValueHOL 64 → Option Nat
  | .val (.word word) => some word.toNat
  | _ => none

/-- A byte-ranged production record value. -/
def recordValue : PanValue W :=
  .nStruct "Point" [("x", .word 3), ("y", .rStruct [.word 4])]

/-- Encoding then decoding the byte-ranged record recovers it. -/
example : panValueOfHOL (panValueToHOL recordValue) = recordValue := by
  apply panValueOfHOL_panValueToHOL
  simp [PanValueByteRanged, recordValue, NameRanged]

/-- Encoding then decoding a word value recovers it. -/
example : panValueOfHOL (panValueToHOL (PanValue.word (7 : W))) = .word 7 := by
  apply panValueOfHOL_panValueToHOL
  simp [PanValueByteRanged]

/-- Exact-side value round trip. -/
example :
    panValueToHOL (panValueOfHOL (ValueHOL.val (HolWordLab.word (11 : W)))) =
      .val (.word 11) := by
  simp

#guard valueWord? (panValueToHOL (.word (7 : W))) == some 7
#guard (holWordLabBits (HolWordLab.word (9 : W))).toNat == 9

/-- A concrete exact struct context. -/
def exactContext : StructContextExact :=
  [(Flapjack.Basis.Pure.MlString.ofString "S", { fields := [], size := 1 })]

example : panStructContextToHOL (panStructContextOfHOL exactContext) = exactContext := by
  simp only [panStructContextToHOL_panStructContextOfHOL]

/-- A concrete code entry round trips on the byte-ranged subset. -/
example :
    panLangEntryOfHOL (panLangEntryToHOL
      (([("x", Shape.one)], (Prog.skip : Prog W), Shape.one) :
        List (VarName × Shape) × Prog W × Shape)) =
      ([("x", Shape.one)], Prog.skip, Shape.one) := by
  apply panLangEntryOfHOL_panLangEntryToHOL
  simp [PanLangEntryByteRanged, ListParamByteRanged, ParamByteRanged, NameRanged,
    ProgByteRanged, ShapeByteRanged]

/-- A concrete exact state over `Unit` with empty code. -/
def exactState : PanSemStateExact 64 Unit where
  locals := fun name => if name = Flapjack.Basis.Pure.MlString.ofString "x"
    then some (.val (.word 7)) else none
  globals := fun _ => none
  structs := []
  code := fun _ => none
  eshapes := fun _ => none
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 5
  be := false
  ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
  baseAddr := 0
  topAddr := 100

/-- Every exact `code` lookup is `none`, so the empty list is a support. -/
theorem emptyCodeSupport :
    ∃ keys : List MlS, ∀ key, exactState.code key ≠ none → key ∈ keys :=
  ⟨[], fun _ hkey => absurd rfl hkey⟩

instance decidableExactMemaddrs : DecidablePred exactState.memaddrs :=
  fun _ => isFalse (by simp [exactState])

instance decidableExactShMemaddrs : DecidablePred exactState.shMemaddrs :=
  fun _ => isFalse (by simp [exactState])

/-- The reverse codec lands in the state relation on the concrete state. -/
example : PanSemStateRel (panSemStateOfExact exactState emptyCodeSupport) exactState :=
  panSemStateRel_ofExact exactState emptyCodeSupport

/-- The exact round trip holds on the concrete state. -/
example :
    panSemStateToExact (panSemStateOfExact exactState emptyCodeSupport)
      exactState.memory (panSemStateMemoryRel_ofExact exactState emptyCodeSupport) =
      exactState :=
  panSemStateToExact_ofExact exactState emptyCodeSupport

def runChecks : IO Bool := do
  IO.println "PASS production/exact PanSemState codec bridge (value/entry/struct/state)"
  pure true

end Flapjack.Test.PanSemStateBridgeParity
