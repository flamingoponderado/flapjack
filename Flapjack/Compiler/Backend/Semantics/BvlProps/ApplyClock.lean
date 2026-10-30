import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyClock
import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyCode

/-! Clock replacement for BVL primitive application. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

namespace ClockCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ClockCarrier

/-- Replace the clock in a successful optional primitive result. -/
def setClockOption {C F : Type} (clock : Nat) (result : Option (BvlSem.Value × State C F)) :
    Option (BvlSem.Value × State C F) :=
  result.map fun (value, state) => (value, { state with clock := clock })

/-- Global primitives commute with replacing the clock. -/
theorem applyGlobal_setClock {C F : Type} (op : ClosLang.GlobOp) (args : List BvlSem.Value)
    (state : State C F) (clock : Nat) :
    applyGlobal op args { state with clock := clock } =
      setClockOption clock (applyGlobal op args state) := by
  unfold applyGlobal setClockOption
  repeat' split
  all_goals simp_all [Function.comp_def]

/-- Block primitives commute with replacing the clock. -/
theorem applyBlock_setClock {C F : Type} (op : ClosLang.BlockOp) (args : List BvlSem.Value)
    (state : State C F) (clock : Nat) :
    applyBlock op args { state with clock := clock } =
      setClockOption clock (applyBlock op args state) := by
  unfold applyBlock setClockOption
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]

/-- Numeric primitives commute with replacing the clock. -/
theorem applyNumeric_setClock {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : State C F) (clock : Nat) :
    applyNumeric op args { state with clock := clock } =
      setClockOption clock (applyNumeric op args state) := by
  cases op <;> simp [applyNumeric, setClockOption, Option.map_map, Function.comp_def]


/-- Memory primitives commute with replacing the clock. -/
theorem applyMemory_setClock {C F : Type} (op : ClosLang.MemOp) (args : List BvlSem.Value)
    (state : State C F) (clock : Nat) :
    applyMemory op args { state with clock := clock } =
      setClockOption clock (applyMemory op args state) := by
  unfold applyMemory setClockOption
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]
  all_goals try omega
  all_goals try (repeat' (congr 1; funext value; cases value <;> simp [Option.map_bind, Function.comp_def]))


/-- Replace the clock in a successful primitive result. -/
def setClockResult {C F : Type} (clock : Nat) (result : Result (BvlSem.Value × State C F) BvlSem.Value) :
    Result (BvlSem.Value × State C F) BvlSem.Value :=
  match result with
  | .err error => .err error
  | .val (value, state) => .val (value, { state with clock := clock })

/-- Installation is independent of the input clock. -/
theorem doInstall_setClock {C F : Type} (args : List BvlSem.Value)
    (state : State C F) (clock : Nat) :
    doInstall (R := BvlSem.Value) args { state with clock := clock } =
      setClockResult clock (doInstall args state) := by
  cases state
  unfold doInstall
  repeat' (split <;> try simp_all [setClockResult])

/-- Every ordinary primitive application commutes with replacing the clock. -/
theorem doApp_setClock {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : State C F) (clock : Nat) :
    doApp op args { state with clock := clock } =
      setClockResult clock (doApp op args state) := by
  cases op with
  | globOp operation =>
    cases found : applyGlobal operation args state with
    | none => simp [doApp, applyGlobal_setClock, found, setClockOption, setClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyGlobal_setClock, found, setClockOption, setClockResult]
  | blockOp operation =>
    cases found : applyBlock operation args state with
    | none => simp [doApp, applyBlock_setClock, found, setClockOption, setClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyBlock_setClock, found, setClockOption, setClockResult]
  | memOp operation =>
    cases found : applyMemory operation args state with
    | none => simp [doApp, applyMemory_setClock, found, setClockOption, setClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyMemory_setClock, found, setClockOption, setClockResult]
  | intOp operation =>
    cases found : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, applyNumeric_setClock, found, setClockOption, setClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyNumeric_setClock, found, setClockOption, setClockResult]
  | wordOp operation =>
    cases found : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, applyNumeric_setClock, found, setClockOption, setClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyNumeric_setClock, found, setClockOption, setClockResult]
  | label =>
    simp only [doApp, setClockResult]
    repeat' split
    all_goals simp_all
  | install => exact doInstall_setClock args state clock
  | ffi | thunkOp =>
    simp only [doApp, setClockResult]
    repeat' split
    all_goals simp_all
    all_goals aesop
/-- Successful primitive application is unaffected by clock replacement. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "do_app_change_clock"
  (fmap_as_finite_support := [refs])]
theorem doAppChangeClock {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (value : BvlSem.Value)
    (next : Flapjack.Compiler.Backend.BvlSem.State C F) (clock : Nat)
    (run : doApp op args state = .val (value, next)) :
    doApp op args { state with clock := clock } = .val (value, { next with clock := clock }) := by
  simpa [run, setClockResult] using doApp_setClock op args state clock

/-- Failed primitive application is unaffected by clock replacement. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "do_app_change_clock_err"
  (fmap_as_finite_support := [refs])]
theorem doAppChangeClockErr {C F : Type} (op : ClosLang.Op) (args : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (error : ErrorResult BvlSem.Value)
    (clock : Nat) (run : doApp op args state = .err error) :
    doApp op args { state with clock := clock } = .err error := by
  simpa [run, setClockResult] using doApp_setClock op args state clock

end Flapjack.Compiler.Backend.BvlProps
