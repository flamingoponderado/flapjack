import Flapjack.Compiler.Backend.Semantics.BviProps.Clock
import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyClock
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyClock

/-! Clock replacement for BVI primitive application. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Flapjack helper: replace the clock in a handled optional result. -/
def setClockAux {C F : Type} (clock : Nat) (result : Option (Option (Value × BviState C F))) :
    Option (Option (Value × BviState C F)) :=
  result.map fun inner => inner.map fun (value, state) => (value, { state with clock := clock })

/-- Flapjack helper: BVI-specific primitives commute with clock replacement. -/
theorem doAppAux_setClock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (clock : Nat) :
    doAppAux op args { state with clock := clock } = setClockAux clock (doAppAux op args state) := by
  unfold doAppAux setClockAux
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]
  all_goals try (cases hg : state.global <;> simp_all)
  all_goals try (rename_i ptr; cases hr : state.refs.lookup ptr <;> simp_all)
  all_goals try (rename_i value; cases value <;> simp_all)
  all_goals try (split <;> simp_all)
  all_goals try grind

/-- Flapjack helper: replace the clock in a successful BVI result. -/
def setClockResult {C F : Type} (clock : Nat) (result : Result (Value × BviState C F) ExnOrRet) :
    Result (Value × BviState C F) ExnOrRet :=
  match result with
  | .err error => .err error
  | .val (value, state) => .val (value, { state with clock := clock })

/-- Flapjack helper: installation commutes with clock replacement. -/
theorem doInstall_setClock {C F : Type} (args : List Value)
    (state : BviState C F) (clock : Nat) :
    doInstall (R := ExnOrRet) args { state with clock := clock } =
      setClockResult clock (doInstall args state) := by
  cases state
  unfold doInstall
  repeat' (split <;> try simp_all [setClockResult])

/-- Flapjack helper: copying the BVL fallback state commutes with clock
replacement on the BVI input. -/
theorem toBvl_setClock {C F : Type} (state : BviState C F) (clock : Nat) :
    toBvl { state with clock := clock } = { toBvl state with clock := clock } := by
  simp [toBvl]

/-- Flapjack helper: copying fallback results preserves the replaced clock. -/
theorem fromBvl_setClock {C F : Type} (source : BvlSem.State C F)
    (state : BviState C F) (clock : Nat) :
    fromBvl { source with clock := clock } { state with clock := clock } =
      { fromBvl source state with clock := clock } := by
  cases source
  cases state
  rfl

/-- Flapjack helper: the BVI-specific or BVL fallback dispatcher commutes
with clock replacement. -/
theorem doAppFallback_setClock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (clock : Nat) :
    doAppFallback op args { state with clock := clock } =
      setClockResult clock (doAppFallback op args state) := by
  unfold doAppFallback
  rw [doAppAux_setClock]
  cases aux : doAppAux op args state with
  | none => simp [setClockAux, setClockResult]
  | some inner =>
    cases inner with
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [setClockAux, setClockResult]
    | none =>
      simp only [setClockAux, Option.map, toBvl_setClock]
      rw [BvlProps.doApp_setClock]
      cases original : BvlSem.doApp op args (toBvl state) with
      | err error =>
        cases error <;> simp [BvlProps.setClockResult, setClockResult]
      | val pair =>
        obtain ⟨value, next⟩ := pair
        simp [BvlProps.setClockResult, setClockResult, fromBvl_setClock]

/-- Flapjack helper: the complete BVI dispatcher commutes with clock
replacement. This remains untagged until dispatcher correspondence review. -/
theorem doApp_setClock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (clock : Nat) :
    doApp op args { state with clock := clock } = setClockResult clock (doApp op args state) := by
  cases op with
  | install => exact doInstall_setClock args state clock
  | _ => simp only [doApp]; exact doAppFallback_setClock _ args state clock

/-- Flapjack helper: successful BVI primitive application commutes with
adding clock allowance. -/
theorem doApp_incClock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : BviState C F) (value : Value) (extra : Nat)
    (run : doApp op args state = .val (value, next)) :
    doApp op args (incClock extra state) = .val (value, incClock extra next) := by
  have sameClock := BviSem.doApp_clock op args state next value run
  simpa [incClock, run, setClockResult, sameClock] using
    doApp_setClock op args state (state.clock + extra)

/-- Flapjack helper: BVI primitive errors are unaffected by clock allowance. -/
theorem doApp_incClock_error {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (extra : Nat) (run : doApp op args state = .err error) :
    doApp op args (incClock extra state) = .err error := by
  simpa [incClock, run, setClockResult] using doApp_setClock op args state (state.clock + extra)

end Flapjack.Compiler.Backend.BviProps
