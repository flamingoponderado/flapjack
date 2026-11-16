module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control

@[expose] public section

/-! Cut-state interaction with stack, clock, and locals-size updates. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Cutting locals commutes with the three independent field updates. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_opt_with_const"]
theorem cutStateOpt_withConst {C F : Type} (names : Option NumSet) (state : State C F)
    (stack : List Stack) (clock : Nat) (localsSize : Option Nat) :
    cutStateOpt names { state with stack := stack } =
      (cutStateOpt names state).map (fun s => { s with stack := stack }) ∧
    cutStateOpt names { state with clock := clock } =
      (cutStateOpt names state).map (fun s => { s with clock := clock }) ∧
    cutStateOpt names { state with localsSize := localsSize } =
      (cutStateOpt names state).map (fun s => { s with localsSize := localsSize }) := by
  cases names with
  | none => simp [cutStateOpt]
  | some names =>
    simp only [cutStateOpt, cutState]
    cases found : cutEnv names state.locals <;> simp

/-- The narrow cut commutes with replacing the space limits. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_opt_with_lim"]
theorem cutStateOpt_withLim {C F : Type} (names : Option NumSet) (state : State C F)
    (limits : Limits) :
    cutStateOpt names { state with limits := limits } =
      (cutStateOpt names state).map (fun s => { s with limits := limits }) := by
  cases names with
  | none => simp [cutStateOpt]
  | some names =>
    simp only [cutStateOpt, cutState]
    cases found : cutEnv names state.locals <;> simp

/-- The narrow cut commutes with replacing the locals size, the stack and the
stack-frame sizes together. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_opt_with_sfs"]
theorem cutStateOpt_withFrameFields {C F : Type} (names : Option NumSet)
    (state : State C F) (lsz : Option Nat) (xs : List Stack) (sfs : Spt Nat) :
    cutStateOpt names { state with localsSize := lsz, stack := xs, stackFrameSizes := sfs } =
      (cutStateOpt names state).map fun next =>
        { next with localsSize := lsz, stack := xs, stackFrameSizes := sfs } := by
  cases names with
  | none => simp [cutStateOpt]
  | some names =>
    simp only [cutStateOpt, cutState]
    cases found : cutEnv names state.locals <;> simp

/-- The narrow cut leaves the stack untouched. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_opt_stack"]
theorem cutStateOpt_stack {C F : Type} (names : Option NumSet) (state next : State C F)
    (cut : cutStateOpt names state = some next) : next.stack = state.stack := by
  cases names with
  | none => simp [cutStateOpt] at cut; subst next; rfl
  | some names =>
    simp only [cutStateOpt, cutState] at cut
    cases found : cutEnv names state.locals with
    | none => simp [found] at cut
    | some env =>
      simp [found] at cut
      subst next
      rfl

end Flapjack.Compiler.Backend.DataProps
