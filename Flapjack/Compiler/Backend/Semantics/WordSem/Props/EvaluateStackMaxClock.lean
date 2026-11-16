module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PopEnvConst
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws

@[expose] public section

/-!
# wordProps `evaluate_stack_max_only_grows`

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:4479-4487`.
HOL proves it by `recInduct evaluate_ind`: the run under the extra clock follows
the same path as the original run, so the reached `stack_max` only grows.  Here
the same induction is a recursion on HOL's termination measure (as for
`evaluate_stack_max_le`), with the motive `∀ ck`.  The non-recursive clauses use
`evaluate_withClock_const`; each recursive clause compares the two runs through
`evaluate_add_clock`, `evaluate_stack_max_le` and `option_le_trans`.

Inherited assumption: `evaluate`'s `Inst` clause calls the tagged `inst`, which
carries `(reals_as_rational_cuts)`; the theorem here records that inherited
`docs/SOUNDNESS.md` item 8 assumption in the theorem map.
-/

namespace Flapjack

namespace WordSemEvaluateStackMaxClockSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateStackMaxClockSupport

namespace WordSemStateFiniteExact

open Flapjack.Compiler.Backend.BackendProps

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the clock clamp of `evaluate` keeps the stack
    maximum, so it never affects the comparison of the two runs.  It has no
    separate HOL original (HOL unfolds `fix_clock` in place). -/
theorem fixClock_stackMax {β : Type} (old : WordSemStateFiniteExact width C F)
    (step : β × WordSemStateFiniteExact width C F) :
    (fixClock old step).2.stackMax = step.2.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the clock clamp commutes with adding a clock
    allowance.  It has no separate HOL original. -/
theorem fixClock_addClock {β : Type} (s : WordSemStateFiniteExact width C F)
    (step : β × WordSemStateFiniteExact width C F) (ck : Nat) :
    fixClock { s with clock := s.clock + ck }
        ⟨step.1, { step.2 with clock := step.2.clock + ck }⟩ =
      ⟨step.1, { (fixClock s step).2 with clock := (fixClock s step).2.clock + ck }⟩ := by
  simp only [fixClock]
  by_cases h : s.clock < step.2.clock
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `dec_clock` keeps the stack maximum. -/
theorem decClock_stackMax (state : WordSemStateFiniteExact width C F) :
    (decClock state).stackMax = state.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `flush_state` keeps the stack maximum. -/
theorem flushState_stackMax (b : Bool) (state : WordSemStateFiniteExact width C F) :
    (flushState b state).stackMax = state.stackMax := by
  cases b <;> rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `inc_clock` keeps the stack maximum. -/
theorem incClock_stackMax (n : Nat) (state : WordSemStateFiniteExact width C F) :
    (incClock n state).stackMax = state.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `set_var` keeps the stack maximum. -/
theorem setVar_stackMax (name : Nat) (value : WordLocW width)
    (state : WordSemStateFiniteExact width C F) :
    (setVar name value state).stackMax = state.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `set_vars` keeps the stack maximum. -/
theorem setVars_stackMax (names : List Nat) (values : List (WordLocW width))
    (state : WordSemStateFiniteExact width C F) :
    (setVars names values state).stackMax = state.stackMax := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): the stack maximum of `call_env`, as used by
    the frame the call records. -/
theorem callEnv_stackMax (args : List (WordLocW width)) (size : Option Nat)
    (state : WordSemStateFiniteExact width C F) :
    (callEnv args size state).stackMax =
      wordSemOptionMax state.stackMax
        (wordSemOptionAdd (wordSemStackSize state.stack) size) := rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `pop_env` keeps the stack maximum (HOL reads
    it from `pop_env_const`). -/
theorem popEnv_stackMax (state next : WordSemStateFiniteExact width C F)
    (h : popEnv state = some next) : next.stackMax = state.stackMax :=
  (popEnvConst state next h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): `cut_state` keeps the stack maximum. -/
theorem cutState_stackMax (names : WordLangCutsetsHOL)
    (state next : WordSemStateFiniteExact width C F)
    (h : cutState names state = some next) : next.stackMax = state.stackMax := by
  unfold cutState at h
  split at h
  · cases h
  · cases h
    rfl

/-- Flapjack infrastructure toward HOL `evaluate_stack_max_only_grows`
    (`wordPropsScript.sml:4479`): a statement that neither reads the clock nor
    recurses reaches the same stack maximum under any clock, exactly as HOL's
    `evaluate_clock_with_const` clause gives it. -/
theorem stackMax_const (s : WordSemStateFiniteExact width C F)
    (p : WordLangProgHOL (BitVec width)) (hp : wordProgClockConst p = true) (ck : Nat) :
    optionLe (evaluate p s).2.stackMax
      (evaluate p { s with clock := s.clock + ck }).2.stackMax := by
  simp only [evaluate_withClock_const s (s.clock + ck) p hp]
  exact optionLe_refl _

end Helpers

end WordSemStateFiniteExact

end Flapjack
