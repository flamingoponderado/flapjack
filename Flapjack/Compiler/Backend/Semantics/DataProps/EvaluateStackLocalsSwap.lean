module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateResourceSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyAuxFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.InitialStateLaws
public import Flapjack.Compiler.Backend.Semantics.DataProps.Jump
public import Flapjack.Misc.ClockWeightInduction

@[expose] public section

/-!
# Stack and locals-size replacement under data evaluation

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:929`
`evaluate_stack_and_locals_swap`, together with the consequences
`evaluate_stack_swap` (`:1421`), `evaluate_stack` (`:1466`) and
`evaluate_NONE_jump_exc` (`:1480`).

The step lemmas below are the induction's cases. Those that are not yet
covered by the assembled theorem are Flapjack infrastructure toward the port of
`evaluate_stack_and_locals_swap`; they carry no `@[hol]` tag of their own.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.DataSem

/-- The stack-and-locals replacement property for one program and state: the
    evaluation outcome is preserved when the stack is replaced by a list of the
    same length and the locals size is replaced, with only the resource
    observations free. -/
private def StackLocalsSwapAt {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  ∀ (res : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F),
    evaluate program state = (res, next) →
    match res with
    | some (.err (.abort .typeError)) => True
    | some (.err (.abort a)) =>
        next.stack = [] ∧
          ∀ (xs : List Stack) (lsz : Option Nat), state.stack.length = xs.length →
            ∃ lss sfs smx phl, evaluate program { state with stack := xs, localsSize := lsz } =
              (some (.err (.abort a)),
                { next with
                  localsSize := lss
                  safeForSpace := sfs
                  stackMax := smx
                  peakHeapLength := phl })
    | some (.err (.raise t)) =>
        ∃ s2, jumpExc state = some s2 ∧ s2.locals = next.locals ∧ s2.stack = next.stack ∧
          s2.handler = next.handler ∧
          ∀ (xs : List Stack) (s7 : State C F) (lsz : Option Nat),
            jumpExc { state with stack := xs, localsSize := lsz } = some s7 →
            state.stack.length = xs.length →
            ∃ lss sfs smx phl, evaluate program { state with stack := xs, localsSize := lsz } =
              (some (.err (.raise t)),
                { next with
                  stack := s7.stack
                  handler := s7.handler
                  locals := s7.locals
                  localsSize := lss
                  safeForSpace := sfs
                  stackMax := smx
                  peakHeapLength := phl })
    | _ =>
        next.stack = state.stack ∧ next.handler = state.handler ∧
          ∀ (xs : List Stack) (lsz : Option Nat), state.stack.length = xs.length →
            ∃ lss sfs smx phl, evaluate program { state with stack := xs, localsSize := lsz } =
              (res, { next with
                localsSize := lss
                stack := xs
                safeForSpace := sfs
                stackMax := smx
                peakHeapLength := phl })

/-- The `Skip` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_skip {C F : Type} (state : State C F) :
    StackLocalsSwapAt (.skip : DataLang.Prog) state := by
  intro res next run
  simp only [evaluate, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨rfl, rfl, ?_⟩
  intro xs lsz len
  exact ⟨lsz, state.safeForSpace, state.stackMax, state.peakHeapLength, by simp [evaluate]⟩

/-- The `Move` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_move {C F : Type} (dest src : Nat) (state : State C F) :
    StackLocalsSwapAt (.move dest src) state := by
  intro res next run
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some value =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨rfl, rfl, ?_⟩
    intro xs lsz len
    exact ⟨lsz, state.safeForSpace, state.stackMax, state.peakHeapLength,
      by simp [evaluate, read, setVar]⟩

/-- The `Tick` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_tick {C F : Type} (state : State C F) :
    StackLocalsSwapAt (.tick : DataLang.Prog) state := by
  intro res next run
  by_cases zero : state.clock = 0
  · simp only [evaluate, zero, timeoutError] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨?_, ?_⟩
    · simp [flushState]
    · intro xs lsz len
      exact ⟨some 0, state.safeForSpace, state.stackMax, state.peakHeapLength,
        by simp [evaluate, zero, timeoutError, flushState]⟩
  · simp only [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨rfl, rfl, ?_⟩
    intro xs lsz len
    exact ⟨lsz, state.safeForSpace, state.stackMax, state.peakHeapLength,
      by simp [evaluate, zero, decClock]⟩

/-- The `MakeSpace` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_makeSpace {C F : Type} (amount : Nat) (names : NumSet)
    (state : State C F) : StackLocalsSwapAt (.makeSpace amount names) state := by
  intro res next run
  cases cut : cutEnv names state.locals with
  | none =>
    simp only [evaluate, cut, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some env =>
    simp only [evaluate, cut, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨rfl, rfl, ?_⟩
    intro xs lsz len
    let target := addSpace { state with locals := env, stack := xs, localsSize := lsz } amount
    refine ⟨lsz, target.safeForSpace, state.stackMax, target.peakHeapLength, ?_⟩
    simp only [evaluate, cut]
    rfl

/-- The `Raise` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_raise {C F : Type} (name : Nat) (state : State C F) :
    StackLocalsSwapAt (.raise name) state := by
  intro res next run
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some value =>
    cases jump : jumpExc state with
    | none =>
      simp only [evaluate, read, jump, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some jumped =>
      simp only [evaluate, read, jump, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨jumped, rfl, rfl, rfl, rfl, ?_⟩
      intro xs s7 lsz jumpedRun len
      refine ⟨s7.localsSize, s7.safeForSpace, s7.stackMax, s7.peakHeapLength, ?_⟩
      obtain ⟨_, n1, e1, ls1, xs1, _, jumpedEq⟩ := jumpExcImp state jumped jump
      obtain ⟨_, n2, e2, ls2, xs2, _, s7Eq⟩ := jumpExcImp _ s7 jumpedRun
      subst s7
      rw [jumpedEq]
      simp [evaluate, read, jumpedRun]

/-- The `Return` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_return {C F : Type} (names : List Nat) (state : State C F) :
    StackLocalsSwapAt (.return names) state := by
  intro res next run
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some values =>
    have hres : res = some (.val values) := by
      have h := congrArg Prod.fst run
      simpa [evaluate, DataSem.getVars, read] using h.symm
    have hnext : next = flushState false state := by
      have h := congrArg Prod.snd run
      simpa [evaluate, DataSem.getVars, read] using h.symm
    rw [hres, hnext]
    refine ⟨rfl, rfl, ?_⟩
    intro xs lsz len
    exact ⟨some 0, state.safeForSpace, state.stackMax, state.peakHeapLength,
      by simp [evaluate, read, flushState]⟩

/-- The `If` case. Flapjack infrastructure toward the port of HOL
    `evaluate_stack_and_locals_swap`; no separate HOL original. -/
private theorem stackLocalsSwap_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (state : State C F) (yesIH : StackLocalsSwapAt yes state) (noIH : StackLocalsSwapAt no state) :
    StackLocalsSwapAt (.ifThenElse name yes no) state := by
  intro res next run
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some value =>
    by_cases yesValue : isBool true value
    · have branch : evaluate yes state = (res, next) := by
        simpa [evaluate, read, yesValue] using run
      have := yesIH res next branch
      simpa [evaluate, read, yesValue] using this
    · by_cases noValue : isBool false value
      · have branch : evaluate no state = (res, next) := by
          simpa [evaluate, read, yesValue, noValue] using run
        have := noIH res next branch
        simpa [evaluate, read, yesValue, noValue] using this
      · simp only [evaluate, read, yesValue, noValue, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial

end Flapjack.Compiler.Backend.DataProps
