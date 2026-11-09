module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyClock
public import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateInduction
public import Lean.Elab.Tactic.Omega

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.FlatSem.Evaluate
import all Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact
@[expose] public section

/-! Clock preservation and clock clamping for flat evaluation and its
declaration projections. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL

/-- Clock bounds and FFI event prefixes used by the shared evaluator induction. -/
private def Progress {C F : Type} (state next : State C F) : Prop :=
  next.clock ≤ state.clock ∧ state.ffi.ioEvents <+: next.ffi.ioEvents
/-- Flapjack proof infrastructure: Progress is reflexive. -/
private theorem progressRefl {C F : Type} (state : State C F) : Progress state state :=
  ⟨Nat.le_refl _, List.prefix_refl _⟩
/-- Flapjack proof infrastructure: Clock bounds and event prefixes compose. -/
private theorem progressTrans {C F : Type} (first middle last : State C F)
    (h : Progress first middle) (h' : Progress middle last) : Progress first last :=
  ⟨Nat.le_trans h'.1 h.1, h.2.trans h'.2⟩
/-- Flapjack proof infrastructure: Clock clamping preserves the event prefix. -/
private theorem progressFix {C F α : Type} (state : State C F) (pair : State C F × α)
    (events : state.ffi.ioEvents <+: pair.1.ffi.ioEvents) : Progress state (fixClock state pair).1 :=
  ⟨fixClock_clock_le state pair, events⟩
/-- Flapjack proof infrastructure: Clock decrement preserves the event trace. -/
private theorem progressDec {C F : Type} (state : State C F) : Progress state (decClock state) := by
  exact ⟨by simp [decClock], List.prefix_refl _⟩
/-- Flapjack proof infrastructure: Primitive results preserve the shared progress invariant. -/
private theorem progressApply {C F : Type} (state : State C F) (op : FlatLang.Op) (values : List Value) :
    Progress state (applyResult state op values).1 := by
  cases run : doApp state op values with
  | none => simp [applyResult, run, Progress]
  | some pair =>
    obtain ⟨next, result⟩ := pair
    have stable := doApp_stableAndIo state next op values result run
    cases result <;> simp [applyResult, run, Progress, stable.1, stable.2.2]
/-- Flapjack proof infrastructure: Constructor evaluation inherits argument progress. -/
private theorem progressCon {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (constructor : Option (FlatLang.CtorId × FlatLang.TypeId))
    (args : List FlatLang.Exp) (ih : Progress state (evaluate env state args.reverse).1) :
    Progress state (evaluate env state [.con trace constructor args]).1 := by
  rw [evaluate]
  generalize h : evaluate env state args.reverse = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result <;> exact ih

/-- Flapjack proof infrastructure: Raise evaluation inherits operand progress. -/
private theorem progressRaise {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (ih : Progress state (evaluate env state [body]).1) :
    Progress state (evaluate env state [.raise trace body]).1 := by
  rw [evaluate]
  generalize h : evaluate env state [body] = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result <;> exact ih

/-- Flapjack proof infrastructure: Expression-list sequencing composes both steps. -/
private theorem progressList {C F : Type} (env : Environment Value) (state : State C F)
    (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (headIH : Progress state (evaluate env state [first]).1)
    (tailIH : ∀ next : State C F, next.clock ≤ state.clock →
      Progress next (evaluate env next (second :: rest)).1) :
    Progress state (evaluate env state (first :: second :: rest)).1 := by
  have head := progressFix state (evaluate env state [first]) headIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [first]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values =>
    have tail := progressTrans state next (evaluate env next (second :: rest)).1 head (tailIH next head.1)
    generalize tailRun : evaluate env next (second :: rest) = output at *
    obtain ⟨last, result⟩ := output
    cases result <;> exact tail

/-- Flapjack proof infrastructure: Declaration-list sequencing composes both steps. -/
private theorem progressDecs {C F : Type} (state : State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp)
    (headIH : Progress state (evaluate ⟨[]⟩ state [declaration]).1)
    (tailIH : ∀ next : State C F, next.clock ≤ state.clock → Progress next (evaluateDecs next rest).1) :
    Progress state (evaluateDecs state (declaration :: rest)).1 := by
  have head := progressFix state (evaluate ⟨[]⟩ state [declaration]) headIH.2
  rw [evaluateDecs]
  generalize h : fixClock state (evaluate ⟨[]⟩ state [declaration]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values =>
    have tail := progressTrans state next (evaluateDecs next rest).1 head (tailIH next head.1)
    split <;> assumption

/-- Flapjack proof infrastructure: Recursive bindings inherit body progress. -/
private theorem progressLetrec {C F : Type} (env : Environment Value) (state : State C F)
    (name : Flapjack.AstHOL.VarN) (funs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
    (body : FlatLang.Exp)
    (ih : Progress state (evaluate { env with v := buildRecEnv funs env env.v } state [body]).1) :
    Progress state (evaluate env state [.letrec name funs body]).1 := by
  rw [evaluate]
  split <;> simp_all [progressRefl]

/-- Flapjack proof infrastructure: Let evaluation composes its operand and body. -/
private theorem progressLet {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (name : Option Flapjack.AstHOL.VarN) (first body : FlatLang.Exp)
    (headIH : Progress state (evaluate env state [first]).1)
    (bodyIH : ∀ (newEnv : Environment Value) (next : State C F), next.clock ≤ state.clock →
      Progress next (evaluate newEnv next [body]).1) :
    Progress state (evaluate env state [.let_ trace name first body]).1 := by
  have head := progressFix state (evaluate env state [first]) headIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [first]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values => exact progressTrans state next _ head (bodyIH _ next head.1)

/-- Flapjack proof infrastructure: Conditional evaluation composes its condition and selected branch. -/
private theorem progressIf {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (cond yes no : FlatLang.Exp)
    (headIH : Progress state (evaluate env state [cond]).1)
    (yesIH : ∀ next : State C F, next.clock ≤ state.clock → Progress next (evaluate env next [yes]).1)
    (noIH : ∀ next : State C F, next.clock ≤ state.clock → Progress next (evaluate env next [no]).1) :
    Progress state (evaluate env state [.if_ trace cond yes no]).1 := by
  have head := progressFix state (evaluate env state [cond]) headIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [cond]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values =>
    dsimp only
    split
    · exact head
    · rename_i body selected
      have choice := doIf_either_or _ yes no body selected
      rcases choice with rfl | rfl
      · exact progressTrans state next _ head (yesIH next head.1)
      · exact progressTrans state next _ head (noIH next head.1)

/-- Flapjack proof infrastructure: Pattern matching composes its scrutinee and selected branch. -/
private theorem progressMatch {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (headIH : Progress state (evaluate env state [body]).1)
    (rowIH : ∀ (next : State C F) (bindings : List (Flapjack.AstHOL.VarN × Value)) (branch : FlatLang.Exp),
      next.clock ≤ state.clock → expWeight branch < rowsWeight rows →
      Progress next (evaluate { env with v := bindings ++ env.v } next [branch]).1) :
    Progress state (evaluate env state [.mat trace body rows]).1 := by
  have head := progressFix state (evaluate env state [body]) headIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [body]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values =>
    dsimp only
    split
    · exact head
    · rename_i bindings branch selected
      have weight := selectRow_weight rows next _ bindExnV bindings branch selected
      exact progressTrans state next _ head (rowIH next bindings branch head.1 weight)

/-- Flapjack proof infrastructure: An exception handler composes its body and selected branch. -/
private theorem progressHandle {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (headIH : Progress state (evaluate env state [body]).1)
    (rowIH : ∀ (next : State C F) (bindings : List (Flapjack.AstHOL.VarN × Value)) (branch : FlatLang.Exp),
      next.clock ≤ state.clock → expWeight branch < rowsWeight rows →
      Progress next (evaluate { env with v := bindings ++ env.v } next [branch]).1) :
    Progress state (evaluate env state [.handle trace body rows]).1 := by
  have head := progressFix state (evaluate env state [body]) headIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state [body]) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | val values => exact head
  | err error =>
    cases error with
    | abort error => exact head
    | raise value =>
      dsimp only
      split
      · exact head
      · rename_i bindings branch selected
        have weight := selectRow_weight rows next value value bindings branch selected
        exact progressTrans state next _ head (rowIH next bindings branch head.1 weight)

/-- Flapjack proof infrastructure: Flat primitive applications compose argument and primitive progress. -/
private theorem progressFlatApp {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (flatOp : ∀ source, op ≠ .src source)
    (argsIH : Progress state (evaluate env state args.reverse).1) :
    Progress state (evaluate env state [.app trace op args]).1 := by
  have head := progressFix state (evaluate env state args.reverse) argsIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values =>
    have tail := progressTrans state next (applyResult next op values.reverse).1 head (progressApply next op values.reverse)
    cases op with
    | src source => exact (flatOp source rfl).elim
    | globalVarAlloc n => exact tail
    | globalVarInit n => exact tail
    | globalVarLookup n => exact tail
    | tagLenEq tag length => exact tail
    | lenEq length => exact tail
    | el n => exact tail
    | id => exact tail

/-- Flapjack proof infrastructure: Ordinary source primitives compose argument and primitive progress. -/
private theorem progressSimpleSourceApp {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (op : Flapjack.AstHOL.Op) (args : List FlatLang.Exp)
    (notCall : op ≠ .opapp) (notEval : op ≠ .eval) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : Progress state (evaluate env state args.reverse).1) :
    Progress state (evaluate env state [.app trace (.src op) args]).1 := by
  have head := progressFix state (evaluate env state args.reverse) argsIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values =>
    have tail := progressTrans state next (applyResult next (.src op) values.reverse).1 head
      (progressApply next (.src op) values.reverse)
    cases op <;> simp_all

/-- Flapjack proof infrastructure: Function application composes argument, clock decrement and body progress. -/
private theorem progressCall {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsIH : Progress state (evaluate env state args.reverse).1)
    (bodyIH : ∀ (newEnv : Environment Value) (newState : State C F) (body : FlatLang.Exp),
      newState.clock < state.clock → Progress newState (evaluate newEnv newState [body]).1) :
    Progress state (evaluate env state [.app trace (.src .opapp) args]).1 := by
  have head := progressFix state (evaluate env state args.reverse) argsIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values =>
    cases call : doOpApp values.reverse with
    | none => simpa [call] using head
    | some pair =>
      obtain ⟨newEnv, body⟩ := pair
      by_cases zero : next.clock = 0
      · simpa [call, zero] using head
      · have clockBound := head.1
        have decrease : (decClock next).clock < state.clock := by simp [decClock]; omega
        have recurse := bodyIH newEnv (decClock next) body decrease
        have overall := progressTrans state next _ head (progressTrans next (decClock next) _ (progressDec next) recurse)
        simpa [call, zero] using overall

/-- Flapjack proof infrastructure: Dynamic evaluation composes argument, clock decrement and declaration progress. -/
private theorem progressEval {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsIH : Progress state (evaluate env state args.reverse).1)
    (decsIH : ∀ (newState : State C F) (decs : List FlatLang.Exp),
      newState.clock < state.clock → Progress newState (evaluateDecs newState decs).1) :
    Progress state (evaluate env state [.app trace (.src .eval) args]).1 := by
  have head := progressFix state (evaluate env state args.reverse) argsIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values =>
    cases decoded : doEval values.reverse next.evalConfig with
    | none => simpa [decoded] using head
    | some payload =>
      obtain ⟨decs, config, returnValue⟩ := payload
      by_cases zero : next.clock = 0
      · simpa [decoded, zero, Progress] using head
      · have clockBound := head.1
        have decrease : (decClock { next with evalConfig := config }).clock < state.clock := by
          simp only [decClock]
          omega
        have updated : Progress next { next with evalConfig := config } := progressRefl next
        have recursive := decsIH (decClock { next with evalConfig := config }) decs decrease
        have overall := progressTrans state next _ head
          (progressTrans next { next with evalConfig := config } _ updated
            (progressTrans _ _ _ (progressDec { next with evalConfig := config }) recursive))
        cases result : (evaluateDecs (decClock { next with evalConfig := config }) decs).2 <;>
          simpa [decoded, zero, result] using overall

/-- Flapjack proof infrastructure: Thunk forcing composes argument and body progress. -/
private theorem progressForce {C F : Type} (env : Environment Value) (state : State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsIH : Progress state (evaluate env state args.reverse).1)
    (bodyIH : ∀ (next : State C F) (value : Value), next.clock ≤ state.clock →
      Progress next (evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ next
        [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))]).1) :
    Progress state (evaluate env state [.app trace (.src (.thunkOp .forceThunk)) args]).1 := by
  have head := progressFix state (evaluate env state args.reverse) argsIH.2
  rw [evaluate]
  generalize h : fixClock state (evaluate env state args.reverse) = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  change Progress state next at head
  cases result with
  | err error => exact head
  | val values =>
    cases thunk : destThunk values next.refs with
    | badRef => simpa [thunk] using head
    | notThunk => simpa [thunk] using head
    | isThunk mode value =>
      cases mode with
      | evaluated => simpa [thunk] using head
      | notEvaluated =>
        have recursive := bodyIH next value head.1
        have overall := progressTrans state next _ head recursive
        generalize bodyRun : evaluate ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ next
          [appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))] = output at *
        obtain ⟨last, output⟩ := output
        change Progress state last at overall
        cases output with
        | err error => simpa [thunk, bodyRun] using overall
        | val newValues =>
          cases updated : updateThunk values last.refs newValues with
          | none => simpa [thunk, bodyRun, updated] using overall
          | some refs => simpa [thunk, bodyRun, updated, Progress] using overall

/-- Flapjack proof infrastructure: Mutual clock-and-weight induction for expressions and declaration lists. -/
private theorem evaluateProgressMutual {C F : Type} :
    (∀ (env : Environment Value) (state : State C F) (expressions : List FlatLang.Exp),
      Progress state (evaluate env state expressions).1) ∧
    (∀ (state : State C F) (declarations : List FlatLang.Exp),
      Progress state (evaluateDecs state declarations).1) := by
  apply flatEvaluateMeasureRec
  · intro env state expressions exprIH smallerE _ smallerD
    let clock := state.clock
    let weight := expsWeight expressions
    have stateClock : state.clock = clock := rfl
    have measure : expsWeight expressions = weight := rfl
    have smallerExpr : ∀ (env : Environment Value) (state : State C F) (body : FlatLang.Exp),
        state.clock < clock → Progress state (evaluate env state [body]).1 := by
      intro env state body h
      exact smallerE env state [body] h
    have smallerDecs : ∀ (state : State C F) (decs : List FlatLang.Exp),
        state.clock < clock → Progress state (evaluateDecs state decs).1 := by
      intro state decs h
      exact smallerD state decs h
    cases expressions with
    | nil => simp [evaluate, progressRefl]
    | cons first rest =>
      cases rest with
      | cons second tail =>
        apply progressList
        · apply exprIH env state [first] (by omega)
          simp only [expsWeight] at measure ⊢
          have := expWeight_pos second
          omega
        · intro next nextBound
          apply exprIH env next (second :: tail) (by omega)
          simp only [expsWeight] at measure ⊢
          omega
      | nil =>
        cases first with
        | lit t l => simp [evaluate, progressRefl]
        | varLocal t n => simp [evaluate]; split <;> simp [progressRefl]
        | fn t n b => simp [evaluate, progressRefl]
        | raise t body =>
          apply progressRaise
          apply exprIH env state [body] (by omega)
          simp only [expsWeight, expWeight] at measure ⊢
          omega
        | con t constructor args =>
          apply progressCon
          apply exprIH env state args.reverse (by omega)
          rw [expsWeight_reverse]
          simp only [expsWeight, expWeight] at measure
          omega
        | letrec name funs body =>
          apply progressLetrec
          apply exprIH _ state [body] (by omega)
          simp only [expsWeight, expWeight] at measure ⊢
          omega
        | let_ t name first body =>
          apply progressLet
          · apply exprIH env state [first] (by omega)
            simp only [expsWeight, expWeight] at measure ⊢
            omega
          · intro newEnv next nextBound
            apply exprIH newEnv next [body] (by omega)
            simp only [expsWeight, expWeight] at measure ⊢
            omega
        | if_ t cond yes no =>
          apply progressIf
          · apply exprIH env state [cond] (by omega)
            simp only [expsWeight, expWeight] at measure ⊢
            omega
          · intro next nextBound
            apply exprIH env next [yes] (by omega)
            simp only [expsWeight, expWeight] at measure ⊢
            omega
          · intro next nextBound
            apply exprIH env next [no] (by omega)
            simp only [expsWeight, expWeight] at measure ⊢
            omega
        | mat t body rows =>
          apply progressMatch
          · apply exprIH env state [body] (by omega)
            simp only [expsWeight, expWeight] at measure ⊢
            omega
          · intro next bindings branch nextBound branchWeight
            apply exprIH _ next [branch] (by omega)
            simp only [expsWeight, expWeight] at measure ⊢
            omega
        | handle t body rows =>
          apply progressHandle
          · apply exprIH env state [body] (by omega)
            simp only [expsWeight, expWeight] at measure ⊢
            omega
          · intro next bindings branch nextBound branchWeight
            apply exprIH _ next [branch] (by omega)
            simp only [expsWeight, expWeight] at measure ⊢
            omega
        | app t op args =>
          have argsIH : Progress state (evaluate env state args.reverse).1 := by
            apply exprIH env state args.reverse (by omega)
            rw [expsWeight_reverse]
            simp only [expsWeight, expWeight] at measure
            omega
          cases op with
          | src source =>
            by_cases call : source = .opapp
            · subst source
              apply progressCall env state t args argsIH
              intro newEnv next body nextLt
              exact smallerExpr newEnv next body (by omega)
            · by_cases eval : source = .eval
              · subst source
                apply progressEval env state t args argsIH
                intro next decs nextLt
                exact smallerDecs next decs (by omega)
              · by_cases force : source = .thunkOp .forceThunk
                · subst source
                  apply progressForce env state t args argsIH
                  intro next value nextBound
                  apply exprIH _ next _ (by omega)
                  have forceWeight := appUnit_force_weight t args
                  simp only [expsWeight, expWeight] at measure ⊢
                  simp only [expWeight] at forceWeight
                  omega
                · exact progressSimpleSourceApp env state t source args call eval force argsIH
          | globalVarAlloc n => exact progressFlatApp env state t _ args (by simp) argsIH
          | globalVarInit n => exact progressFlatApp env state t _ args (by simp) argsIH
          | globalVarLookup n => exact progressFlatApp env state t _ args (by simp) argsIH
          | tagLenEq n l => exact progressFlatApp env state t _ args (by simp) argsIH
          | lenEq l => exact progressFlatApp env state t _ args (by simp) argsIH
          | el n => exact progressFlatApp env state t _ args (by simp) argsIH
          | id => exact progressFlatApp env state t _ args (by simp) argsIH
  · intro state declarations exprIH _ decIH _
    let clock := state.clock
    let weight := expsWeight declarations + 1
    have stateClock : state.clock = clock := rfl
    have measure : expsWeight declarations + 1 = weight := rfl
    cases declarations with
    | nil => simp [evaluateDecs, progressRefl]
    | cons declaration rest =>
      apply progressDecs
      · apply exprIH ⟨[]⟩ state [declaration] (by omega)
        simp only [expsWeight] at measure ⊢
        omega
      · intro next nextBound
        apply decIH next rest (by omega)
        simp only [expsWeight] at measure
        have := expWeight_pos declaration
        omega


/-- Shared evaluator invariant: evaluation cannot increase the clock and
extends its FFI events. This Flapjack infrastructure supports the separate HOL
clock-preservation and event-prefix results. -/
theorem evaluate_clockAndEvents_mutual {C F : Type} :
    (∀ (env : Environment Value) (state : State C F) (expressions : List FlatLang.Exp),
      (evaluate env state expressions).1.clock ≤ state.clock ∧
        state.ffi.ioEvents <+: (evaluate env state expressions).1.ffi.ioEvents) ∧
    (∀ (state : State C F) (declarations : List FlatLang.Exp),
      (evaluateDecs state declarations).1.clock ≤ state.clock ∧
        state.ffi.ioEvents <+: (evaluateDecs state declarations).1.ffi.ioEvents) :=
  evaluateProgressMutual

/-- Clock preservation for expressions and declaration lists, a projection of
the shared evaluator invariant. This helper has no separate HOL declaration. -/
theorem evaluate_clock_mutual {C F : Type} :
    (∀ (env : Environment Value) (state : State C F) (expressions : List FlatLang.Exp),
      (evaluate env state expressions).1.clock ≤ state.clock) ∧
    (∀ (state : State C F) (declarations : List FlatLang.Exp),
      (evaluateDecs state declarations).1.clock ≤ state.clock) := by
  constructor
  · intro env state expressions
    exact (evaluate_clockAndEvents_mutual.1 env state expressions).1
  · intro state declarations
    exact (evaluate_clockAndEvents_mutual.2 state declarations).1

/-- The single-declaration evaluation projection also preserves the clock. -/
theorem evaluateDec_clock {C F : Type} (state : State C F) (declaration : FlatLang.Exp) :
    (evaluateDec state declaration).1.clock ≤ state.clock := by
  have bound := evaluate_clock_mutual.1 ⟨[]⟩ state [declaration]
  unfold evaluateDec
  generalize h : evaluate ⟨[]⟩ state [declaration] = evaluated at *
  obtain ⟨next, result⟩ := evaluated
  cases result with
  | err error => exact bound
  | val values => dsimp only; split <;> exact bound

/-- Expression, single-declaration and declaration-list evaluation do not
increase the clock. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "evaluate_clock"]
theorem evaluate_clock_spec {C F : Type} :
    (∀ (env : Environment Value) (state : State C F) (expressions : List FlatLang.Exp)
      (result : Result (List Value) Value) (next : State C F),
      evaluate env state expressions = (next, result) → next.clock ≤ state.clock) ∧
    (∀ (state : State C F) (declaration : FlatLang.Exp) (result : Option (ErrorResult Value))
      (next : State C F), evaluateDec state declaration = (next, result) → next.clock ≤ state.clock) ∧
    (∀ (state : State C F) (declarations : List FlatLang.Exp) (result : Option (ErrorResult Value))
      (next : State C F), evaluateDecs state declarations = (next, result) → next.clock ≤ state.clock) := by
  refine ⟨?_, ?_, ?_⟩
  · intro env state expressions result next run
    have bound := evaluate_clock_mutual.1 env state expressions
    simpa [run] using bound
  · intro state declaration result next run
    have bound := evaluateDec_clock state declaration
    simpa [run] using bound
  · intro state declarations result next run
    have bound := evaluate_clock_mutual.2 state declarations
    simpa [run] using bound

/-- Clock clamping is redundant after any expression, declaration, or
declaration-list evaluation in the current clocked evaluator. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "fix_clock_evaluate"]
theorem fixClock_evaluations {C F : Type} (env : Environment Value) (state : State C F)
    (expressions : List FlatLang.Exp) (declaration : FlatLang.Exp) (declarations : List FlatLang.Exp) :
    fixClock state (evaluate env state expressions) = evaluate env state expressions ∧
    fixClock state (evaluateDec state declaration) = evaluateDec state declaration ∧
    fixClock state (evaluateDecs state declarations) = evaluateDecs state declarations := by
  constructor
  · have bound := evaluate_clock_mutual.1 env state expressions
    cases run : evaluate env state expressions with
    | mk next result =>
      have nextBound : next.clock ≤ state.clock := by simpa [run] using bound
      simp [fixClock, Nat.min_eq_right nextBound]

  constructor
  · have bound := evaluateDec_clock state declaration
    cases run : evaluateDec state declaration with
    | mk next result =>
      have nextBound : next.clock ≤ state.clock := by simpa [run] using bound
      simp [fixClock, Nat.min_eq_right nextBound]
  · have bound := evaluate_clock_mutual.2 state declarations
    cases run : evaluateDecs state declarations with
    | mk next result =>
      have nextBound : next.clock ≤ state.clock := by simpa [run] using bound
      simp [fixClock, Nat.min_eq_right nextBound]

/-- The declaration-list evaluator sequences the single-declaration
projection, stopping at the first error. -/
theorem evaluateDecs_cons {C F : Type} (state : State C F)
    (declaration : FlatLang.Exp) (rest : List FlatLang.Exp) :
    evaluateDecs state (declaration :: rest) =
      match evaluateDec state declaration with
      | (next, none) => evaluateDecs next rest
      | (next, some error) => (next, some error) := by
  rw [evaluateDecs]
  have unclamped := (fixClock_evaluations ⟨[]⟩ state [declaration] declaration rest).1
  rw [unclamped]
  unfold evaluateDec
  generalize h : evaluate ⟨[]⟩ state [declaration] = evaluated
  obtain ⟨next, result⟩ := evaluated
  cases result with
  | err error => rfl
  | val values => dsimp only; split <;> rfl

end Flapjack.Compiler.Backend.FlatSem
