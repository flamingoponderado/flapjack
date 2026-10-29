import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.FlatToClos.Proofs.SmartCons
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Recursive
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateLength
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
import Mathlib.Data.List.Forall2

/-! Initial cases of the proof-side flat-to-closure evaluator simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Relate expression results by relating returned lists and raised values,
while preserving aborts exactly. This proof-side relation and its semantic
carriers await correspondence review. -/
inductive EvalResultRel : Result (List FlatSem.Value) FlatSem.Value →
    Result (List ClosSem.Value) ClosSem.Value → Prop where
  | value {source target} (related : List.Forall₂ ValueRel source target) :
      EvalResultRel (.val source) (.val target)
  | raise {source target} (related : ValueRel source target) :
      EvalResultRel (.err (.raise source)) (.err (.raise target))
  | abort (error : Abort) : EvalResultRel (.err (.abort error)) (.err (.abort error))

/-- A flat Boolean accepted by `doIf` selects the same closure branch. -/
theorem doIf_related (source : FlatSem.Value) (target : ClosSem.Value) (branch : Bool)
    (related : ValueRel source target) (selected : FlatSem.doIf source true false = some branch) :
    ClosSem.asBool target = some branch := by
  cases related <;> simp [FlatSem.doIf] at selected
  case con values =>
    cases values with
    | nil =>
      rename_i tag typeId
      cases typeId with
      | none => simp at selected
      | some typeId =>
        simp [BackendCommon.trueTag, BackendCommon.falseTag] at selected
        split_ifs at selected <;> simp_all [ClosSem.asBool]
        split_ifs at selected <;> simp_all
    | cons _ _ => simp at selected

/-- Choosing expressions factors through the Boolean observation. -/
theorem doIf_asBool (value : FlatSem.Value) (yes no : FlatLang.Exp) :
    FlatSem.doIf value yes no = (FlatSem.doIf value true false).map (fun b => if b then yes else no) := by
  cases value <;> simp [FlatSem.doIf]
  case conv stamp fields =>
    cases stamp with
    | none => rfl
    | some pair =>
      obtain ⟨tag, typeId⟩ := pair
      cases typeId <;> cases fields <;> simp
      all_goals split_ifs <;> rfl

/-- Evaluation of a flat expression list and its translation preserves the
proof-side state and result relations. -/
def EvalSim {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F) (expressions : List FlatLang.Exp) : Prop :=
  let sourceResult := FlatSem.evaluate env source expressions
  let targetResult := ClosSem.evaluate (compile names expressions) values target
  StateRel sourceResult.1 targetResult.2 ∧ EvalResultRel sourceResult.2 targetResult.1

/-- Compilation preserves the evaluation order of reversed argument lists. -/
theorem compileExps_reverse (names : List (Option MlString)) (expressions : List FlatLang.Exp) :
    compileExps names expressions.reverse = (compileExps names expressions).reverse := by
  have mapEq : ∀ xs : List FlatLang.Exp, compileExps names xs = xs.map (compileExp names) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons head tail ih => simp [compileExps, ih]
  simp [mapEq]

/-- The empty expression list preserves the related state and returns empty
related lists. -/
theorem evaluate_nil {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (states : StateRel source target) : EvalSim env names values source target [] := by
  simpa [EvalSim, compile, compileExps, FlatSem.evaluate, ClosSem.evaluate] using
    And.intro states (EvalResultRel.value .nil)

/-- A successful flat local lookup reads the related closure environment at
the de Bruijn index chosen by compilation. -/
theorem evaluate_var {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (name : MlString) (value : FlatSem.Value)
    (states : StateRel source target) (environments : EnvRel env names values)
    (found : env.v.lookup name = some value) :
    EvalSim env names values source target [.varLocal trace name] := by
  obtain ⟨targetValue, targetFound, related⟩ := (envRel_iff_lookup _ _ _).1 environments name value found
  simpa [EvalSim, compile, compileExps, compileExp, FlatSem.evaluate, ClosSem.evaluate, found, targetFound]
    using And.intro states (EvalResultRel.value (.cons related .nil))

/-- Literal compilation evaluates to a related closure value without
changing either state. -/
theorem evaluate_lit {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (literal : Lit) (states : StateRel source target) :
    EvalSim env names values source target [.lit trace literal] := by
  cases literal <;>
    simp [EvalSim, compile, compileExps, compileExp, compileLit, FlatSem.evaluate,
      ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
      ClosSem.doIntApp, ClosSem.applyBlock, ClosSem.makeConst, states]
  all_goals first
    | exact EvalResultRel.value (.cons (ValueRel.int _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.char _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.string _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.word8 _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.word64 _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.float64 _) .nil)

/-- Nullary tuples and constructors evaluate to related closure blocks. -/
theorem evaluate_con_nil {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (stamp : Option (FlatLang.CtorId × FlatLang.TypeId))
    (states : StateRel source target) :
    EvalSim env names values source target [.con trace stamp []] := by
  cases stamp with
  | none =>
    simp [EvalSim, compile, compileExps, compileExp, smartCons, FlatSem.evaluate,
      ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, states,
      EvalResultRel.value (.cons (ValueRel.tuple .nil) .nil)]
  | some stamp =>
    obtain ⟨tag, typeId⟩ := stamp
    simp [EvalSim, compile, compileExps, compileExp, smartCons, FlatSem.evaluate,
      ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, states,
      EvalResultRel.value (.cons (ValueRel.con .nil) .nil)]

/-- Constructor translation preserves evaluation when its reversed
argument list is simulated. -/
theorem evaluate_con {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (stamp : Option (FlatLang.CtorId × FlatLang.TypeId))
    (arguments : List FlatLang.Exp)
    (argsSim : EvalSim env names values source target arguments.reverse) :
    EvalSim env names values source target [.con trace stamp arguments] := by
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
  rw [FlatSem.evaluate, smartCons_evaluate, ClosSem.evaluate, ClosSem.fixClock_evaluate]
  cases flatRun : FlatSem.evaluate env source arguments.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names arguments).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        cases stamp with
        | none =>
          simp [ClosSem.doApp, ClosSem.applyBlock, states,
            EvalResultRel.value (.cons (ValueRel.tuple (List.rel_reverse related)) .nil)]
        | some stamp =>
          obtain ⟨tag, typeId⟩ := stamp
          simp [ClosSem.doApp, ClosSem.applyBlock, states,
            EvalResultRel.value (.cons (ValueRel.con (List.rel_reverse related)) .nil)]

/-- A match-free flat function compiles to a related unary closure when the
target supports unary calls. -/
theorem evaluate_fn {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace name : MlString) (body : FlatLang.Exp)
    (states : StateRel source target) (environments : EnvRel env names values)
    (safe : FlatProps.noMat body = true) :
    EvalSim env names values source target [.fn trace name body] := by
  have closure : ValueRel (.closure env name body) (.closure none [] values 1 (compileExp (some name :: names) body)) :=
    .closure environments safe
  have positive := states.1
  simp [EvalSim, compile, compileExps, compileExp, FlatSem.evaluate, ClosSem.evaluate.eq_def, positive, states,
    EvalResultRel.value (.cons closure .nil)]

/-- Recursive binding compilation extends related environments with the
same ordered function group, then evaluates the body. -/
theorem evaluate_letrec {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : MlString) (funs : List (VarN × VarN × FlatLang.Exp)) (body : FlatLang.Exp)
    (states : StateRel source target) (environments : EnvRel env names values)
    (safe : FlatProps.noMatFuns funs = true)
    (bodySim : ∀ (env' : FlatSem.Environment FlatSem.Value) (names' : List (Option MlString))
        (values' : List ClosSem.Value),
      EnvRel env' names' values' →
      (FlatSem.evaluate env' source [body]).2 ≠ .err (.abort .typeError) →
      EvalSim env' names' values' source target [body])
    (notTypeError : (FlatSem.evaluate env source [.letrec trace funs body]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.letrec trace funs body] := by
  have distinct : (funs.map Prod.fst).Nodup := by
    by_contra duplicate
    simp [FlatSem.evaluate, duplicate] at notTypeError
  have unary := compileFuns_unary (funs.map (fun f => some f.1) ++ names) funs target.maxApp states.1
  have extended := envRel_rec funs env names values environments distinct safe
  have bodyNot : (FlatSem.evaluate { env with v := FlatSem.buildRecEnv funs env env.v } source [body]).2 ≠
      .err (.abort .typeError) := by
    simpa [FlatSem.evaluate, distinct] using notTypeError
  have simulated := bodySim _ _ _ extended bodyNot
  unfold EvalSim at simulated ⊢
  simp only [compile, compileExps, compileExp] at simulated ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate.eq_def]
  simpa only [distinct, unary, ↓reduceIte] using simulated

/-- A related body simulation lifts through a raise, preserving an existing
error or relating the raised singleton value. -/
theorem evaluate_raise {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (bodySim : EvalSim env names values source target [body]) :
    EvalSim env names values source target [.raise trace body] := by
  unfold EvalSim at bodySim ⊢
  simp only [compile, compileExps, compileExp] at bodySim ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate]
  cases flatRun : FlatSem.evaluate env source [body] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names body] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at bodySim ⊢
      rcases bodySim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next body _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | nil => exact ⟨states, .raise head⟩
          | cons _ _ => simp at length

/-- A let binding extends the related environments and composes the bound
expression with the body's induction hypothesis. -/
theorem evaluate_let {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (name : Option MlString) (first body : FlatLang.Exp)
    (environments : EnvRel env names values)
    (firstSim : EvalSim env names values source target [first])
    (bodySim : ∀ (sourceValue : FlatSem.Value) (targetValue : ClosSem.Value)
        (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      ValueRel sourceValue targetValue → StateRel next nextTarget →
      let nextEnv := { env with v := match name with
        | none => env.v | some key => (key, sourceValue) :: env.v }
      EnvRel nextEnv (name :: names) (targetValue :: values) →
      (FlatSem.evaluate nextEnv next [body]).2 ≠ .err (.abort .typeError) →
      EvalSim nextEnv (name :: names) (targetValue :: values) next nextTarget [body])
    (notTypeError : (FlatSem.evaluate env source [.let_ trace name first body]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.let_ trace name first body] := by
  have flatFix := (FlatSem.fixClock_evaluations env source [first] first []).1
  have closFix := ClosSem.fixClock_evaluate [compileExp names first] values target
  unfold EvalSim at firstSim ⊢
  simp only [compile, compileExps, compileExp] at firstSim ⊢
  rw [FlatSem.evaluate, flatFix] at notTypeError ⊢
  rw [ClosSem.evaluate, closFix]
  cases flatRun : FlatSem.evaluate env source [first] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names first] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at firstSim notTypeError ⊢
      rcases firstSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next first _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | nil =>
            rename_i flatHead closHead
            simp at notTypeError ⊢
            cases name with
            | none =>
              have nextEnv := envRel_skip environments closHead
              simpa [EvalSim, compile, compileExps] using bodySim _ _ next nextTarget head states nextEnv notTypeError
            | some key =>
              have nextEnv := envRel_cons (name := key) environments head
              simpa [EvalSim, compile, compileExps] using bodySim _ _ next nextTarget head states nextEnv notTypeError
          | cons _ _ => simp at length

/-- A related Boolean condition selects the same branch in both evaluators. -/
theorem evaluate_if {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (condition yes no : FlatLang.Exp)
    (conditionSim : EvalSim env names values source target [condition])
    (branchSim : ∀ (branch : Bool) (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      StateRel next nextTarget →
      (FlatSem.evaluate env next [if branch then yes else no]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values next nextTarget [if branch then yes else no])
    (notTypeError : (FlatSem.evaluate env source [.if_ trace condition yes no]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.if_ trace condition yes no] := by
  have flatFix := (FlatSem.fixClock_evaluations env source [condition] condition []).1
  have closFix := ClosSem.fixClock_evaluate [compileExp names condition] values target
  unfold EvalSim at conditionSim ⊢
  simp only [compile, compileExps, compileExp] at conditionSim ⊢
  rw [FlatSem.evaluate, flatFix] at notTypeError ⊢
  rw [ClosSem.evaluate, closFix]
  cases flatRun : FlatSem.evaluate env source [condition] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names condition] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at conditionSim notTypeError ⊢
      rcases conditionSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next condition _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | nil =>
            rename_i flatHead closHead
            simp at notTypeError ⊢
            cases choice : FlatSem.doIf flatHead true false with
            | none =>
              have actualChoice : FlatSem.doIf flatHead yes no = none := by rw [doIf_asBool, choice]; rfl
              split at notTypeError <;> simp_all
            | some branch =>
              have targetChoice := doIf_related flatHead closHead branch head choice
              have actualChoice : FlatSem.doIf flatHead yes no = some (if branch then yes else no) := by
                rw [doIf_asBool, choice]
                rfl
              cases branch <;> split at notTypeError <;> simp_all
              · simpa [EvalSim, compile, compileExps] using branchSim.1 next nextTarget states notTypeError
              · simpa [EvalSim, compile, compileExps] using branchSim.2 next nextTarget states notTypeError
          | cons _ _ => simp at length

/-- A single variable handler binds the raised value in both environments.
This is the handler shape admitted by the flat no-match condition. -/
theorem evaluate_handle {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (name : MlString) (body handler : FlatLang.Exp)
    (environments : EnvRel env names values)
    (bodySim : EvalSim env names values source target [body])
    (handlerSim : ∀ (sourceValue : FlatSem.Value) (targetValue : ClosSem.Value)
        (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      ValueRel sourceValue targetValue → StateRel next nextTarget →
      EnvRel { env with v := (name, sourceValue) :: env.v } (some name :: names) (targetValue :: values) →
      (FlatSem.evaluate { env with v := (name, sourceValue) :: env.v } next [handler]).2 ≠
        .err (.abort .typeError) →
      EvalSim { env with v := (name, sourceValue) :: env.v } (some name :: names)
        (targetValue :: values) next nextTarget [handler])
    (notTypeError : (FlatSem.evaluate env source [.handle trace body [(.pvar name, handler)]]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.handle trace body [(.pvar name, handler)]] := by
  have flatFix := (FlatSem.fixClock_evaluations env source [body] body []).1
  have closFix := ClosSem.fixClock_evaluate [compileExp names body] values target
  unfold EvalSim at bodySim ⊢
  simp only [compile, compileExps, compileExp] at bodySim ⊢
  rw [FlatSem.evaluate, flatFix] at notTypeError ⊢
  rw [ClosSem.evaluate, closFix]
  cases flatRun : FlatSem.evaluate env source [body] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names body] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at bodySim notTypeError ⊢
      rcases bodySim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | value related => exact ⟨states, .value related⟩
      | raise related =>
        rename_i sourceValue targetValue
        have selected : FlatSem.selectRow next [(.pvar name, handler)] sourceValue sourceValue =
            .ok ([(name, sourceValue)], handler) := by
          simp [FlatSem.selectRow, FlatSem.pmatchRows, FlatSem.pmatch, FlatLang.patBindings]
        repeat' first | split at notTypeError | simp_all
        repeat' first | split | simp_all
        all_goals simp_all [FlatSem.selectRow, FlatSem.pmatchRows, FlatSem.pmatch, FlatLang.patBindings]
        rcases selected with ⟨selectedBindings, selectedBody⟩
        obtain ⟨bindingsEq, bodyEq⟩ := ‹_ ∧ _›
        subst_vars
        have nextEnv := envRel_cons (name := name) environments related
        simpa [EvalSim, compile, compileExps] using
          handlerSim _ _ next nextTarget related states nextEnv notTypeError

/-- Compose singleton and tail simulations for a nonempty tail. The tail
induction hypothesis is used only when the tail does not end in a source
type error, as in the original pass theorem. -/
theorem evaluate_cons {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (firstSim : EvalSim env names values source target [first])
    (tailSim : ∀ (source' : FlatSem.State C F) (target' : ClosSem.State C F), StateRel source' target' →
      (FlatSem.evaluate env source' (second :: rest)).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source' target' (second :: rest))
    (notTypeError : (FlatSem.evaluate env source (first :: second :: rest)).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target (first :: second :: rest) := by
  have flatFix := (FlatSem.fixClock_evaluations env source [first] first []).1
  have closFix := ClosSem.fixClock_evaluate [compileExp names first] values target
  unfold EvalSim at firstSim ⊢
  simp only [compile, compileExps] at firstSim ⊢
  rw [FlatSem.evaluate, flatFix] at notTypeError ⊢
  rw [ClosSem.evaluate, closFix]
  cases flatRun : FlatSem.evaluate env source [first] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names first] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at firstSim notTypeError ⊢
      rcases firstSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next first _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | nil =>
            simp at notTypeError ⊢
            have tailNot : (FlatSem.evaluate env next (second :: rest)).2 ≠ .err (.abort .typeError) := by
              intro bad
              simp [bad] at notTypeError
            have tailRelated := tailSim next nextTarget states tailNot
            simp only [EvalSim, compile, compileExps] at tailRelated
            cases flatTail : FlatSem.evaluate env next (second :: rest) with
            | mk final flatResult =>
              cases closTail : ClosSem.evaluate (compileExp names second :: compileExps names rest) values nextTarget with
              | mk closResult finalTarget =>
                simp only [flatTail, closTail] at tailRelated ⊢
                rcases tailRelated with ⟨finalStates, finalResults⟩
                cases finalResults with
                | value tailValues => exact ⟨finalStates, .value (.cons head tailValues)⟩
                | raise valueRel => exact ⟨finalStates, .raise valueRel⟩
                | abort error => exact ⟨finalStates, .abort error⟩
          | cons _ _ => simp at length

end Flapjack.Compiler.Backend.FlatToClos
