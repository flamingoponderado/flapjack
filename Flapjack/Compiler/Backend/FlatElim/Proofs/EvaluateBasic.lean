import Flapjack.Compiler.Backend.FlatElim.Proofs.ApplyNumeric
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact

/-! Basic expression cases of the flat-elimination evaluation simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- No expression in the list contains dynamic evaluation. -/
def expressionsNoEval (expressions : List FlatLang.Exp) : Prop :=
  ∀ expression ∈ expressions, hasEval expression = false

/-- The Boolean expression-list traversal agrees with its member-wise form. -/
theorem hasEvalList_eq_false_iff (expressions : List FlatLang.Exp) :
    hasEvalList expressions = false ↔ expressionsNoEval expressions := by
  induction expressions with
  | nil => simp [hasEvalList, expressionsNoEval]
  | cons expression rest ih =>
    simp [hasEvalList, expressionsNoEval] at ih ⊢
    intro _
    exact ih

/-- A list of expressions is reachable exactly when each expression is. -/
theorem findLookupsList_within_iff (expressions : List FlatLang.Exp) (reachable : NumSet) :
    globalsWithin (findGlobalsList destGlobalVarLookup expressions) reachable ↔
      ∀ expression ∈ expressions, globalsWithin (findLookups expression) reachable := by
  induction expressions with
  | nil => simp [findGlobalsList, globalsWithin, sptMem, sptDomain]
  | cons expression rest ih =>
    simp only [findGlobalsList, globalsWithin_union, List.mem_cons, forall_eq_or_imp, ih, findLookups]

/-- Reversing evaluation arguments does not change their global bound. -/
theorem findLookupsList_reverse_within (expressions : List FlatLang.Exp) (reachable : NumSet)
    (closed : globalsWithin (findGlobalsList destGlobalVarLookup expressions) reachable) :
    globalsWithin (findGlobalsList destGlobalVarLookup expressions.reverse) reachable := by
  apply (findLookupsList_within_iff _ _).mpr
  intro expression member
  exact (findLookupsList_within_iff _ _).mp closed expression (by simpa using member)

/-- Reversing evaluation results preserves their global bound. -/
theorem findValuesGlobals_reverse_within (values : List FlatSem.Value) (reachable : NumSet)
    (closed : globalsWithin (findValuesGlobals values) reachable) :
    globalsWithin (findValuesGlobals values.reverse) reachable := by
  apply (findValuesGlobals_within_iff _ _).mpr
  intro value member
  exact (findValuesGlobals_within_iff _ _).mp closed value (by simpa using member)

/-- Reversing an Eval-free list of expressions preserves that invariant. -/
theorem expressionsNoEval_reverse (expressions : List FlatLang.Exp)
    (safe : expressionsNoEval expressions) : expressionsNoEval expressions.reverse := by
  intro expression member
  exact safe expression (by simpa using member)

/-- Reversing an Eval-free list of values preserves that invariant. -/
theorem valuesNoEval_reverse (values : List FlatSem.Value)
    (safe : valuesNoEval values) : valuesNoEval values.reverse := by
  intro value member
  exact safe value (by simpa using member)

/-- The evaluation simulation statement for one expression list. -/
def evaluationSimulation {C F : Type} (expressions : List FlatLang.Exp) : Prop :=
  ∀ (env : FlatSem.Environment FlatSem.Value) (source next : FlatSem.State C F)
    (result : Result (List FlatSem.Value) FlatSem.Value) (reachable : NumSet) (target : FlatSem.State C F),
    FlatSem.evaluate env source expressions = (next, result) →
    globalsWithin (findGlobalsList destGlobalVarLookup expressions) reachable →
    flatStateRel reachable source target → globalsWithin (findEnvGlobals env) reachable →
    bindingsNoEval env.v → expressionsNoEval expressions → result ≠ .err (.abort .typeError) →
    ∃ targetNext, FlatSem.evaluate env target expressions = (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧ globalsWithin (findPrimitiveResultGlobals result) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues result)

/-- The empty-expression case of the original evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel_empty {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source next target : FlatSem.State C F) (result : Result (List FlatSem.Value) FlatSem.Value)
    (reachable : NumSet) (run : FlatSem.evaluate env source [] = (next, result))
    (_lookupsClosed : globalsWithin (findGlobalsList destGlobalVarLookup []) reachable)
    (related : flatStateRel reachable source target)
    (_envClosed : globalsWithin (findEnvGlobals env) reachable)
    (_envSafe : bindingsNoEval env.v) (_expressionsSafe : expressionsNoEval [])
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, FlatSem.evaluate env target [] = (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧
      globalsWithin (findPrimitiveResultGlobals result) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues result) := by
  simp [FlatSem.evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  refine ⟨target, by simp [FlatSem.evaluate], related, ?_, ?_⟩
  · simp [findPrimitiveResultGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain]
  · simp [Flapjack.Compiler.Backend.FlatProps.resultValues, valuesNoEval]

/-- The literal case of the original evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel_lit {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source next target : FlatSem.State C F) (result : Result (List FlatSem.Value) FlatSem.Value)
    (reachable : NumSet) (tra : BackendCommon.Tra) (lit : Flapjack.AstHOL.Lit)
    (run : FlatSem.evaluate env source [.lit tra lit] = (next, result))
    (_lookupsClosed : globalsWithin (findGlobalsList destGlobalVarLookup [.lit tra lit]) reachable)
    (related : flatStateRel reachable source target)
    (_envClosed : globalsWithin (findEnvGlobals env) reachable)
    (_envSafe : bindingsNoEval env.v) (_expressionsSafe : expressionsNoEval [.lit tra lit])
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, FlatSem.evaluate env target [.lit tra lit] = (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧
      globalsWithin (findPrimitiveResultGlobals result) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues result) := by
  simp [FlatSem.evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  have resultSafe := primitiveResult_value_invariants reachable (.litv lit)
    (by simp [findValueGlobals, globalsWithin, sptMem, sptDomain]) (by simp [valueHasEval])
  exact ⟨target, by simp [FlatSem.evaluate], related, resultSafe.1, resultSafe.2⟩

/-- The local-variable case of the original evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel_var {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source next target : FlatSem.State C F) (result : Result (List FlatSem.Value) FlatSem.Value)
    (reachable : NumSet) (tra : BackendCommon.Tra) (name : Flapjack.AstHOL.VarN)
    (run : FlatSem.evaluate env source [.varLocal tra name] = (next, result))
    (_lookupsClosed : globalsWithin (findGlobalsList destGlobalVarLookup [.varLocal tra name]) reachable)
    (related : flatStateRel reachable source target)
    (envClosed : globalsWithin (findEnvGlobals env) reachable)
    (envSafe : bindingsNoEval env.v) (_expressionsSafe : expressionsNoEval [.varLocal tra name])
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, FlatSem.evaluate env target [.varLocal tra name] = (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧
      globalsWithin (findPrimitiveResultGlobals result) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues result) := by
  cases lookup : env.v.lookup name with
  | none =>
    simp [FlatSem.evaluate, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    exact (notTypeError rfl).elim
  | some value =>
    simp [FlatSem.evaluate, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    have member : (name, value) ∈ env.v := by
      obtain ⟨before, after, h, _⟩ := List.lookup_eq_some_iff.mp lookup
      rw [h]
      simp
    have valueClosed : globalsWithin (findValueGlobals value) reachable := by
      intro key keyFound
      apply envClosed key
      apply findValuesGlobals_member (env.v.map Prod.snd) value _ key keyFound
      exact List.mem_map.mpr ⟨(name, value), member, rfl⟩
    have valueSafe : valueHasEval value = false := envSafe (name, value) member
    have resultSafe := primitiveResult_value_invariants reachable value valueClosed valueSafe
    exact ⟨target, by simp [FlatSem.evaluate, lookup], related, resultSafe.1, resultSafe.2⟩

/-- The closure-creation case of the original evaluation simulation. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel_fn {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source next target : FlatSem.State C F) (result : Result (List FlatSem.Value) FlatSem.Value)
    (reachable : NumSet) (functionName argumentName : Flapjack.AstHOL.VarN) (body : FlatLang.Exp)
    (run : FlatSem.evaluate env source [.fn functionName argumentName body] = (next, result))
    (lookupsClosed : globalsWithin (findGlobalsList destGlobalVarLookup [.fn functionName argumentName body]) reachable)
    (related : flatStateRel reachable source target)
    (envClosed : globalsWithin (findEnvGlobals env) reachable)
    (envSafe : bindingsNoEval env.v) (expressionsSafe : expressionsNoEval [.fn functionName argumentName body])
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, FlatSem.evaluate env target [.fn functionName argumentName body] = (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧
      globalsWithin (findPrimitiveResultGlobals result) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues result) := by
  have bodyClosed : globalsWithin (findLookups body) reachable := by
    simp only [findGlobalsList, findGlobals, globalsWithin_union] at lookupsClosed
    exact lookupsClosed.1
  have bodySafe : hasEval body = false := by
    have safe := expressionsSafe (.fn functionName argumentName body) (by simp)
    simpa [hasEval] using safe
  have envValuesSafe : valuesNoEval (env.v.map Prod.snd) := by
    intro value member
    obtain ⟨binding, bindingMember, eq⟩ := List.mem_map.mp member
    subst value
    exact envSafe binding bindingMember
  have envBindingsSafe : bindingsHaveEval env.v = false := by
    rw [bindingsHaveEval_eq_map]
    exact (valuesHaveEval_eq_false_iff _).mpr envValuesSafe
  have closureClosed : globalsWithin (findValueGlobals (.closure env argumentName body)) reachable := by
    cases env with
    | mk bindings =>
      simp only [findValueGlobals, findBindingsGlobals_eq_map, globalsWithin_union]
      exact ⟨envClosed, bodyClosed⟩
  have closureSafe : valueHasEval (.closure env argumentName body) = false := by
    cases env with
    | mk bindings => simp [valueHasEval, bodySafe, envBindingsSafe]
  simp [FlatSem.evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  have resultSafe := primitiveResult_value_invariants reachable (.closure env argumentName body) closureClosed closureSafe
  exact ⟨target, by simp [FlatSem.evaluate], related, resultSafe.1, resultSafe.2⟩

/-- Lifting a non-application primitive result preserves the evaluation
simulation. This helper connects the primitive theorem to the evaluator. -/
theorem applyResult_flatStateRel {C F : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (op : FlatLang.Op) (values : List FlatSem.Value)
    (result : Result (List FlatSem.Value) FlatSem.Value) (tra : BackendCommon.Tra)
    (related : flatStateRel reachable source target) (opNotApply : op ≠ .src .opapp)
    (valuesClosed : globalsWithin (findValuesGlobals values) reachable)
    (opClosed : globalsWithin (findLookups (.app tra op [])) reachable)
    (valuesSafe : valuesNoEval values)
    (run : FlatSem.applyResult source op values = (next, result))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, FlatSem.applyResult target op values = (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧
      globalsWithin (findPrimitiveResultGlobals result) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues result) := by
  cases call : FlatSem.doApp source op values with
  | none =>
    simp [FlatSem.applyResult, call] at run
    rcases run with ⟨rfl, rfl⟩
    exact (notTypeError rfl).elim
  | some output =>
    obtain ⟨state, primitiveResult⟩ := output
    have lifted : FlatSem.applyResult source op values = (state, Flapjack.EvaluateHOL.listResult primitiveResult) := by
      cases primitiveResult <;> simp [FlatSem.applyResult, Flapjack.EvaluateHOL.listResult, call]
    rw [lifted] at run
    cases run
    have primitiveNotTypeError : primitiveResult ≠ .err (.abort .typeError) := by
      intro bad
      subst primitiveResult
      exact notTypeError rfl
    obtain ⟨targetNext, stateRel, targetCall, closed, safe⟩ :=
      doApp_some_flatStateRel reachable source target op values next primitiveResult () tra related opNotApply
        valuesClosed opClosed valuesSafe call primitiveNotTypeError
    refine ⟨targetNext, ?_, stateRel, closed, safe⟩
    cases primitiveResult <;> simp [FlatSem.applyResult, Flapjack.EvaluateHOL.listResult, targetCall]

/-- Clamping related evaluation states to related initial clocks preserves the
flat state relation. -/
theorem flatStateRel_fixClock {C F : Type} (reachable : NumSet)
    (source target sourceNext targetNext : FlatSem.State C F)
    (result : Result (List FlatSem.Value) FlatSem.Value)
    (initial : flatStateRel reachable source target) (next : flatStateRel reachable sourceNext targetNext) :
    flatStateRel reachable (FlatSem.fixClock source (sourceNext, result)).1
      (FlatSem.fixClock target (targetNext, result)).1 := by
  obtain ⟨initialClock, _, _, _, _, _⟩ := initial
  obtain ⟨nextClock, refs, ffi, globals, refsClosed, refsSafe⟩ := next
  exact ⟨by simp [FlatSem.fixClock, initialClock, nextClock], refs, ffi, globals, refsClosed, refsSafe⟩

/-- The assignment-application case of the evaluation simulation, assuming
the original induction hypothesis for evaluation of its arguments. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_keep_flat_state_rel_eq_lemma"]
theorem evaluate_keep_flatStateRel_appAssign {C F : Type} (tra : BackendCommon.Tra)
    (args : List FlatLang.Exp) (ih : evaluationSimulation (C := C) (F := F) args.reverse) :
    evaluationSimulation (C := C) (F := F) [.app tra (.src .opassign) args] := by
  intro env source next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have argsClosed : globalsWithin (findGlobalsList destGlobalVarLookup args.reverse) reachable := by
    apply findLookupsList_reverse_within args reachable
    simp only [findGlobalsList, findGlobals, destGlobalVarLookup, globalsWithin_union] at lookupsClosed
    exact lookupsClosed.1
  have argsSafe : expressionsNoEval args.reverse := by
    apply expressionsNoEval_reverse args
    apply (hasEvalList_eq_false_iff args).mp
    have safe := expressionsSafe (.app tra (.src .opassign) args) (by simp)
    simpa [hasEval] using safe
  cases argEval : FlatSem.evaluate env source args.reverse with
  | mk argState argResult =>
    simp only [FlatSem.evaluate, argEval, FlatSem.fixClock] at run
    have argNotTypeError : argResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetArgState, targetArgEval, argRelated, argClosed, argSafe⟩ :=
      ih env source argState argResult reachable target argEval argsClosed related envClosed envSafe argsSafe argNotTypeError
    have clampedRelated := flatStateRel_fixClock reachable source target argState targetArgState argResult related argRelated
    simp only [FlatSem.fixClock] at clampedRelated
    cases argResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ targetArgState with clock := min target.clock targetArgState.clock }, ?_, clampedRelated, argClosed, argSafe⟩
      simp [FlatSem.evaluate, targetArgEval, FlatSem.fixClock]
    | val values =>
      simp only at run
      have valuesClosed : globalsWithin (findValuesGlobals values.reverse) reachable := by
        apply findValuesGlobals_reverse_within
        simpa [findPrimitiveResultGlobals] using argClosed
      have valuesSafe : valuesNoEval values.reverse := by
        apply valuesNoEval_reverse
        simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using argSafe
      have opClosed : globalsWithin (findLookups (.app tra (.src .opassign) [])) reachable := by
        simp [findLookups, findGlobals, destGlobalVarLookup, findGlobalsList, globalsWithin, sptMem, sptDomain]
      obtain ⟨targetNext, applied, nextRelated, closed, safe⟩ :=
        applyResult_flatStateRel reachable
          { argState with clock := min source.clock argState.clock }
          { targetArgState with clock := min target.clock targetArgState.clock }
          next (.src .opassign) values.reverse result tra clampedRelated (by intro h; cases h)
          valuesClosed opClosed valuesSafe run notTypeError
      refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
      simpa [FlatSem.evaluate, targetArgEval, FlatSem.fixClock] using applied

end Flapjack.Compiler.Backend.FlatElim
