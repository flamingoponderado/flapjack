import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence

/-! Captured-environment facts for the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Restricting related environments to valid source indices produces
pointwise related captured values, in the original order. -/
theorem lookupVars_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (indices : List Nat) (env : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (values : List ClosSem.Value) (related : envRel maxApp f refs code env targetEnv)
    (lookup : ClosSem.lookupVars indices env = some values) :
    ∃ targetValues, ClosSem.lookupVars indices targetEnv = some targetValues ∧
      List.Forall₂ (vRel maxApp f refs code) values targetValues ∧ indices.length = values.length := by
  induction indices generalizing values with
  | nil =>
    simp [ClosSem.lookupVars] at lookup
    subst values
    exact ⟨[], rfl, .nil, rfl⟩
  | cons index indices ih =>
    cases headLookup : env[index]? with
    | none => simp [ClosSem.lookupVars, headLookup] at lookup
    | some value =>
      cases tailLookup : ClosSem.lookupVars indices env with
      | none => simp [ClosSem.lookupVars, headLookup, tailLookup] at lookup
      | some rest =>
        simp [ClosSem.lookupVars, headLookup, tailLookup] at lookup
        subst values
        obtain ⟨targetValue, targetLookup, valueRel⟩ := envRel_lookup related headLookup
        obtain ⟨targetRest, targetTailLookup, restRel, lengthEq⟩ := ih rest tailLookup
        refine ⟨targetValue :: targetRest, ?_, .cons valueRel restRel, ?_⟩
        · simp [ClosSem.lookupVars, targetLookup, targetTailLookup]
        · simpa using congrArg Nat.succ lengthEq

/-- Evaluating a list of BVL variables is exactly environment selection and
leaves the state untouched, including the clock. -/
theorem evaluate_vars {C F : Type} (indices : List Nat) (env : List BvlSem.Value)
    (state : BvlSem.State C F) (values : List BvlSem.Value)
    (lookup : ClosSem.lookupVars indices env = some values) :
    BvlSem.evaluate (indices.map Bvl.Exp.var) env state = (.val values, state) := by
  induction indices generalizing values with
  | nil =>
    simp [ClosSem.lookupVars] at lookup
    subst values
    simp [BvlSem.evaluate]
  | cons index indices ih =>
    cases headLookup : env[index]? with
    | none => simp [ClosSem.lookupVars, headLookup] at lookup
    | some value =>
      cases tailLookup : ClosSem.lookupVars indices env with
      | none => simp [ClosSem.lookupVars, headLookup, tailLookup] at lookup
      | some rest =>
        simp [ClosSem.lookupVars, headLookup, tailLookup] at lookup
        subst values
        cases indices with
        | nil =>
          simp [ClosSem.lookupVars] at tailLookup
          subst rest
          simp [BvlSem.evaluate, headLookup]
        | cons next tail =>
          have tailRun := ih rest tailLookup
          have headRun : BvlSem.evaluate [.var index] env state = (.val [value], state) := by
            simp [BvlSem.evaluate, headLookup]
          simp only [List.map_cons] at tailRun ⊢
          rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, headRun, tailRun]
          rfl

/-- The original lookup fact used by closure compilation: source capture
selection yields a related target selection whose BVL variable evaluation is
independent of the target state. This candidate is untagged pending HOL
inferred-carrier and evaluator review. -/
theorem lookupVars_simulation {C F : Type} {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (indices : List Nat) (env : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (values : List ClosSem.Value) (related : envRel maxApp f refs code env targetEnv)
    (lookup : ClosSem.lookupVars indices env = some values) :
    ∃ targetValues, (∀ state : BvlSem.State C F,
      BvlSem.evaluate (indices.map Bvl.Exp.var) targetEnv state = (.val targetValues, state)) ∧
      List.Forall₂ (vRel maxApp f refs code) values targetValues ∧ indices.length = values.length := by
  obtain ⟨targetValues, targetLookup, valuesRel, lengthEq⟩ := lookupVars_related indices env targetEnv values related lookup
  exact ⟨targetValues, fun state => evaluate_vars indices targetEnv state targetValues targetLookup, valuesRel, lengthEq⟩

/-- Successful environment selections compose over concatenated indices. -/
theorem lookupVars_append {α : Type} (first second : List Nat) (env : List α)
    (values more : List α) (firstLookup : ClosSem.lookupVars first env = some values)
    (secondLookup : ClosSem.lookupVars second env = some more) :
    ClosSem.lookupVars (first ++ second) env = some (values ++ more) := by
  induction first generalizing values with
  | nil =>
    simp [ClosSem.lookupVars] at firstLookup
    subst values
    simpa using secondLookup
  | cons index tail ih =>
    cases headLookup : env[index]? with
    | none => simp [ClosSem.lookupVars, headLookup] at firstLookup
    | some value =>
      cases restLookup : ClosSem.lookupVars tail env with
      | none => simp [ClosSem.lookupVars, headLookup, restLookup] at firstLookup
      | some rest =>
        simp [ClosSem.lookupVars, headLookup, restLookup] at firstLookup
        subst values
        have restResult := ih rest restLookup
        simp [ClosSem.lookupVars, headLookup, restResult]

/-- Selecting reversed indices returns the selected values in reverse order. -/
theorem lookupVars_reverse {α : Type} (indices : List Nat) (env : List α) (values : List α)
    (lookup : ClosSem.lookupVars indices env = some values) :
    ClosSem.lookupVars indices.reverse env = some values.reverse := by
  induction indices generalizing values with
  | nil => simp [ClosSem.lookupVars] at lookup; subst values; rfl
  | cons index tail ih =>
    cases headLookup : env[index]? with
    | none => simp [ClosSem.lookupVars, headLookup] at lookup
    | some value =>
      cases tailLookup : ClosSem.lookupVars tail env with
      | none => simp [ClosSem.lookupVars, headLookup, tailLookup] at lookup
      | some rest =>
        simp [ClosSem.lookupVars, headLookup, tailLookup] at lookup
        subst values
        have reverseTail := ih rest tailLookup
        have single : ClosSem.lookupVars [index] env = some [value] := by
          simp [ClosSem.lookupVars, headLookup]
        simpa using lookupVars_append tail.reverse [index] env rest.reverse [value] reverseTail single

/-- Variable evaluation may be prefixed to a successful nonempty target
expression list, preserving its final state and concatenating its values. -/
theorem evaluate_vars_append {C F : Type} (indices : List Nat) (env : List BvlSem.Value)
    (state final : BvlSem.State C F) (values more : List BvlSem.Value) (tail : List Bvl.Exp)
    (tailNonempty : tail ≠ []) (lookup : ClosSem.lookupVars indices env = some values)
    (tailRun : BvlSem.evaluate tail env state = (.val more, final)) :
    BvlSem.evaluate (indices.map Bvl.Exp.var ++ tail) env state = (.val (values ++ more), final) := by
  induction indices generalizing values with
  | nil =>
    simp [ClosSem.lookupVars] at lookup
    subst values
    simpa using tailRun
  | cons index indices ih =>
    cases headLookup : env[index]? with
    | none => simp [ClosSem.lookupVars, headLookup] at lookup
    | some value =>
      cases restLookup : ClosSem.lookupVars indices env with
      | none => simp [ClosSem.lookupVars, headLookup, restLookup] at lookup
      | some rest =>
        simp [ClosSem.lookupVars, headLookup, restLookup] at lookup
        subst values
        have headRun : BvlSem.evaluate [.var index] env state = (.val [value], state) := by
          simp [BvlSem.evaluate, headLookup]
        have remaining := ih rest restLookup
        have nonempty : indices.map Bvl.Exp.var ++ tail ≠ [] := by
          cases indices with
          | nil => simpa using tailNonempty
          | cons first rest => simp
        cases remainingExpressions : indices.map Bvl.Exp.var ++ tail with
        | nil => exact False.elim (nonempty remainingExpressions)
        | cons next later =>
          simp only [List.map_cons, List.cons_append, remainingExpressions]
          rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, headRun]
          simp only [remainingExpressions] at remaining
          rw [remaining]
          rfl

/-- The closure constructor's arguments evaluate in reverse order, leaving
the target state unchanged when the generated code label is installed. -/
theorem evaluate_closure_arguments {C F : Type} (indices : List Nat) (env : List BvlSem.Value)
    (state : BvlSem.State C F) (values : List BvlSem.Value) (label arity : Nat)
    (lookup : ClosSem.lookupVars indices env = some values)
    (installed : ∃ entry, sptLookup label state.code = some entry) :
    BvlSem.evaluate ((mkLabel label :: mkConst arity :: indices.map Bvl.Exp.var).reverse) env state =
      (.val (values.reverse ++ [.number (Int.ofNat arity), .codePtr label]), state) := by
  obtain ⟨entry, labelLookup⟩ := installed
  have tailRun : BvlSem.evaluate [mkConst arity, mkLabel label] env state =
      (.val [.number (Int.ofNat arity), .codePtr label], state) := by
    simp [mkConst, mkLabel, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp, labelLookup]
  have reversed := lookupVars_reverse indices env values lookup
  have evaluated := evaluate_vars_append indices.reverse env state state values.reverse
    [.number (Int.ofNat arity), .codePtr label] [mkConst arity, mkLabel label] (by simp) reversed tailRun
  simpa using evaluated

/-- The generated closure block contains its installed code pointer, arity,
and captured values in source capture order. -/
theorem evaluate_closure_block {C F : Type} (indices : List Nat) (env : List BvlSem.Value)
    (state : BvlSem.State C F) (values : List BvlSem.Value) (label arity : Nat)
    (lookup : ClosSem.lookupVars indices env = some values)
    (installed : ∃ entry, sptLookup label state.code = some entry) :
    BvlSem.evaluate [.op (.blockOp (.cons 30))
      ((mkLabel label :: mkConst arity :: indices.map Bvl.Exp.var).reverse)] env state =
      (.val [.block 30 (.codePtr label :: .number (Int.ofNat arity) :: values)], state) := by
  have argsRun := evaluate_closure_arguments indices env state values label arity lookup installed
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun]
  simp [BvlSem.doApp, BvlSem.applyBlock]

/-- Closure creation satisfies the source-shaped simulation when locations
and captured-variable annotations are present and generated code is installed.
This proof-side candidate remains untagged pending semantic carrier review. -/
theorem expressionSimulation_fn {C F : Type} (name : Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp) :
    expressionSimulation (C := C) (F := F) [.fn name location selected arity body] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases location with
  | none => simp [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] at locations
  | some label =>
    cases selected with
    | none => simp [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] at varsAnnotated
    | some indices =>
      have bodyLoc : ClosProps.everyFnLocationSome [body] := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have bodyVars : ClosProps.everyFnVarsSome [body] := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
      by_cases valid : arity ≤ s.maxApp ∧ arity ≠ 0
      · cases capture : ClosSem.lookupVars indices sourceEnv with
        | none =>
          simp [ClosSem.evaluate, valid, capture] at run
          exact False.elim (noTypeError run.1.symm)
        | some sourceValues =>
          simp [ClosSem.evaluate, valid, capture] at run
          rcases run with ⟨rfl, rfl⟩
          cases bodyCompile : compileExpHOL s.maxApp body aux with
          | mk targetBody auxBody =>
            have bodyCompiled : compileExpsHOL s.maxApp [body] aux = ([targetBody], auxBody) := by
              rw [compileExps_eq_list]
              simp [compileExpListHOL, bodyCompile]
            let entry := (label + numStubs s.maxApp, arity + 1,
              Bvl.Exp.let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) indices.length) targetBody)
            have wholeCompiled : compileExpsHOL s.maxApp [.fn name (some label) (some indices) arity body] aux =
                ([.op (.blockOp (.cons 30))
                  ((mkLabel (label + numStubs s.maxApp) :: mkConst (arity - 1) :: indices.map Bvl.Exp.var).reverse)],
                  entry :: auxBody) := by
              rw [compileExps_eq_list]
              simp [compileExpListHOL, compileExpHOL, bodyCompile, entry]
            have equal := compile.symm.trans wholeCompiled
            cases equal
            have entryLookup := installed entry (by simp)
            have bodyInstalled : codeInstalled auxBody t.code := by
              intro next member
              exact installed next (by simp [member])
            obtain ⟨targetValues, targetCapture, valuesRel, lengthEq⟩ :=
              lookupVars_related indices sourceEnv targetEnv sourceValues envRelated capture
            have targetLookup : sptLookup (label + numStubs s.maxApp) t.code =
                some (arity + 1, .let ((List.range arity).map Bvl.Exp.var ++
                  freeLet (.var arity) sourceValues.length) targetBody) := by
              simpa [entry, lengthEq] using entryLookup
            have closureRel : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
                (sourceValues, targetValues) (.closure (some label) [] sourceValues arity body)
                (.block 30 (.codePtr (label + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: targetValues)) :=
              .closure valid.1 valid.2 bodyLoc bodyVars bodyCompiled bodyInstalled targetLookup
            have valueRel := vRel.closure valuesRel closureRel
            refine ⟨0, .val [.block 30 (.codePtr (label + numStubs s.maxApp) ::
              .number (Int.ofNat (arity - 1)) :: targetValues)], { t with clock := s.clock }, f,
              ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
            · simpa using evaluate_closure_block indices targetEnv { t with clock := s.clock } targetValues
                (label + numStubs s.maxApp) (arity - 1) targetCapture ⟨_, targetLookup⟩
            · exact List.Forall₂.cons valueRel .nil
            · exact (stateRel_clock f s t s.clock).1.mpr states
            · intro key value lookup; exact lookup
            · intro key value lookup fresh; exact ⟨lookup, fresh⟩
      · simp [ClosSem.evaluate, valid] at run
        exact False.elim (noTypeError run.1.symm)

end Flapjack.Compiler.Backend.ClosToBvl
