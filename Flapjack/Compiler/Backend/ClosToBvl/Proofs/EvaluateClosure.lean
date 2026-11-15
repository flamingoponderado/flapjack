module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

@[expose] public section

/-! Captured-environment facts for the closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- Convert the source equality outcome to the BVL result used in this proof. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "eq_res_def"]
def eqRes {α : Type} : EqResult → Result (List BvlSem.Value) α
  | .val b => .val [BvlSem.boolValue b]
  | .typeError => .err (.abort .typeError)

/-- Converting an equality outcome cannot yield a timeout. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "eq_res_not_timeout"]
theorem eqResNotTimeout {α : Type} (x : EqResult) :
    (eqRes x : Result (List BvlSem.Value) α) ≠ .err (.abort .timeoutError) := by
  cases x <;> simp [eqRes]

namespace FreshRefsCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end FreshRefsCarrier

/-- Every BVL state has a natural reference outside its finite domain. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "EXISTS_NOT_IN_refs"
  (fmap_as_finite_support := [refs])]
theorem existsNotInRefs {C F : Type} (t1 : Flapjack.Compiler.Backend.BvlSem.State C F) :
    ∃ x, x ∉ t1.refs.domain := by
  obtain ⟨x, unused⟩ := BvlSem.unusedRef_exists t1.refs
  refine ⟨x, ?_⟩
  change ¬ (t1.refs.lookup x ≠ none)
  exact fun present => present unused

/-- A closure tag returns true; other block tags evaluate the fallback. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_check_closure"
  (fmap_as_finite_support := [refs])]
theorem evaluateCheckClosure {C F : Type} (n : Nat) (env : List BvlSem.Value) (t : Nat)
    (vs : List BvlSem.Value) (e : Bvl.Exp) (s : Flapjack.Compiler.Backend.BvlSem.State C F)
    (premises : n < env.length ∧ holEl n env = .block t vs) :
    BvlSem.evaluate [checkClosure n e] env s =
      if t = BackendCommon.closureTag ∨ t = BackendCommon.partialAppTag then
        (eqRes (.val true), s)
      else BvlSem.evaluate [e] env s := by
  obtain ⟨bound, selected⟩ := premises
  have lookup : env[n]? = some (.block t vs) := by
    rw [holEl_eq_getElem n env bound] at selected
    rw [List.getElem?_eq_getElem bound, selected]
  by_cases h : t = 30 <;> by_cases h2 : t = 31 <;>
    simp [h, h2, checkClosure, BvlSem.asBool, BackendCommon.boolToTag, BackendCommon.trueTag, BackendCommon.falseTag, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock,
    BvlSem.boolValue, BackendCommon.closureTag, BackendCommon.partialAppTag, Bvl.boolExp, eqRes, lookup]

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

namespace LookupVarsCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end LookupVarsCarrier

/-- Related variable selections evaluate to related values in any BVL state. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "lookup_vars_IMP2"
  (fmap_as_finite_support_relation := [BvlSem.State.refs, f, refs])]
theorem lookupVarsImp2 {C F : Type} (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (vs : List Nat) (env : List ClosSem.Value) (xs : List ClosSem.Value) (env2 : List BvlSem.Value)
    (premises : ClosSem.lookupVars vs env = some xs ∧ envRel maxApp f refs code env env2) :
    ∃ ys, (∀ t1 : BvlSem.State C F, BvlSem.evaluate (vs.map Bvl.Exp.var) env2 t1 = (.val ys, t1)) ∧
      List.Forall₂ (vRel maxApp f refs code) xs ys ∧ vs.length = xs.length := by
  obtain ⟨ys, selected, related, length⟩ := lookupVars_related vs env env2 xs premises.2 premises.1
  exact ⟨ys, fun t1 => evaluate_vars vs env2 t1 ys selected, related, length⟩

/-- A successful source selection has a related target evaluation in the given state. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "lookup_vars_IMP"
  (fmap_as_finite_support_relation := [BvlSem.State.refs, f, refs])]
theorem lookupVarsImp {C F : Type} (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (vs : List Nat) (env : List ClosSem.Value) (xs : List ClosSem.Value) (env2 : List BvlSem.Value)
    (t1 : BvlSem.State C F)
    (premises : ClosSem.lookupVars vs env = some xs ∧ envRel maxApp f refs code env env2) :
    ∃ ys, BvlSem.evaluate (vs.map Bvl.Exp.var) env2 t1 = (.val ys, t1) ∧
      List.Forall₂ (vRel maxApp f refs code) xs ys ∧ vs.length = xs.length := by
  obtain ⟨ys, run, related, length⟩ := lookupVarsImp2 (C := C) (F := F) maxApp f refs code vs env xs env2 premises
  exact ⟨ys, run t1, related, length⟩

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

/-- Variable evaluation may be prefixed to a successful target expression
list, preserving its final state and concatenating its values. -/
theorem evaluate_vars_append {C F : Type} (indices : List Nat) (env : List BvlSem.Value)
    (state final : BvlSem.State C F) (values more : List BvlSem.Value) (tail : List Bvl.Exp)
    (lookup : ClosSem.lookupVars indices env = some values)
    (tailRun : BvlSem.evaluate tail env state = (.val more, final)) :
    BvlSem.evaluate (indices.map Bvl.Exp.var ++ tail) env state = (.val (values ++ more), final) := by
  change BvlSem.evaluateTuple (indices.map Bvl.Exp.var ++ tail, env, state) = _
  rw [BvlProps.evaluateAppend]
  simp [BvlSem.evaluateTuple, evaluate_vars indices env state values lookup, tailRun]

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
    [.number (Int.ofNat arity), .codePtr label] [mkConst arity, mkLabel label] reversed tailRun
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
