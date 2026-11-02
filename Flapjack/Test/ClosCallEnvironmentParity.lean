import Flapjack.Compiler.Backend.ClosCall.Proofs.Environment
import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosure
import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeIncludes
import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosureRelation
import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation
import Flapjack.Compiler.Backend.ClosCall.Proofs.PrimitiveEquality
import Flapjack.Compiler.Backend.Semantics.ClosProps.RefRelations
import Flapjack.Compiler.Backend.ClosCall.Proofs.RecursiveInvariant

/-! Replay binder and environment cases captured from CakeML/HOL. -/
namespace Flapjack.Test.ClosCallEnvironmentParity
open Flapjack.Compiler.Backend ClosCall ClosLang ClosProps
open Flapjack.Basis.Pure.MlString

private def posCases : List ClosLang.Exp :=
  [.let .none [.var .none 2] (.var .none 2),
   .fn (ofString "f") none none 2 (.var .none 2),
   .letrec [ofString "f", ofString "g"] (some 10) none
     [(1, .var .none 3), (0, .var .none 1)] (.var .none 0),
   .handle .none (.var .none 2) (.var .none 1)]

private def negCases : List ClosLang.Exp :=
  [.let .none [.var .none 2] (.var .none 1),
   .fn (ofString "f") none none 2 (.var .none 1),
   .letrec [ofString "f", ofString "g"] (some 10) none
     [(1, .var .none 1), (0, .var .none 1)] (.var .none 0),
   .handle .none (.var .none 2) (.var .none 0)]

example : freeVars 1 [posCases[0]] ∧ freeVars 0 [posCases[1]] ∧
    freeVars 0 [posCases[2]] ∧ freeVars 0 [posCases[3]] := by
  simp [posCases, freeVars, freeVarExp, freeVarFuns]

example : ¬freeVars 1 [negCases[0]] ∧ ¬freeVars 0 [negCases[1]] ∧
    ¬freeVars 0 [negCases[2]] ∧ ¬freeVars 0 [negCases[3]] := by
  simp [negCases, freeVars, freeVarExp, freeVarFuns]

example : envRel (· = ·) ([1, 2] : List Nat) [1] 0 [(0, .var .none 0)] := by
  simp [envRel, freeVar, freeVars, freeVarExp]

example : ¬envRel (· = ·) ([1, 2] : List Nat) [1] 0 [(0, .var .none 1)] := by
  simp [envRel, freeVar, freeVars, freeVarExp]

example : ¬envRel (· = ·) ([1, 2] : List Nat) [1, 3] 0 [] := by
  simp [envRel, List.forall₂_cons_left_iff]

example : envRel (· = ·) ([1, 2] : List Nat) [1, 2] 0 [] := by
  simp [envRel, List.forall₂_cons_left_iff]

-- `clos_call_wfg_probe.out`: adding distinct code preserves old lookup,
-- while duplicate or replaced bindings do not constitute an extension.
example : stateExtends ((.ln, [(1, 2)]) : Flapjack.Spt Unit × List (Nat × Nat))
    (.ln, [(2, 3), (1, 2)]) := by
  refine ⟨?_, ?_, by simp⟩
  · intro key member
    exact ⟨member, rfl⟩
  · intro key value lookup
    by_cases equal : key = 1
    · subst key
      simpa [logicalAssocLookup, List.find?] using lookup
    · simp [logicalAssocLookup, List.find?, equal] at lookup

example : ¬stateExtends ((.ln, [(1, 2)]) : Flapjack.Spt Unit × List (Nat × Nat))
    (.ln, [(1, 3), (1, 2)]) := by
  simp [stateExtends]

example : ¬stateExtends ((.ln, [(1, 2)]) : Flapjack.Spt Unit × List (Nat × Nat))
    (.ln, [(1, 3)]) := by
  intro extension
  have lookup := extension.2.1 1 2
  simp [logicalAssocLookup, List.find?] at lookup

-- `clos_call_wfg_probe.out`: nested locations precede the group's range,
-- followed by the enclosing body; missing locations use the source default.
example : codeLocations [.letrec [ofString "f", ofString "g"] (some 10) none
    [(1, .fn (ofString "h") (some 6) none 1 (.var .none 0)), (0, .var .none 0)]
    (.fn (ofString "k") (some 20) none 1 (.var .none 0))] = [6, 10, 12, 20] := by
  rfl

example : codeLocations [.fn (ofString "f") none none 1 (.var .none 0)] = [0] := by
  rfl

example : recClosureWellFormed 10 ([((true : Bool), .var .none 0)] : List (Bool × ClosLang.Exp)) := by
  simp [recClosureWellFormed, everyFnLocationSome, fnLocationSomeExp, everyFnVarsNone,
    fnVarsNoneExp, codeLocations, codeLocationsExp]

example : ¬recClosureWellFormed 10
    ([((true : Bool), .fn (ofString "f") (some 10) none 1 (.var .none 0))] : List (Bool × ClosLang.Exp)) := by
  simp [recClosureWellFormed, everyFnLocationSome, fnLocationSomeExp, everyFnVarsNone,
    fnVarsNoneExp, codeLocations, codeLocationsExp, Set.disjoint_left]

private def singletonCode : Flapjack.HolFiniteMapExact Nat Nat :=
  Flapjack.HolFiniteMapExact.empty.update (1, 2)

-- `clos_call_wfg_probe.out`: lookup uses the first binding of a duplicate key.
example : codeIncludes [(1, 2)] singletonCode := by
  intro key value lookup
  by_cases eq : key = 1
  · subst key
    simpa [logicalAssocLookup, List.find?, singletonCode, Flapjack.HolFiniteMapExact.update,
      Flapjack.FUPDATE] using lookup
  · simp [logicalAssocLookup, List.find?, eq] at lookup

example : ¬codeIncludes [(1, 3)] singletonCode := by
  intro included
  have lookup := included 1 3
  simp [logicalAssocLookup, List.find?, singletonCode, Flapjack.HolFiniteMapExact.update,
    Flapjack.FUPDATE] at lookup

example : codeIncludes [(1, 2), (1, 3)] singletonCode := by
  intro key value lookup
  by_cases eq : key = 1
  · subst key
    simpa [logicalAssocLookup, List.find?, singletonCode, Flapjack.HolFiniteMapExact.update,
      Flapjack.FUPDATE] using lookup
  · simp [logicalAssocLookup, List.find?, eq] at lookup

-- The fuel-aware recursive-closure relation is inhabited for the empty group.
example (fuel loc : Nat) :
    recClosureRelFuel fuel (.ln, []) ∅ Flapjack.HolFiniteMapExact.empty loc [] [] := by
  refine ⟨(.ln, []), ?_, ?_, ?_, ?_, [], (.ln, []), ?_, Or.inl ?_⟩
  · simp [recClosureWellFormed, everyFnLocationSome, everyFnVarsNone, codeLocations]
  · constructor
    · ext label
      simp only [Set.mem_ofPred_eq, List.map_nil, List.not_mem_nil, false_iff]
      rintro ⟨key, member, _⟩
      change Flapjack.sptDomain (.ln : Flapjack.NumSet) key at member
      simp [Flapjack.sptDomain, Flapjack.sptLookup] at member
    · simp
  · simp [codeLocations]
  · simp
  · cases fuel <;> rfl
  · refine ⟨?_, ⟨.none, 0, rfl⟩, ?_, ?_, ?_⟩
    · exact List.Forall₂.nil
    · apply stateExtends_refl
      simp [codeList]
    · simp [groupLocationsCovered, codeLocations]
    · simp [codeIncludes, codeList, logicalAssocLookup_nil]

private def closedGroup : List (Nat × ClosLang.Exp) := [(1, .var .none 0)]
private def closedGroupInitial : State := (.ln, [])
private def closedGroupAfter : State := insertEach 10 1 closedGroupInitial
private def closedGroupResult : State := codeList 10 closedGroup closedGroupAfter
private def closedGroupCode : Flapjack.HolFiniteMapExact Nat (Nat × ClosLang.Exp) :=
  Flapjack.HolFiniteMapExact.empty.update (11, (1, .var .none 0))

-- Distinct locations for a two-function group imply the group invariant.
example (names : List Flapjack.Basis.Pure.MlString.MlString) :
    recClosureWellFormed 10 [(1, .var .none 0), (2, .var .none 1)] := by
  have invariants := letrec_source_invariants names 10
    [(1, .var .none 0), (2, .var .none 1)] (.var .none 2) closedGroupInitial
  apply (invariants ?_ ?_ ?_ ?_).1
  · simp [everyFnLocationSome, fnLocationSomeExp, fnLocationSomeFuns]
  · simp [everyFnVarsNone, fnVarsNoneExp, fnVarsNoneFuns]
  · simp [codeLocations, codeLocationsExp, codeLocationsFuns, List.range_succ]
  · simp [LabelsFresh, closedGroupInitial]

-- A real closed group is related to its generated direct-call stub and code.
private theorem closedGroupRelation : recClosureRelFuel 5 closedGroupResult ∅ closedGroupCode 10 closedGroup
    [(1, .call .none 0 11 [.var .none 0])] := by
  have result := callsFuel_fn_closed_source 4 (Flapjack.Basis.Pure.MlString.ofString "") 10 1
    (.var .none 0) (.var .none 0) closedGroupInitial closedGroupAfter closedGroupResult ∅ closedGroupCode
  apply result ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ |>.2
  · rfl
  · simp [freeVarExp]
  · constructor
    · ext label
      simp only [closedGroupInitial, Set.mem_ofPred_eq, List.map_nil, List.not_mem_nil, false_iff]
      rintro ⟨key, member, _⟩
      change Flapjack.sptDomain (.ln : Flapjack.NumSet) key at member
      simp [Flapjack.sptDomain, Flapjack.sptLookup] at member
    · simp [closedGroupInitial]
  · simp [everyFnLocationSome, fnLocationSomeExp]
  · simp [everyFnVarsNone, fnVarsNoneExp]
  · simp [codeLocations, codeLocationsExp]
  · simp [LabelsFresh, closedGroupInitial]
  · apply stateExtends_refl
    simp [closedGroupResult, closedGroup, closedGroupAfter, closedGroupInitial, codeList, insertEach]
  · simp [codeLocations, codeLocationsExp, closedGroupAfter, closedGroupInitial, insertEach,
      Flapjack.sptDomain, Flapjack.sptLookup, Flapjack.sptInsert]
  · intro key value lookup
    by_cases equal : key = 11
    · subst key
      simpa [closedGroupAfter, codeList, logicalAssocLookup, List.find?,
        closedGroupCode, Flapjack.HolFiniteMapExact.update, Flapjack.FUPDATE] using lookup
    · simp [closedGroupAfter, closedGroupInitial, codeList, insertEach,
        logicalAssocLookup, List.find?, equal] at lookup

-- A group with a captured variable follows the open-closure alternative.
private theorem openGroupRelation : recClosureRelFuel 5 (.ln, []) {10} Flapjack.HolFiniteMapExact.empty 10
    [(1, .var .none 1)] [(1, .var .none 1)] := by
  have result := callsFuel_fn_open_source 4 (Flapjack.Basis.Pure.MlString.ofString "") 10 1
    (.var .none 1) (.var .none 1) (.var .none 1)
    (.ln, []) (insertEach 10 1 (.ln, [])) (.ln, []) (.ln, []) {10} Flapjack.HolFiniteMapExact.empty
  apply result ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ |>.2
  · rfl
  · simp [freeVarExp]
  · rfl
  · constructor
    · ext label
      simp only [Set.mem_ofPred_eq, List.map_nil, List.not_mem_nil, false_iff]
      rintro ⟨key, member, _⟩
      change Flapjack.sptDomain (.ln : Flapjack.NumSet) key at member
      simp [Flapjack.sptDomain, Flapjack.sptLookup] at member
    · simp
  · simp [everyFnLocationSome, fnLocationSomeExp]
  · simp [everyFnVarsNone, fnVarsNoneExp]
  · simp [codeLocations, codeLocationsExp]
  · simp [LabelsFresh]
  · apply stateExtends_refl
    simp
  · simp [codeLocations, codeLocationsExp]
  · simp [codeIncludes, logicalAssocLookup_nil]

example : ValueRelFuel 5 closedGroupResult ∅ closedGroupCode
    (.closure (some 10) [] [] 1 (.var .none 0))
    (.closure (some 10) [] [] 1 (.call .none 0 11 [.var .none 0])) := by
  exact .closure closedGroupRelation .nil (.equalLength rfl .nil)

-- A recursive group binds related recursive closures before its body runs.
example {C F : Type} (names : List Flapjack.Basis.Pure.MlString.MlString)
    (source : ClosSem.State (Flapjack.NumSet × C) F) (target : ClosSem.State C F)
    (states : StateRelFuel 5 closedGroupResult ∅ source target)
    (targetCode : target.code = closedGroupCode) (arityOk : 1 ≤ source.maxApp) :
    ∃ result final,
      ClosSem.evaluate [.letrec names (some 10) none
        [(1, .call .none 0 11 [.var .none 0])] (.var .none 0)] [] target = (result, final) ∧
      Flapjack.SemanticPrimitivesProps.resultRel
        (List.Forall₂ (ValueRelFuel 5 closedGroupResult ∅ final.code))
        (ValueRelFuel 5 closedGroupResult ∅ final.code)
        (.val [.recclosure (some 10) [] [] closedGroup 0]) result ∧
      StateRelFuel 5 closedGroupResult ∅ source final ∧
      (∀ key value, target.code.lookup key = some value → final.code.lookup key = some value) := by
  apply evaluate_letrec_fuel 5 closedGroupResult ∅ names 10 closedGroup
    [(1, .call .none 0 11 [.var .none 0])] (.var .none 0) (.var .none 0)
    (exprSimFuel_var 5 closedGroupResult ∅ .none 0) [] [] source target
    (.val [.recclosure (some 10) [] [] closedGroup 0]) source
  · simp [ClosSem.evaluate, closedGroup, arityOk]
  · simp
  · exact .equalLength rfl .nil
  · exact states
  · simpa [targetCode] using closedGroupRelation

-- Creating a closed function produces the extracted direct-call closure.
example {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (source : ClosSem.State (Flapjack.NumSet × C) F) (target : ClosSem.State C F)
    (states : StateRelFuel 5 closedGroupResult ∅ source target)
    (targetCode : target.code = closedGroupCode) (arityOk : 1 ≤ source.maxApp) :
    ∃ result final,
      ClosSem.evaluate [.fn name (some 10) none 1 (.call .none 0 11 [.var .none 0])] [] target = (result, final) ∧
      Flapjack.SemanticPrimitivesProps.resultRel
        (List.Forall₂ (ValueRelFuel 5 closedGroupResult ∅ final.code))
        (ValueRelFuel 5 closedGroupResult ∅ final.code)
        (.val [.closure (some 10) [] [] 1 (.var .none 0)]) result ∧
      StateRelFuel 5 closedGroupResult ∅ source final ∧
      (∀ key value, target.code.lookup key = some value → final.code.lookup key = some value) := by
  apply evaluate_fn_fuel 5 closedGroupResult ∅ name 10 1 (.var .none 0)
    (.call .none 0 11 [.var .none 0]) [] [] source target
    (.val [.closure (some 10) [] [] 1 (.var .none 0)]) source
  · simp [ClosSem.evaluate, arityOk]
  · simp
  · exact .equalLength rfl .nil
  · exact states
  · simpa [targetCode, closedGroup] using closedGroupRelation

-- The function relation is derived from the pass run, without supplying it
-- as an assumption to the evaluation simulation.
example {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (source : ClosSem.State (Flapjack.NumSet × C) F) (target : ClosSem.State C F)
    (states : StateRelFuel 5 closedGroupResult ∅ source target)
    (targetCode : target.code = closedGroupCode) (arityOk : 1 ≤ source.maxApp) :
    ∃ result final,
      ClosSem.evaluate [.fn name (some 10) none 1 (.call .none 0 11 [.var .none 0])] [] target = (result, final) ∧
      Flapjack.SemanticPrimitivesProps.resultRel
        (List.Forall₂ (ValueRelFuel 5 closedGroupResult ∅ final.code))
        (ValueRelFuel 5 closedGroupResult ∅ final.code)
        (.val [.closure (some 10) [] [] 1 (.var .none 0)]) result ∧
      StateRelFuel 5 closedGroupResult ∅ source final ∧
      (∀ key value, target.code.lookup key = some value → final.code.lookup key = some value) := by
  apply callsFuel_fn_evaluate 4 name 10 1 (.var .none 0)
    (.fn name (some 10) none 1 (.call .none 0 11 [.var .none 0]))
    closedGroupInitial closedGroupResult closedGroupResult ∅ [] [] source target
    (.val [.closure (some 10) [] [] 1 (.var .none 0)]) source
  · simp [ClosSem.evaluate, arityOk]
  · simp
  · rfl
  · constructor
    · ext label
      simp only [closedGroupInitial, Set.mem_ofPred_eq, List.map_nil, List.not_mem_nil, false_iff]
      rintro ⟨key, member, _⟩
      change Flapjack.sptDomain (.ln : Flapjack.NumSet) key at member
      simp [Flapjack.sptDomain, Flapjack.sptLookup] at member
    · simp [closedGroupInitial]
  · simp [everyFnLocationSome, fnLocationSomeExp]
  · simp [everyFnVarsNone, fnVarsNoneExp]
  · simp [codeLocations, codeLocationsExp]
  · simp [LabelsFresh, closedGroupInitial]
  · apply stateExtends_refl
    simp [closedGroupResult, closedGroup, closedGroupAfter, closedGroupInitial, codeList, insertEach]
  · simp [codeLocations, codeLocationsExp, closedGroupResult, closedGroup, codeList,
      closedGroupAfter, closedGroupInitial, insertEach, Flapjack.sptDomain, Flapjack.sptLookup, Flapjack.sptInsert]
  · rw [targetCode]
    intro key value lookup
    by_cases equal : key = 11
    · subst key
      simpa [closedGroupResult, closedGroup, closedGroupAfter, codeList, logicalAssocLookup, List.find?,
        closedGroupCode, Flapjack.HolFiniteMapExact.update, Flapjack.FUPDATE] using lookup
    · simp [closedGroupResult, closedGroup, closedGroupAfter, closedGroupInitial, codeList, insertEach,
        logicalAssocLookup, List.find?, equal] at lookup
  · exact .equalLength rfl .nil
  · exact states

-- Extending code preserves a captured direct-call closure in an environment.
example : EnvRelFuel 5 closedGroupResult ∅
    (closedGroupCode.update (12, (1, .var .none 0)))
    [.closure (some 10) [] [] 1 (.var .none 0)]
    [.closure (some 10) [] [] 1 (.call .none 0 11 [.var .none 0])]
    0 [(0, .var .none 0)] := by
  apply envRelFuel_mono (code := closedGroupCode)
  · exact .equalLength rfl (.cons (.closure closedGroupRelation .nil (.equalLength rfl .nil)) .nil)
  · apply stateExtends_refl
    simp [closedGroupResult, closedGroup, closedGroupAfter, closedGroupInitial, codeList, insertEach]
  · exact Set.Subset.rfl
  · intro key value lookup
    by_cases same : key = 12
    · subst key
      simp [closedGroupCode, Flapjack.HolFiniteMapExact.update, Flapjack.FUPDATE] at lookup
    · simpa [Flapjack.HolFiniteMapExact.update, Flapjack.FUPDATE, Ne.symm same] using lookup

example : ValueRelFuel 5 (.ln, []) {10} Flapjack.HolFiniteMapExact.empty
    (.closure (some 10) [] [.number 42] 1 (.var .none 1))
    (.closure (some 10) [] [.number 42] 1 (.var .none 1)) := by
  exact .closure openGroupRelation .nil (.equalLength rfl (.cons (.number 42) .nil))

-- `clos_call_env_rel_probe.out`: reference relations preserve heterogeneous
-- element relations and reject different thunk modes or constructors.
example : refRel (fun (n : Nat) (b : Bool) => (n = 1) ↔ b = true)
    (.valueArray [1, 0]) (.valueArray [true, false]) := by
  simp [refRel]

example : ¬refRel (fun (n : Nat) (b : Bool) => (n = 1) ↔ b = true)
    (.thunk .evaluated 1) (.thunk .notEvaluated true) := by
  simp [refRel]

example : ¬refRel (fun (n : Nat) (b : Bool) => (n = 1) ↔ b = true)
    (.valueArray [1]) (.byteArray [1]) := by
  simp [refRel]

-- Related closures remain indistinguishable to the executable equality op.
example : Flapjack.Compiler.Backend.ClosSem.doEq
      (.closure (some 10) [] [] 1 (.var .none 0)) (.number 4) =
    Flapjack.Compiler.Backend.ClosSem.doEq
      (.closure (some 10) [] [] 1 (.call .none 0 11 [.var .none 0])) (.number 4) := by
  apply valueRelFuel_doEq 5 closedGroupResult ∅ closedGroupCode
  · exact .closure closedGroupRelation .nil (.equalLength rfl .nil)
  · exact .number 4

-- A used variable is simulated even when the source environment is longer.
example {C F : Type} (source : ClosSem.State (Flapjack.NumSet × C) F) (target : ClosSem.State C F)
    (states : StateRelFuel 5 (.ln, []) ∅ source target) :
    ∃ result final,
      ClosSem.evaluate [.var .none 0] [.number 7] target = (result, final) ∧
      Flapjack.SemanticPrimitivesProps.resultRel
        (List.Forall₂ (ValueRelFuel 5 (.ln, []) ∅ target.code))
        (ValueRelFuel 5 (.ln, []) ∅ target.code) (.val [.number 7]) result ∧
      StateRelFuel 5 (.ln, []) ∅ source final := by
  have envs : EnvRelFuel 5 (.ln, []) ∅ target.code [.number 7, .number 8] [.number 7]
      0 [(0, .var .none 0)] := by
    apply (envRelFuel_iff _ _ _ _ _ _ _ _).mpr
    simp [envRel, freeVar, freeVars, freeVarExp, ValueRelFuel.number]
  apply evaluate_var_fuel 5 (.ln, []) ∅ .none 0 [.number 7, .number 8] [.number 7]
    source target (.val [.number 7]) source
  · simp [ClosSem.evaluate]
  · simp
  · exact envs
  · exact states

-- The structural induction composes a tick with its variable body.
example {C F : Type} :
    ExprSimFuel (C := C) (F := F) 5 (.ln, []) ∅
      (.tick .none (.var .none 0)) (.tick .none (.var .none 0)) := by
  exact exprSimFuel_tick 5 (.ln, []) ∅ .none _ _ (exprSimFuel_var 5 (.ln, []) ∅ .none 0)

-- Raising a ticked variable composes the three simulations.
example {C F : Type} :
    ExprSimFuel (C := C) (F := F) 5 (.ln, []) ∅
      (.raise .none (.tick .none (.var .none 0)))
      (.raise .none (.tick .none (.var .none 0))) := by
  exact exprSimFuel_raise 5 (.ln, []) ∅ .none _ _
    (exprSimFuel_tick 5 (.ln, []) ∅ .none _ _ (exprSimFuel_var 5 (.ln, []) ∅ .none 0))

-- Condition and branch environments can use different variables.
example {C F : Type} :
    ExprSimFuel (C := C) (F := F) 5 (.ln, []) ∅
      (.ifThenElse .none (.var .none 0) (.var .none 1) (.raise .none (.var .none 2)))
      (.ifThenElse .none (.var .none 0) (.var .none 1) (.raise .none (.var .none 2))) := by
  apply exprSimFuel_if 5 (.ln, []) ∅ .none <;> try simp
  · exact exprSimFuel_var 5 (.ln, []) ∅ .none 0
  · exact exprSimFuel_var 5 (.ln, []) ∅ .none 1
  · exact exprSimFuel_raise 5 (.ln, []) ∅ .none _ _ (exprSimFuel_var 5 (.ln, []) ∅ .none 2)

-- An exception handler binds the payload before evaluating its body.
example {C F : Type} :
    ExprSimFuel (C := C) (F := F) 5 (.ln, []) ∅
      (.handle .none (.raise .none (.var .none 0)) (.var .none 1))
      (.handle .none (.raise .none (.var .none 0)) (.var .none 1)) := by
  apply exprSimFuel_handle 5 (.ln, []) ∅ .none <;> try simp
  · exact exprSimFuel_raise 5 (.ln, []) ∅ .none _ _ (exprSimFuel_var 5 (.ln, []) ∅ .none 0)
  · exact exprSimFuel_var 5 (.ln, []) ∅ .none 1

-- Sequences may use different environment slots and propagate exceptions.
example {C F : Type} :
    ExprsSimFuel (C := C) (F := F) 5 (.ln, []) ∅
      [.var .none 0, .raise .none (.var .none 1)]
      [.var .none 0, .raise .none (.var .none 1)] := by
  apply exprsSimFuel_of_forall₂ 5 (.ln, []) ∅ (by simp)
  exact .cons (exprSimFuel_var 5 (.ln, []) ∅ .none 0)
    (.cons (exprSimFuel_raise 5 (.ln, []) ∅ .none _ _ (exprSimFuel_var 5 (.ln, []) ∅ .none 1)) .nil)

-- The body can refer past two newly bound values into the outer environment.
example {C F : Type} :
    ExprSimFuel (C := C) (F := F) 5 (.ln, []) ∅
      (.let .none [.var .none 0, .var .none 1] (.var .none 2))
      (.let .none [.var .none 0, .var .none 1] (.var .none 2)) := by
  apply exprSimFuel_let 5 (.ln, []) ∅ .none <;> try simp
  · apply exprsSimFuel_of_forall₂ 5 (.ln, []) ∅ (by simp)
    exact .cons (exprSimFuel_var 5 (.ln, []) ∅ .none 0)
      (.cons (exprSimFuel_var 5 (.ln, []) ∅ .none 1) .nil)
  · exact exprSimFuel_var 5 (.ln, []) ∅ .none 2

end Flapjack.Test.ClosCallEnvironmentParity
