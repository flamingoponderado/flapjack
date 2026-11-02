import Flapjack.Compiler.Backend.ClosCall.Proofs.Environment
import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosure
import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeIncludes
import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosureRelation
import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation
import Flapjack.Compiler.Backend.ClosCall.Proofs.PrimitiveEquality
import Flapjack.Compiler.Backend.Semantics.ClosProps.RefRelations
import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateIf

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

-- A real closed group is related to its generated direct-call stub and code.
private theorem closedGroupRelation : recClosureRelFuel 5 closedGroupResult ∅ closedGroupCode 10 closedGroup
    [(1, .call .none 0 11 [.var .none 0])] := by
  refine ⟨closedGroupInitial, ?_, ?_, ?_, ?_, [.var .none 0], closedGroupAfter, ?_, Or.inl ?_⟩
  · simp [closedGroup, recClosureWellFormed, everyFnLocationSome, fnLocationSomeExp,
      everyFnVarsNone, fnVarsNoneExp, codeLocations, codeLocationsExp]
  · constructor
    · ext label
      simp only [closedGroupInitial, Set.mem_ofPred_eq, List.map_nil, List.not_mem_nil, false_iff]
      rintro ⟨key, member, _⟩
      change Flapjack.sptDomain (.ln : Flapjack.NumSet) key at member
      simp [Flapjack.sptDomain, Flapjack.sptLookup] at member
    · simp [closedGroupInitial]
  · simp [closedGroupInitial]
  · simp [closedGroupInitial]
  · rfl
  · refine ⟨?_, ⟨.none, 0, rfl⟩, ?_, ?_, ?_⟩
    · simp [groupClosed, closedGroup, freeVarExp]
    · apply stateExtends_refl
      simp [closedGroup, closedGroupAfter, closedGroupInitial, codeList, insertEach]
    · simp [groupLocationsCovered, closedGroup, codeLocations, codeLocationsExp]
    · intro key value lookup
      by_cases equal : key = 11
      · subst key
        simpa [closedGroup, closedGroupAfter, codeList, logicalAssocLookup, List.find?,
          closedGroupCode, Flapjack.HolFiniteMapExact.update, Flapjack.FUPDATE] using lookup
      · simp [closedGroup, closedGroupAfter, closedGroupInitial, codeList, insertEach,
          logicalAssocLookup, List.find?, equal] at lookup

-- A group with a captured variable follows the open-closure alternative.
private theorem openGroupRelation : recClosureRelFuel 5 (.ln, []) {10} Flapjack.HolFiniteMapExact.empty 10
    [(1, .var .none 1)] [(1, .var .none 1)] := by
  refine ⟨(.ln, []), ?_, ?_, ?_, ?_, [.var .none 1], insertEach 10 1 (.ln, []), ?_, Or.inr ?_⟩
  · simp [recClosureWellFormed, everyFnLocationSome, fnLocationSomeExp,
      everyFnVarsNone, fnVarsNoneExp, codeLocations, codeLocationsExp]
  · constructor
    · ext label
      simp only [Set.mem_ofPred_eq, List.map_nil, List.not_mem_nil, false_iff]
      rintro ⟨key, member, _⟩
      change Flapjack.sptDomain (.ln : Flapjack.NumSet) key at member
      simp [Flapjack.sptDomain, Flapjack.sptLookup] at member
    · simp
  · simp
  · simp
  · rfl
  · refine ⟨?_, [.var .none 1], (.ln, []), rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [groupClosed, freeVarExp]
    · apply stateExtends_refl
      simp
    · simp [groupLocationsCovered, codeLocations, codeLocationsExp]
    · simp
    · simp [codeIncludes, logicalAssocLookup_nil]

example : ValueRelFuel 5 closedGroupResult ∅ closedGroupCode
    (.closure (some 10) [] [] 1 (.var .none 0))
    (.closure (some 10) [] [] 1 (.call .none 0 11 [.var .none 0])) := by
  exact .closure closedGroupRelation .nil (.equalLength rfl .nil)

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

end Flapjack.Test.ClosCallEnvironmentParity
