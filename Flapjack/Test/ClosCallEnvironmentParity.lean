module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.Environment
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
public import Flapjack.Compiler.Backend.ClosCall.Proofs.RecClosure
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeIncludes
public import Flapjack.Compiler.Backend.Semantics.ClosProps.RefRelations

@[expose] public section

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
      simpa [Flapjack.holALookup] using lookup
    · simp [Flapjack.holALookup, equal] at lookup

example : ¬stateExtends ((.ln, [(1, 2)]) : Flapjack.Spt Unit × List (Nat × Nat))
    (.ln, [(1, 3), (1, 2)]) := by
  simp [stateExtends]

example : ¬stateExtends ((.ln, [(1, 2)]) : Flapjack.Spt Unit × List (Nat × Nat))
    (.ln, [(1, 3)]) := by
  intro extension
  have lookup := extension.2.1 1 2
  simp [Flapjack.holALookup] at lookup

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
    simpa [Flapjack.holALookup, singletonCode, Flapjack.HolFiniteMapExact.update,
      Flapjack.FUPDATE] using lookup
  · simp [Flapjack.holALookup, eq] at lookup

example : ¬codeIncludes [(1, 3)] singletonCode := by
  intro included
  have lookup := included 1 3
  simp [Flapjack.holALookup, singletonCode, Flapjack.HolFiniteMapExact.update,
    Flapjack.FUPDATE] at lookup

example : codeIncludes [(1, 2), (1, 3)] singletonCode := by
  intro key value lookup
  by_cases eq : key = 1
  · subst key
    simpa [Flapjack.holALookup, singletonCode, Flapjack.HolFiniteMapExact.update,
      Flapjack.FUPDATE] using lookup
  · simp [Flapjack.holALookup, eq] at lookup

-- A generated entry takes precedence over an older entry with the same label.
example : Flapjack.holALookup
    (codeList 10 [(1, .var .none 0)] (.ln, [(11, 2, .var .none 9)])).2 11 =
    some (1, .var .none 0) := by
  simp [codeList, Flapjack.holALookup]

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

end Flapjack.Test.ClosCallEnvironmentParity
