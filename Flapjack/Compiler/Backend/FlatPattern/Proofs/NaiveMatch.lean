import Flapjack.Compiler.Backend.FlatPattern.Proofs.BranchEvaluation

/-! Evaluation facts for the naive pattern dispatcher. The clocked evaluator
remains pending source and carrier review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.SemanticPrimitivesHOL (storeLookup)

/-- Evaluating the flat Boolean expression yields the corresponding value. -/
theorem evaluate_bool {C F : Type} (trace : Tra) (b : Bool)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) :
    FlatSem.evaluate env state [FlatLang.mkBool trace b] = (state, .val [FlatSem.boolValue b]) := by
  cases b <;> simp [FlatSem.evaluate, FlatLang.mkBool, FlatSem.boolValue]

/-- Boolean values choose the expected conditional branch. -/
theorem doIf_bool {A : Type} (b : Bool) (yes no : A) :
    FlatSem.doIf (FlatSem.boolValue b) yes no = some (if b then yes else no) := by
  cases b <;> simp [FlatSem.doIf, FlatSem.boolValue, FlatLang.boolId, boolToTag, trueTag, falseTag]

/-- A conditional with a pure Boolean guard evaluates its selected branch. -/
theorem evaluate_if_pure_bool {C F : Type} (trace : Tra) (guard yes no : FlatLang.Exp)
    (b : Bool) (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (pure : FlatSem.evaluate env state [guard] = (state, .val [FlatSem.boolValue b])) :
    FlatSem.evaluate env state [.if_ trace guard yes no] =
      FlatSem.evaluate env state [if b then yes else no] := by
  cases b <;> simp [FlatSem.evaluate, pure, FlatSem.fixClock, FlatSem.doIf, FlatSem.boolValue,
    FlatLang.boolId, boolToTag, trueTag, falseTag]

/-- Smart conditionals agree with ordinary conditionals in flat evaluation. -/
theorem evaluate_smartIf {C F : Type} (trace : Tra) (guard yes no : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) :
    FlatSem.evaluate env state [FlatLang.smartIf trace guard yes no] =
      FlatSem.evaluate env state [.if_ trace guard yes no] := by
  cases guard <;> try rfl
  case con guardTrace stamp values =>
    cases values with
    | cons _ _ => cases stamp <;> simp [FlatLang.smartIf]
    | nil =>
      cases stamp with
      | none => rfl
      | some tagged =>
        obtain ⟨tag, typeId⟩ := tagged
        cases typeId with
        | none => rfl
        | some typeId =>
          simp only [FlatLang.smartIf]
          split
          · split
            · rename_i tagEq typeEq
              subst typeId
              subst tag
              simpa [FlatLang.mkBool, boolToTag] using
                (evaluate_if_pure_bool trace (.con guardTrace (some (trueTag, some FlatLang.boolId)) []) yes no true
                  env state (by simpa [FlatLang.mkBool, boolToTag] using evaluate_bool guardTrace true env state)).symm
            · split
              · rename_i tagEq tagNe typeEq
                subst typeId
                subst tag
                simpa [FlatLang.mkBool, boolToTag] using
                  (evaluate_if_pure_bool trace (.con guardTrace (some (falseTag, some FlatLang.boolId)) []) yes no false
                    env state (by simpa [FlatLang.mkBool, boolToTag] using evaluate_bool guardTrace false env state)).symm
              · rfl
          · rfl

/-- A pure guard that reflects a successful or failed pattern match. The
individual guard simulation is the remaining prerequisite for the dispatcher. -/
def NaiveGuardCorrect {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value) : Prop :=
  ∀ pattern, match FlatSem.pmatch state pattern value [] with
    | .typeError => True
    | .noMatch => FlatSem.evaluate env state [naivePatternMatch trace [(pattern, expression)]] =
        (state, .val [FlatSem.boolValue false])
    | .match _ => FlatSem.evaluate env state [naivePatternMatch trace [(pattern, expression)]] =
        (state, .val [FlatSem.boolValue true])

/-- The corresponding guard obligation for one pattern. -/
def NaiveGuardCase {C F : Type} (trace : Tra) (pattern : FlatLang.Pat) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value) : Prop :=
  match FlatSem.pmatch state pattern value [] with
  | .typeError => True
  | .noMatch => FlatSem.evaluate env state [naivePatternMatch trace [(pattern, expression)]] =
      (state, .val [FlatSem.boolValue false])
  | .match _ => FlatSem.evaluate env state [naivePatternMatch trace [(pattern, expression)]] =
      (state, .val [FlatSem.boolValue true])

/-- Wildcard and variable patterns always produce a true naive guard. -/
theorem naiveGuard_any_var {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (name : VarN) :
    NaiveGuardCase trace .pany expression env state value ∧
    NaiveGuardCase trace (.pvar name) expression env state value := by
  constructor <;> simpa [NaiveGuardCase, FlatSem.pmatch, naivePatternMatch] using evaluate_bool trace true env state

/-- Reference guards reduce to the nested guard after evaluating the same
reference projection used by the matcher. -/
theorem naiveGuard_ref {C F : Type} (trace : Tra) (pattern : FlatLang.Pat) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value]))
    (ih : ∀ expression' value', FlatSem.evaluate env state [expression'] = (state, .val [value']) →
      NaiveGuardCase trace pattern expression' env state value') :
    NaiveGuardCase trace (.pref pattern) expression env state value := by
  cases value with
  | litv _ | conv _ _ | closure _ _ _ | recclosure _ _ _ | vectorv _ => simp [NaiveGuardCase, FlatSem.pmatch]
  | loc flag index =>
    cases found : storeLookup index state.refs with
    | none => simp [NaiveGuardCase, FlatSem.pmatch, found]
    | some entry =>
      cases entry with
      | w8array _ | varray _ | thunk _ _ => simp [NaiveGuardCase, FlatSem.pmatch, found]
      | refv contents =>
        have projected := evaluate_ref_projection trace expression env state flag index contents pure found
        have nested := ih (.app trace (.el 0) [expression]) contents projected
        simpa [NaiveGuardCase, FlatSem.pmatch, naivePatternMatch, found] using nested

/-- The ordered naive dispatcher evaluates the first matching body or the
default, provided each compiled guard correctly represents its pattern. -/
theorem naivePatternMatches_from_guards {C F : Type} (trace : Tra) (expression default : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (guards : NaiveGuardCorrect trace expression env state value)
    (rows : List (FlatLang.Pat × FlatLang.Exp))
    (safe : FlatSem.pmatchRows rows state value ≠ .typeError) :
    FlatSem.evaluate env state [naivePatternMatches trace expression rows default] =
      FlatSem.evaluate env state [match FlatSem.pmatchRows rows state value with
        | .match (_, _, body) => body
        | _ => default] := by
  induction rows with
  | nil => simp [naivePatternMatches, FlatSem.pmatchRows]
  | cons row rows ih =>
    obtain ⟨pattern, body⟩ := row
    cases head : FlatSem.pmatch state pattern value [] with
    | typeError => simp [FlatSem.pmatchRows, head] at safe
    | noMatch =>
      have guard := guards pattern
      simp only [head] at guard
      have tailSafe : FlatSem.pmatchRows rows state value ≠ .typeError := by
        simpa [FlatSem.pmatchRows, head] using safe
      have branch := evaluate_if_pure_bool trace (naivePatternMatch trace [(pattern, expression)]) body
        (naivePatternMatches trace expression rows default) false env state guard
      have rest := ih tailSafe
      simpa [naivePatternMatches, evaluate_smartIf, branch, FlatSem.pmatchRows, head] using rest
    | «match» bindings =>
      have guard := guards pattern
      simp only [head] at guard
      have branch := evaluate_if_pure_bool trace (naivePatternMatch trace [(pattern, expression)]) body
        (naivePatternMatches trace expression rows default) true env state guard
      cases tail : FlatSem.pmatchRows rows state value with
      | typeError => simp [FlatSem.pmatchRows, head, tail] at safe
      | noMatch => simp [naivePatternMatches, evaluate_smartIf, branch, FlatSem.pmatchRows, head, tail]
      | «match» selected => simp [naivePatternMatches, evaluate_smartIf, branch, FlatSem.pmatchRows, head, tail]

end Flapjack.Compiler.Backend.FlatPattern
