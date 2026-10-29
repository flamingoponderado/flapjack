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

/-- The Boolean result of a successful pattern test; a type error has no
Boolean result. -/
def matchDecision {A : Type} : Flapjack.SemanticPrimitivesHOL.MatchResult A → Option Bool
  | .typeError => none
  | .noMatch => some false
  | .match _ => some true

/-- A pattern-list decision does not depend on the incoming bindings. -/
theorem pmatchList_decision_independent {C F : Type} (state : FlatSem.State C F)
    (patterns : List FlatLang.Pat) (values : List FlatSem.Value)
    (left right : List (VarN × FlatSem.Value)) :
    matchDecision (FlatSem.pmatchList state patterns values left) =
      matchDecision (FlatSem.pmatchList state patterns values right) := by
  have l := pmatchList_append_bindings state patterns values [] left
  have r := pmatchList_append_bindings state patterns values [] right
  simp only [List.nil_append] at l r
  rw [l, r]
  cases FlatSem.pmatchList state patterns values [] <;> rfl

/-- A work-list guard returns the same Boolean as the pattern matcher when
all input expressions evaluate purely and matching does not raise a type error. -/
def NaiveListCorrect {C F : Type} (trace : Tra) (todo : List (FlatLang.Pat × FlatLang.Exp)) : Prop :=
  ∀ (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (values : List FlatSem.Value) (bindings : List (VarN × FlatSem.Value)) (answer : Bool),
    List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
      (todo.map Prod.snd) values →
    matchDecision (FlatSem.pmatchList state (todo.map Prod.fst) values bindings) = some answer →
    FlatSem.evaluate env state [naivePatternMatch trace todo] = (state, .val [FlatSem.boolValue answer])

/-- Removing an as-pattern wrapper preserves the work-list match decision. -/
theorem pmatchList_as_decision {C F : Type} (state : FlatSem.State C F) (pattern : FlatLang.Pat)
    (name : VarN) (rest : List FlatLang.Pat) (value : FlatSem.Value) (values : List FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) :
    matchDecision (FlatSem.pmatchList state (.pas pattern name :: rest) (value :: values) bindings) =
      matchDecision (FlatSem.pmatchList state (pattern :: rest) (value :: values) ((name, value) :: bindings)) := by
  cases head : FlatSem.pmatch state pattern value ((name, value) :: bindings) with
  | typeError => simp [FlatSem.pmatchList, FlatSem.pmatch, head, matchDecision]
  | «match» next => simp [FlatSem.pmatchList, FlatSem.pmatch, head]
  | noMatch =>
    have tail := pmatchList_decision_independent state rest values bindings ((name, value) :: bindings)
    cases left : FlatSem.pmatchList state rest values bindings <;>
      cases right : FlatSem.pmatchList state rest values ((name, value) :: bindings) <;>
      simp_all [FlatSem.pmatchList, FlatSem.pmatch, matchDecision]

/-- The empty work-list guard evaluates to true. -/
theorem naiveList_nil {C F : Type} (trace : Tra) : @NaiveListCorrect C F trace [] := by
  intro env state values bindings answer pure decision
  cases values with
  | nil =>
    simp [FlatSem.pmatchList, matchDecision] at decision
    subst answer
    simpa [naivePatternMatch] using evaluate_bool trace true env state
  | cons _ _ => simp [FlatSem.pmatchList, matchDecision] at decision

/-- Wildcards pass the work-list match and guard directly to the tail. -/
theorem naiveList_any {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (rest : List (FlatLang.Pat × FlatLang.Exp)) (ih : @NaiveListCorrect C F trace rest) :
    @NaiveListCorrect C F trace ((.pany, expression) :: rest) := by
  intro env state values bindings answer pure decision
  cases values with
  | nil => simp [FlatSem.pmatchList, matchDecision] at decision
  | cons value values =>
    cases pure with
    | cons _ tail =>
      have tailDecision : matchDecision (FlatSem.pmatchList state (rest.map Prod.fst) values bindings) = some answer := by
        simpa [FlatSem.pmatchList, FlatSem.pmatch] using decision
      simpa [naivePatternMatch] using ih env state values bindings answer tail tailDecision

/-- Variable patterns pass the work-list decision to the tail with an
additional binding, while emitting no guard code. -/
theorem naiveList_var {C F : Type} (trace : Tra) (name : VarN) (expression : FlatLang.Exp)
    (rest : List (FlatLang.Pat × FlatLang.Exp)) (ih : @NaiveListCorrect C F trace rest) :
    @NaiveListCorrect C F trace ((.pvar name, expression) :: rest) := by
  intro env state values bindings answer pure decision
  cases values with
  | nil => simp [FlatSem.pmatchList, matchDecision] at decision
  | cons value values =>
    cases pure with
    | cons _ tail =>
      have tailDecision : matchDecision (FlatSem.pmatchList state (rest.map Prod.fst) values ((name, value) :: bindings)) = some answer := by
        simpa [FlatSem.pmatchList, FlatSem.pmatch] using decision
      simpa [naivePatternMatch] using ih env state values ((name, value) :: bindings) answer tail tailDecision

/-- The alias case reuses the nested work-list simulation. -/
theorem naiveList_as {C F : Type} (trace : Tra) (pattern : FlatLang.Pat) (name : VarN)
    (expression : FlatLang.Exp) (rest : List (FlatLang.Pat × FlatLang.Exp))
    (ih : @NaiveListCorrect C F trace ((pattern, expression) :: rest)) :
    @NaiveListCorrect C F trace ((.pas pattern name, expression) :: rest) := by
  intro env state values bindings answer pure decision
  cases values with
  | nil => simp [FlatSem.pmatchList, matchDecision] at decision
  | cons value values =>
    have nested : matchDecision (FlatSem.pmatchList state (pattern :: rest.map Prod.fst)
        (value :: values) ((name, value) :: bindings)) = some answer := by
      rw [← pmatchList_as_decision state pattern name (rest.map Prod.fst) value values bindings]
      simpa using decision
    have nestedPure : List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
        (((pattern, expression) :: rest).map Prod.snd) (value :: values) := by simpa using pure
    simpa [naivePatternMatch] using ih env state (value :: values) ((name, value) :: bindings) answer nestedPure nested

/-- Literal type compatibility is reflexive and symmetric. -/
theorem litSameType_refl (lit : Lit) : Flapjack.SemanticPrimitivesHOL.litSameType lit lit = true := by
  cases lit <;> rfl

theorem litSameType_symm (left right : Lit) :
    Flapjack.SemanticPrimitivesHOL.litSameType left right = Flapjack.SemanticPrimitivesHOL.litSameType right left := by
  cases left <;> cases right <;> rfl

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

/-- Equality of same-typed literal values evaluates to their Boolean equality. -/
theorem evaluate_literal_equality {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (actual lit : Lit)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.litv actual]))
    (sameType : Flapjack.SemanticPrimitivesHOL.litSameType actual lit = true) :
    FlatSem.evaluate env state [.app trace (.src .equality) [expression, .lit trace lit]] =
      (state, .val [FlatSem.boolValue (decide (actual = lit))]) := by
  simp [FlatSem.evaluate, pure, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp,
    FlatSem.doAppNumeric, FlatSem.doEq, sameType]

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

/-- Literal guards compare same-typed literal values and return the match
result's Boolean; incompatible literal types correspond to a match error. -/
theorem naiveGuard_literal {C F : Type} (trace : Tra) (lit : Lit) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    NaiveGuardCase trace (.plit lit) expression env state value := by
  cases value with
  | litv actual =>
    by_cases same : lit = actual
    · subst actual
      have guard := evaluate_literal_equality trace expression env state lit lit pure (litSameType_refl lit)
      have branch := evaluate_if_pure_bool trace (.app trace (.src .equality) [expression, .lit trace lit])
        (FlatLang.mkBool trace true) (FlatLang.mkBool trace false) true env state (by simpa using guard)
      simpa [NaiveGuardCase, FlatSem.pmatch, naivePatternMatch, evaluate_smartIf, branch] using
        evaluate_bool trace true env state
    · by_cases typeSame : Flapjack.SemanticPrimitivesHOL.litSameType lit actual = true
      · have otherType : Flapjack.SemanticPrimitivesHOL.litSameType actual lit = true := by
          simpa [litSameType_symm actual lit] using typeSame
        have guard := evaluate_literal_equality trace expression env state actual lit pure otherType
        have different : actual ≠ lit := Ne.symm same
        have branch := evaluate_if_pure_bool trace (.app trace (.src .equality) [expression, .lit trace lit])
          (FlatLang.mkBool trace true) (FlatLang.mkBool trace false) false env state (by simpa [different] using guard)
        simpa [NaiveGuardCase, FlatSem.pmatch, same, typeSame, naivePatternMatch, evaluate_smartIf, branch] using
          evaluate_bool trace false env state
      · simp [NaiveGuardCase, FlatSem.pmatch, same, typeSame]
  | conv _ _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ =>
    simp [NaiveGuardCase, FlatSem.pmatch]

/-- A literal work item either continues with the tail or returns false;
later type errors are still reflected in the source match decision. -/
theorem naiveList_literal {C F : Type} (trace : Tra) (lit : Lit) (expression : FlatLang.Exp)
    (rest : List (FlatLang.Pat × FlatLang.Exp)) (ih : @NaiveListCorrect C F trace rest) :
    @NaiveListCorrect C F trace ((.plit lit, expression) :: rest) := by
  intro env state values bindings answer pure decision
  cases values with
  | nil => simp [FlatSem.pmatchList, matchDecision] at decision
  | cons value values =>
    cases pure with
    | cons first tail =>
      cases value with
      | conv _ _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ =>
        simp [FlatSem.pmatchList, FlatSem.pmatch, matchDecision] at decision
      | litv actual =>
        by_cases same : lit = actual
        · subst actual
          have tailDecision : matchDecision (FlatSem.pmatchList state (rest.map Prod.fst) values bindings) = some answer := by
            simpa [FlatSem.pmatchList, FlatSem.pmatch] using decision
          have tailEval := ih env state values bindings answer tail tailDecision
          have guard := evaluate_literal_equality trace expression env state lit lit first (litSameType_refl lit)
          have branch := evaluate_if_pure_bool trace (.app trace (.src .equality) [expression, .lit trace lit])
            (naivePatternMatch trace rest) (FlatLang.mkBool trace false) true env state (by simpa using guard)
          simpa [naivePatternMatch, evaluate_smartIf, branch] using tailEval
        · by_cases sameType : Flapjack.SemanticPrimitivesHOL.litSameType lit actual = true
          · have otherType : Flapjack.SemanticPrimitivesHOL.litSameType actual lit = true := by
              simpa [litSameType_symm actual lit] using sameType
            have guard := evaluate_literal_equality trace expression env state actual lit first otherType
            have different : actual ≠ lit := Ne.symm same
            have branch := evaluate_if_pure_bool trace (.app trace (.src .equality) [expression, .lit trace lit])
              (naivePatternMatch trace rest) (FlatLang.mkBool trace false) false env state (by simpa [different] using guard)
            cases result : FlatSem.pmatchList state (rest.map Prod.fst) values bindings <;>
              simp [FlatSem.pmatchList, FlatSem.pmatch, same, sameType, result, matchDecision] at decision
            all_goals subst answer
            all_goals simpa [naivePatternMatch, evaluate_smartIf, branch] using evaluate_bool trace false env state
          · simp [FlatSem.pmatchList, FlatSem.pmatch, same, sameType, matchDecision] at decision

/-- An as-pattern has the same success, non-match and error outcome as its
nested pattern, despite adding the alias to the match environment. -/
theorem naiveGuard_as {C F : Type} (trace : Tra) (pattern : FlatLang.Pat) (name : VarN)
    (expression : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (value : FlatSem.Value) (ih : NaiveGuardCase trace pattern expression env state value) :
    NaiveGuardCase trace (.pas pattern name) expression env state value := by
  have suffix := pmatch_append_bindings state pattern value [] [(name, value)]
  simp only [List.nil_append] at suffix
  cases result : FlatSem.pmatch state pattern value [] <;>
    simp_all [NaiveGuardCase, FlatSem.pmatch, naivePatternMatch, appendMatchBindings]

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

/-- Reference patterns replace their input expression with the corresponding
pure store projection before continuing through the nested work list. -/
theorem naiveList_ref {C F : Type} (trace : Tra) (pattern : FlatLang.Pat) (expression : FlatLang.Exp)
    (rest : List (FlatLang.Pat × FlatLang.Exp))
    (ih : @NaiveListCorrect C F trace ((pattern, .app trace (.el 0) [expression]) :: rest)) :
    @NaiveListCorrect C F trace ((.pref pattern, expression) :: rest) := by
  intro env state values bindings answer pure decision
  cases values with
  | nil => simp [FlatSem.pmatchList, matchDecision] at decision
  | cons value values =>
    cases pure with
    | cons first tail =>
      cases value with
      | litv _ | conv _ _ | closure _ _ _ | recclosure _ _ _ | vectorv _ =>
        simp [FlatSem.pmatchList, FlatSem.pmatch, matchDecision] at decision
      | loc flag index =>
        cases found : storeLookup index state.refs with
        | none => simp [FlatSem.pmatchList, FlatSem.pmatch, found, matchDecision] at decision
        | some entry =>
          cases entry with
          | w8array _ | varray _ | thunk _ _ =>
            simp [FlatSem.pmatchList, FlatSem.pmatch, found, matchDecision] at decision
          | refv contents =>
            have projected := evaluate_ref_projection trace expression env state flag index contents first found
            have nestedPure : List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
                (((pattern, .app trace (.el 0) [expression]) :: rest).map Prod.snd) (contents :: values) :=
              .cons projected tail
            have nestedDecision : matchDecision (FlatSem.pmatchList state
                (((pattern, .app trace (.el 0) [expression]) :: rest).map Prod.fst) (contents :: values) bindings) = some answer := by
              simpa [FlatSem.pmatchList, FlatSem.pmatch, found] using decision
            simpa [naivePatternMatch] using ih env state (contents :: values) bindings answer nestedPure nestedDecision

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
