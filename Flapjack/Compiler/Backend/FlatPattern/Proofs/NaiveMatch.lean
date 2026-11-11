module

public import Flapjack.SemanticPrimitivesProps.Literals
public import Flapjack.Compiler.Backend.FlatPattern.Proofs.PatternRowsSame
public import Flapjack.Compiler.Backend.FlatProps.PatternList
public import Flapjack.Compiler.Backend.FlatPattern.Proofs.BranchEvaluation
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Evaluation facts for the naive pattern dispatcher. The clocked evaluator
remains pending source and carrier review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.SemanticPrimitivesHOL (storeLookup)
open Flapjack.SemanticPrimitivesProps (litSameType_refl litSameType_sym)

/-- Evaluating the flat Boolean expression yields the corresponding value. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "evaluate_Bool"]
theorem evaluate_bool {C F : Type}
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (trace : Tra) (b : Bool) :
    FlatSem.evaluate env state [FlatLang.mkBool trace b] = (state, .val [FlatSem.boolValue b]) := by
  cases b <;> simp [FlatSem.evaluate, FlatLang.mkBool, FlatSem.boolValue]

/-- The Boolean result of a successful pattern test; a type error has no
Boolean result. -/
private def matchDecision {A : Type} : Flapjack.SemanticPrimitivesHOL.MatchResult A → Option Bool
  | .typeError => none
  | .noMatch => some false
  | .match _ => some true

/-- Both parts of a pattern-list match are checked for type errors, even if
an earlier pattern did not match. -/
private def combineMatchDecisions : Option Bool → Option Bool → Option Bool
  | some first, some second => some (first && second)
  | _, _ => none

/-- A work-list guard returns the same Boolean as the pattern matcher when
all input expressions evaluate purely and matching does not raise a type error. -/
private def NaiveListCorrect {C F : Type} (trace : Tra) (todo : List (FlatLang.Pat × FlatLang.Exp)) : Prop :=
  ∀ (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (values : List FlatSem.Value) (bindings : List (VarN × FlatSem.Value)) (answer : Bool),
    List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
      (todo.map Prod.snd) values →
    matchDecision (FlatSem.pmatchList state (todo.map Prod.fst) values bindings) = some answer →
    FlatSem.evaluate env state [naivePatternMatch trace todo] = (state, .val [FlatSem.boolValue answer])

/-- Removing an as-pattern wrapper preserves the work-list match decision. -/
private theorem pmatchList_as_decision {C F : Type} (state : FlatSem.State C F) (pattern : FlatLang.Pat)
    (name : VarN) (rest : List FlatLang.Pat) (value : FlatSem.Value) (values : List FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) :
    matchDecision (FlatSem.pmatchList state (.pas pattern name :: rest) (value :: values) bindings) =
      matchDecision (FlatSem.pmatchList state (pattern :: rest) (value :: values) ((name, value) :: bindings)) := by
  cases head : FlatSem.pmatch state pattern value ((name, value) :: bindings) with
  | typeError => simp [FlatSem.pmatchList, FlatSem.pmatch, head, matchDecision]
  | «match» next => simp [FlatSem.pmatchList, FlatSem.pmatch, head]
  | noMatch =>
    have tail : matchDecision (FlatSem.pmatchList state rest values bindings) =
        matchDecision (FlatSem.pmatchList state rest values ((name, value) :: bindings)) := by
      cases original : FlatSem.pmatchList state rest values bindings with
      | noMatch =>
        have other := FlatProps.pmatchAnyNoMatch.2 state rest values bindings original ((name, value) :: bindings)
        simp [other, matchDecision]
      | typeError =>
        have other := FlatProps.pmatchAnyError.2 state rest values bindings original ((name, value) :: bindings)
        simp [other, matchDecision]
      | «match» result =>
        obtain ⟨result', other⟩ := FlatProps.pmatchAnyMatch.2 state rest values bindings result original ((name, value) :: bindings)
        simp [other, matchDecision]
    cases left : FlatSem.pmatchList state rest values bindings <;>
      cases right : FlatSem.pmatchList state rest values ((name, value) :: bindings) <;>
      simp_all [FlatSem.pmatchList, FlatSem.pmatch, matchDecision]

/-- The alias case reuses the nested work-list simulation. -/
private theorem naiveList_as {C F : Type} (trace : Tra) (pattern : FlatLang.Pat) (name : VarN)
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

/-- A Boolean value selects its corresponding conditional branch. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "do_if_Boolv"]
theorem doIf_bool {A : Type} (b : Bool) (yes no : A) :
    FlatSem.doIf (FlatSem.boolValue b) yes no = some (if b then yes else no) := by
  cases b <;> simp [FlatSem.doIf, FlatSem.boolValue, FlatLang.boolId, boolToTag, trueTag, falseTag]

/-- A conditional with a pure Boolean guard evaluates its selected branch. -/
theorem evaluate_if_pure_bool {C F : Type} (trace : Tra) (guard yes no : FlatLang.Exp)
    (b : Bool) (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (pure : FlatSem.evaluate env state [guard] = (state, .val [FlatSem.boolValue b])) :
    FlatSem.evaluate env state [.if_ trace guard yes no] =
      FlatSem.evaluate env state [if b then yes else no] := by
  simp [FlatSem.evaluate, pure, FlatSem.fixClock]
  rw [doIf_bool]

/-- Equality of same-typed literal values evaluates to their Boolean equality. -/
theorem evaluate_literal_equality {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (actual lit : Lit)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.litv actual]))
    (sameType : Flapjack.SemanticPrimitivesHOL.litSameType actual lit = true) :
    FlatSem.evaluate env state [.app trace (.src .equality) [expression, .lit trace lit]] =
      (state, .val [FlatSem.boolValue (decide (actual = lit))]) := by
  simp [FlatSem.evaluate, pure, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp,
    FlatSem.doAppNumeric, FlatSem.doEq, sameType]

/-- The generated constructor guard tests exactly the constructor tag and
field count in the evaluated value. -/
theorem evaluate_tagLenEq {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (tag actual : Nat) (typeId : FlatLang.TypeId) (expected : Nat) (fields : List FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.conv (some (actual, typeId)) fields])) :
    FlatSem.evaluate env state [.app trace (.tagLenEq tag expected) [expression]] =
      (state, .val [FlatSem.boolValue (actual == tag && fields.length == expected)]) := by
  simp [FlatSem.evaluate, pure, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat]

/-- The complete generated projection list evaluates to the constructor's
fields in order. -/
private theorem naiveChildren_pure {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)) (fields : List FlatSem.Value)
    (patterns : List FlatLang.Pat) (lengths : patterns.length = fields.length)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.conv stamp fields])) :
    List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
      ((patterns.mapIdx (fun i p => (p, FlatLang.Exp.app trace (.el i) [expression]))).map Prod.snd) fields := by
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp [lengths], ?_⟩
  intro i leftBound rightBound
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_mapIdx]
  exact evaluate_con_projection trace expression env state stamp fields i _ pure (List.getElem?_eq_getElem rightBound)

/-- When constructor stamps and arities match, expanding its fields into the
work list preserves the match decision, including later type errors. -/
private theorem pmatchList_con_expanded_decision {C F : Type} (state : FlatSem.State C F)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeGroupId)) (patterns rest : List FlatLang.Pat)
    (actual : Option (FlatLang.CtorId × FlatLang.TypeId)) (fields values : List FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value))
    (compatible : FlatSem.PmatchStampsOk stamp actual patterns.length fields.length)
    (same : stamp.map Prod.fst = actual.map Prod.fst ∧ patterns.length = fields.length) :
    matchDecision (FlatSem.pmatchList state (.pcon stamp patterns :: rest) (.conv actual fields :: values) bindings) =
      matchDecision (FlatSem.pmatchList state (patterns ++ rest) (fields ++ values) bindings) := by
  have notBad : ¬ ¬ FlatSem.PmatchStampsOk stamp actual patterns.length fields.length := fun h => h compatible
  have head : FlatSem.pmatch state (.pcon stamp patterns) (.conv actual fields) bindings =
      FlatSem.pmatchList state patterns fields bindings := by
    simp only [FlatSem.pmatch, if_neg notBad, if_pos same]
  rw [FlatProps.pmatchListAppend patterns fields rest values state bindings same.2]
  simp only [FlatSem.pmatchList, head]
  cases FlatSem.pmatchList state patterns fields bindings <;> rfl

/-- An incompatible constructor tag or arity gives a non-match unless the
remaining patterns raise a type error. -/
private theorem pmatchList_con_failed_decision {C F : Type} (state : FlatSem.State C F)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeGroupId)) (patterns rest : List FlatLang.Pat)
    (actual : Option (FlatLang.CtorId × FlatLang.TypeId)) (fields values : List FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value))
    (compatible : FlatSem.PmatchStampsOk stamp actual patterns.length fields.length)
    (different : ¬ (stamp.map Prod.fst = actual.map Prod.fst ∧ patterns.length = fields.length)) :
    matchDecision (FlatSem.pmatchList state (.pcon stamp patterns :: rest) (.conv actual fields :: values) bindings) =
      combineMatchDecisions (some false) (matchDecision (FlatSem.pmatchList state rest values bindings)) := by
  have notBad : ¬ ¬ FlatSem.PmatchStampsOk stamp actual patterns.length fields.length := fun h => h compatible
  have head : FlatSem.pmatch state (.pcon stamp patterns) (.conv actual fields) bindings = .noMatch := by
    simp only [FlatSem.pmatch, if_neg notBad, if_neg different]
  cases tail : FlatSem.pmatchList state rest values bindings <;>
    simp [FlatSem.pmatchList, head, tail, matchDecision, combineMatchDecisions]

/-- Smart conditionals agree with ordinary conditionals in flat evaluation. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "evaluate_SmartIf"]
theorem evaluate_smartIf {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state : FlatSem.State C F) (trace : Tra) (guard yes no : FlatLang.Exp) :
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
                  env state (by simpa [FlatLang.mkBool, boolToTag] using evaluate_bool env state guardTrace true)).symm
            · split
              · rename_i tagEq tagNe typeEq
                subst typeId
                subst tag
                simpa [FlatLang.mkBool, boolToTag] using
                  (evaluate_if_pure_bool trace (.con guardTrace (some (falseTag, some FlatLang.boolId)) []) yes no false
                    env state (by simpa [FlatLang.mkBool, boolToTag] using evaluate_bool env state guardTrace false)).symm
              · rfl
          · rfl

/-- Constructor work items use their recursive field guard when the source
constructor and pattern have the same tag and arity. -/
private theorem naiveList_con_matching {C F : Type} (trace : Tra)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeGroupId)) (patterns : List FlatLang.Pat)
    (expression : FlatLang.Exp) (rest : List (FlatLang.Pat × FlatLang.Exp))
    (ih : @NaiveListCorrect C F trace (patterns.mapIdx (fun i p => (p, FlatLang.Exp.app trace (.el i) [expression])) ++ rest))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (actual : Option (FlatLang.CtorId × FlatLang.TypeId)) (fields values : List FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (answer : Bool)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.conv actual fields]))
    (tailPure : List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
      (rest.map Prod.snd) values)
    (compatible : FlatSem.PmatchStampsOk stamp actual patterns.length fields.length)
    (same : stamp.map Prod.fst = actual.map Prod.fst ∧ patterns.length = fields.length)
    (decision : matchDecision (FlatSem.pmatchList state (.pcon stamp patterns :: rest.map Prod.fst)
      (.conv actual fields :: values) bindings) = some answer) :
    FlatSem.evaluate env state [naivePatternMatch trace ((.pcon stamp patterns, expression) :: rest)] =
      (state, .val [FlatSem.boolValue answer]) := by
  have childPure := naiveChildren_pure trace expression env state actual fields patterns same.2 pure
  have allPure : List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
      ((patterns.mapIdx (fun i p => (p, FlatLang.Exp.app trace (.el i) [expression])) ++ rest).map Prod.snd) (fields ++ values) := by
    simp only [List.map_append]
    have appendProof : ∀ xs ys vs ws,
        List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value])) xs vs →
        List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value])) ys ws →
        List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value])) (xs ++ ys) (vs ++ ws) := by
      intro xs ys vs ws first second
      induction first with
      | nil => exact second
      | cons head tail ih => exact .cons head ih
    exact appendProof _ _ _ _ childPure tailPure
  have expanded := pmatchList_con_expanded_decision state stamp patterns (rest.map Prod.fst) actual fields values bindings compatible same
  have nestedDecision : matchDecision (FlatSem.pmatchList state
      ((patterns.mapIdx (fun i p => (p, FlatLang.Exp.app trace (.el i) [expression])) ++ rest).map Prod.fst) (fields ++ values) bindings) = some answer := by
    simpa [List.map_append, mapIdx_pair_fst] using expanded.symm.trans decision
  have nested := ih env state (fields ++ values) bindings answer allPure nestedDecision
  cases stamp with
  | none => simpa [naivePatternMatch] using nested
  | some patternTag =>
    obtain ⟨tag, group⟩ := patternTag
    cases actual with
    | none => simp at same
    | some actualTag =>
      obtain ⟨actualTag, actualType⟩ := actualTag
      have tagEq : actualTag = tag := by simpa using same.1.symm
      subst actualTag
      have guard := evaluate_tagLenEq trace expression env state tag tag actualType patterns.length fields pure
      have guardTrue : FlatSem.evaluate env state [.app trace (.tagLenEq tag patterns.length) [expression]] =
          (state, .val [FlatSem.boolValue true]) := by simpa [same.2] using guard
      have branch := evaluate_if_pure_bool trace (.app trace (.tagLenEq tag patterns.length) [expression])
        (naivePatternMatch trace (patterns.mapIdx (fun i p => (p, FlatLang.Exp.app trace (.el i) [expression])) ++ rest)) (FlatLang.mkBool trace false)
        true env state guardTrue
      simpa [naivePatternMatch, evaluate_smartIf, branch] using nested

/-- Constructor case of the recursive naive work-list simulation. -/
private theorem naiveList_con {C F : Type} (trace : Tra)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeGroupId)) (patterns : List FlatLang.Pat)
    (expression : FlatLang.Exp) (rest : List (FlatLang.Pat × FlatLang.Exp))
    (ih : @NaiveListCorrect C F trace (patterns.mapIdx (fun i p => (p, FlatLang.Exp.app trace (.el i) [expression])) ++ rest)) :
    @NaiveListCorrect C F trace ((.pcon stamp patterns, expression) :: rest) := by
  intro env state values bindings answer pure decision
  cases values with
  | nil => simp [FlatSem.pmatchList, matchDecision] at decision
  | cons value values =>
    cases pure with
    | cons first tail =>
      cases value with
      | litv _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ =>
        simp [FlatSem.pmatchList, FlatSem.pmatch, matchDecision] at decision
      | conv actual fields =>
        by_cases compatible : FlatSem.PmatchStampsOk stamp actual patterns.length fields.length
        · by_cases same : stamp.map Prod.fst = actual.map Prod.fst ∧ patterns.length = fields.length
          · exact naiveList_con_matching trace stamp patterns expression rest ih env state actual fields values
              bindings answer first tail compatible same (by simpa using decision)
          · have failed := pmatchList_con_failed_decision state stamp patterns (rest.map Prod.fst) actual fields values
              bindings compatible same
            have failedDecision : combineMatchDecisions (some false)
                (matchDecision (FlatSem.pmatchList state (rest.map Prod.fst) values bindings)) = some answer := by
              rw [← failed]
              simpa using decision
            cases stamp with
            | none => cases compatible; simp_all
            | some patternTag =>
              obtain ⟨tag, group⟩ := patternTag
              cases actual with
              | none => cases compatible
              | some actualTag =>
                obtain ⟨actualTag, actualType⟩ := actualTag
                have guard := evaluate_tagLenEq trace expression env state tag actualTag actualType patterns.length fields first
                have cond : (actualTag == tag && fields.length == patterns.length) = false := by
                  by_cases tagMatch : actualTag = tag
                  · by_cases lenMatch : fields.length = patterns.length
                    · have impossible : False := by
                        apply same
                        simp [tagMatch, lenMatch]
                      exact impossible.elim
                    · simp [tagMatch, lenMatch]
                  · simp [tagMatch]
                have guardFalse : FlatSem.evaluate env state [.app trace (.tagLenEq tag patterns.length) [expression]] =
                    (state, .val [FlatSem.boolValue false]) := by simpa [cond] using guard
                have branch := evaluate_if_pure_bool trace (.app trace (.tagLenEq tag patterns.length) [expression])
                  (naivePatternMatch trace (patterns.mapIdx (fun i p => (p, FlatLang.Exp.app trace (.el i) [expression])) ++ rest)) (FlatLang.mkBool trace false)
                  false env state guardFalse
                cases result : FlatSem.pmatchList state (rest.map Prod.fst) values bindings <;>
                  simp [result, matchDecision, combineMatchDecisions] at failedDecision
                all_goals subst answer
                all_goals simpa [naivePatternMatch, evaluate_smartIf, branch] using evaluate_bool env state trace false
        · have head : FlatSem.pmatch state (.pcon stamp patterns) (.conv actual fields) bindings = .typeError := by
            simp [FlatSem.pmatch, compatible]
          simp [FlatSem.pmatchList, head, matchDecision] at decision

/-- A pure guard that reflects a successful or failed pattern match. The
individual guard simulation is the remaining prerequisite for the dispatcher. -/
private def NaiveGuardCorrect {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value) : Prop :=
  ∀ pattern, match FlatSem.pmatch state pattern value [] with
    | .typeError => True
    | .noMatch => FlatSem.evaluate env state [naivePatternMatch trace [(pattern, expression)]] =
        (state, .val [FlatSem.boolValue false])
    | .match _ => FlatSem.evaluate env state [naivePatternMatch trace [(pattern, expression)]] =
        (state, .val [FlatSem.boolValue true])

/-- A literal work item either continues with the tail or returns false;
later type errors are still reflected in the source match decision. -/
private theorem naiveList_literal {C F : Type} (trace : Tra) (lit : Lit) (expression : FlatLang.Exp)
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
              exact litSameType_sym lit actual sameType
            have guard := evaluate_literal_equality trace expression env state actual lit first otherType
            have different : actual ≠ lit := Ne.symm same
            have branch := evaluate_if_pure_bool trace (.app trace (.src .equality) [expression, .lit trace lit])
              (naivePatternMatch trace rest) (FlatLang.mkBool trace false) false env state (by simpa [different] using guard)
            cases result : FlatSem.pmatchList state (rest.map Prod.fst) values bindings <;>
              simp [FlatSem.pmatchList, FlatSem.pmatch, same, sameType, result, matchDecision] at decision
            all_goals subst answer
            all_goals simpa [naivePatternMatch, evaluate_smartIf, branch] using evaluate_bool env state trace false
          · simp [FlatSem.pmatchList, FlatSem.pmatch, same, sameType, matchDecision] at decision

/-- Reference patterns replace their input expression with the corresponding
pure store projection before continuing through the nested work list. -/
private theorem naiveList_ref {C F : Type} (trace : Tra) (pattern : FlatLang.Pat) (expression : FlatLang.Exp)
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

open Classical in
/-- The original naive-pattern guard correctness theorem, including the
matcher result and the generated expression as explicit parameters. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "naive_pattern_match_correct"]
theorem naivePatternMatch_correct {C F : Type} (state : FlatSem.State C F)
    (env : FlatSem.Environment FlatSem.Value) :
    ∀ (trace : Tra) (todo : List (FlatLang.Pat × FlatLang.Exp)) (values : List FlatSem.Value)
      (bindings : List (VarN × FlatSem.Value)) (expression : FlatLang.Exp)
      (result : Flapjack.SemanticPrimitivesHOL.MatchResult (List (VarN × FlatSem.Value))),
      List.Forall₂ (pureEvalTo state env) (todo.map Prod.snd) values ∧
        FlatSem.pmatchList state (todo.map Prod.fst) values bindings = result ∧
        result ≠ .typeError ∧ naivePatternMatch trace todo = expression →
      pureEvalTo state env expression (FlatSem.boolValue (decide (result ≠ .noMatch))) := by
  intro trace todo values bindings expression result ⟨pure, matched, safe, rfl⟩
  have workAll (t : Tra) (xs : List (FlatLang.Pat × FlatLang.Exp)) : @NaiveListCorrect C F t xs := by
    induction xs using naivePatternMatch.induct t with
    | case1 =>
      intro env state values bindings answer pure decision
      cases values with
      | nil =>
        simp [FlatSem.pmatchList, matchDecision] at decision
        subst answer
        simpa [naivePatternMatch] using evaluate_bool env state t true
      | cons _ _ => simp [FlatSem.pmatchList, matchDecision] at decision
    | case2 expression rest ih =>
      intro env state values bindings answer pure decision
      cases values with
      | nil => simp [FlatSem.pmatchList, matchDecision] at decision
      | cons value values =>
        cases pure with
        | cons _ tail =>
          have tailDecision : matchDecision (FlatSem.pmatchList state (rest.map Prod.fst) values bindings) = some answer := by
            simpa [FlatSem.pmatchList, FlatSem.pmatch] using decision
          simpa [naivePatternMatch] using ih env state values bindings answer tail tailDecision
    | case3 expression rest name ih =>
      intro env state values bindings answer pure decision
      cases values with
      | nil => simp [FlatSem.pmatchList, matchDecision] at decision
      | cons value values =>
        cases pure with
        | cons _ tail =>
          have tailDecision : matchDecision (FlatSem.pmatchList state (rest.map Prod.fst) values ((name, value) :: bindings)) = some answer := by
            simpa [FlatSem.pmatchList, FlatSem.pmatch] using decision
          simpa [naivePatternMatch] using ih env state values ((name, value) :: bindings) answer tail tailDecision
    | case4 expression rest lit ih => exact naiveList_literal t lit expression rest ih
    | case5 expression rest patterns ih => exact naiveList_con t none patterns expression rest ih
    | case6 expression rest patterns tag group ih => exact naiveList_con t (some (tag, group)) patterns expression rest ih
    | case7 expression rest pattern name ih => exact naiveList_as t pattern name expression rest ih
    | case8 expression rest pattern ih => exact naiveList_ref t pattern expression rest ih
  have decision : matchDecision (FlatSem.pmatchList state (todo.map Prod.fst) values bindings) =
      some (decide (result ≠ .noMatch)) := by
    rw [matched]
    cases result <;> simp_all [matchDecision]
  exact workAll trace todo env state values bindings _ pure decision

/-- A pure scrutinee supplies the single-pattern guards for every row. -/
private theorem naiveGuardCorrect_of_pure {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    NaiveGuardCorrect trace expression env state value := by
  intro pattern
  have workPure : List.Forall₂ (pureEvalTo state env)
      ([(pattern, expression)].map Prod.snd) [value] := .cons pure .nil
  cases result : FlatSem.pmatch state pattern value [] with
  | typeError => simp
  | noMatch =>
    have matched : FlatSem.pmatchList state ([(pattern, expression)].map Prod.fst) [value] [] = .noMatch := by
      simp [FlatSem.pmatchList, result]
    have work := naivePatternMatch_correct state env trace [(pattern, expression)] [value] []
      (naivePatternMatch trace [(pattern, expression)]) .noMatch ⟨workPure, matched, by simp, rfl⟩
    simpa [pureEvalTo, result] using work
  | «match» bindings =>
    have matched : FlatSem.pmatchList state ([(pattern, expression)].map Prod.fst) [value] [] = .match bindings := by
      simp [FlatSem.pmatchList, result]
    have work := naivePatternMatch_correct state env trace [(pattern, expression)] [value] []
      (naivePatternMatch trace [(pattern, expression)]) (.match bindings) ⟨workPure, matched, by simp, rfl⟩
    simpa [pureEvalTo, result] using work

/-- The ordered naive dispatcher evaluates the first matching body or the
default, provided each compiled guard correctly represents its pattern. -/
private theorem naivePatternMatches_from_guards {C F : Type} (trace : Tra) (expression default : FlatLang.Exp)
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

/-- The ordered naive dispatcher selects the same body as the source matcher
when its scrutinee evaluates purely and matching does not type-error. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "naive_pattern_matches_correct"]
theorem naivePatternMatches_correct {C F : Type} (state : FlatSem.State C F)
    (env : FlatSem.Environment FlatSem.Value) :
    ∀ (trace : Tra) (expression : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
      (default output : FlatLang.Exp) (value : FlatSem.Value)
      (result : Flapjack.SemanticPrimitivesHOL.MatchResult (List (VarN × FlatSem.Value) × FlatLang.Pat × FlatLang.Exp)),
    naivePatternMatches trace expression rows default = output ∧
      pureEvalTo state env expression value ∧ FlatSem.pmatchRows rows state value = result ∧
      result ≠ .typeError →
    FlatSem.evaluate env state [output] = match result with
      | .match (_, _, body) => FlatSem.evaluate env state [body]
      | _ => FlatSem.evaluate env state [default] := by
  intro trace expression rows default output value result ⟨rfl, pure, matched, safe⟩
  have full := naivePatternMatches_from_guards trace expression default env state value
    (naiveGuardCorrect_of_pure trace expression env state value pure) rows (by simpa [matched] using safe)
  rw [matched] at full
  cases result <;> simpa using full

/-- Zipping the pattern projection with transformed bodies keeps their
original row pairing. -/
theorem zip_row_bodies {E E' : Type} (rows : List (FlatLang.Pat × E)) (f : FlatLang.Pat → E → E') :
    List.zip (rows.map Prod.fst) (rows.map fun row => f row.1 row.2) =
      rows.map (fun (pattern, body) => (pattern, f pattern body)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨pattern, body⟩ := row
    simp [ih]

/-- The compiler's naive branch-lowering path evaluates the compiled body of
the row selected by the source matcher, or the default when no row matches. -/
theorem evaluate_compilePats_naive {C F : Type} (cfg : Config) (trace : Tra) (n : Nat)
    (expression default : FlatLang.Exp) (rows : List (FlatLang.Pat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value]))
    (safe : FlatSem.pmatchRows rows state value ≠ .typeError) :
    FlatSem.evaluate env state [compilePats cfg true trace n expression default rows] =
      FlatSem.evaluate env state [match FlatSem.pmatchRows rows state value with
        | .match (_, pattern, body) => compilePatRhs trace n expression (pattern, body)
        | _ => default] := by
  let f := fun pattern body => compilePatRhs trace n expression (pattern, body)
  let mapped := rows.map (fun (pattern, body) => (pattern, f pattern body))
  let : Nonempty FlatLang.Pat := ⟨.pany⟩
  let : Nonempty FlatLang.Exp := ⟨expression⟩
  have same : rows.map Prod.fst = mapped.map Prod.fst := by simp [mapped]
  have mappedResult := pmatchRows_sameFst state value rows mapped same
  have mappedSafe : FlatSem.pmatchRows mapped state value ≠ .typeError := by
    cases h : FlatSem.pmatchRows rows state value with
    | typeError => exact (safe h).elim
    | noMatch =>
      have target : FlatSem.pmatchRows mapped state value = .noMatch := by simpa [h] using mappedResult
      simp [target]
    | «match» result =>
      obtain ⟨bindings, pattern, body⟩ := result
      simp only [h] at mappedResult
      obtain ⟨_, _, _, target⟩ := mappedResult
      simp [target]
  have dispatch := naivePatternMatches_correct state env trace expression mapped default
    (naivePatternMatches trace expression mapped default) value (FlatSem.pmatchRows mapped state value)
    ⟨rfl, pure, rfl, mappedSafe⟩
  have compiledRows : List.zip (rows.map Prod.fst) (rows.map (compilePatRhs trace n expression)) = mapped := by
    simpa [mapped, f] using zip_row_bodies rows f
  cases original : FlatSem.pmatchRows rows state value with
  | typeError => exact (safe original).elim
  | noMatch =>
    have target : FlatSem.pmatchRows mapped state value = .noMatch := by
      simpa [original] using mappedResult
    simpa [compilePats, compiledRows, mapped, f, original, target] using dispatch
  | «match» selected =>
    rcases selected with ⟨bindings, pattern, body⟩
    simp only [original] at mappedResult
    obtain ⟨i, bound, source, target⟩ := mappedResult
    have sourceBound : i < rows.length := by simpa [mapped] using bound
    have selectedRow : rows[i] = (pattern, body) := by
      simpa [Flapjack.holEl_eq_getElem i rows sourceBound] using source
    have selectedMapped : Flapjack.holEl i mapped = (pattern, f pattern body) := by
      rw [Flapjack.holEl_eq_getElem i mapped bound]
      simp [mapped, selectedRow]
    rw [selectedMapped] at target
    simpa [compilePats, compiledRows, mapped, f, original, target] using dispatch

open Classical in
/-- The naive guard agrees with a singleton pattern match. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "naive_pattern_match_correct_inst"]
theorem naivePatternMatch_correct_inst {C F : Type} (expression : FlatLang.Exp) (value : FlatSem.Value)
    (trace : Tra) (state : FlatSem.State C F) (pattern : FlatLang.Pat)
    (env : FlatSem.Environment FlatSem.Value)
    (premises : pureEvalTo state env expression value ∧
      FlatSem.pmatchList state [pattern] [value] [] ≠ .typeError) :
    FlatSem.evaluate env state [naivePatternMatch trace [(pattern, expression)]] =
      (state, .val [FlatSem.boolValue (decide (FlatSem.pmatchList state [pattern] [value] [] ≠ .noMatch))]) := by
  have pure : List.Forall₂ (pureEvalTo state env) [expression] [value] := .cons premises.1 .nil
  have result := naivePatternMatch_correct state env trace [(pattern, expression)] [value] []
    (naivePatternMatch trace [(pattern, expression)]) (FlatSem.pmatchList state [pattern] [value] [])
    ⟨by simpa using pure, rfl, premises.2, rfl⟩
  exact result

end Flapjack.Compiler.Backend.FlatPattern
