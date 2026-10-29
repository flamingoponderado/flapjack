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

/-- Both parts of a pattern-list match are checked for type errors, even if
an earlier pattern did not match. -/
def combineMatchDecisions : Option Bool → Option Bool → Option Bool
  | some first, some second => some (first && second)
  | _, _ => none

/-- Matching appended pattern and value lists combines their decisions while
preserving a type error from either part. -/
theorem pmatchList_append_decision {C F : Type} (state : FlatSem.State C F)
    (left right : List FlatLang.Pat) (leftValues rightValues : List FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (lengths : left.length = leftValues.length) :
    matchDecision (FlatSem.pmatchList state (left ++ right) (leftValues ++ rightValues) bindings) =
      combineMatchDecisions (matchDecision (FlatSem.pmatchList state left leftValues bindings))
        (matchDecision (FlatSem.pmatchList state right rightValues bindings)) := by
  induction left generalizing leftValues bindings with
  | nil =>
    cases leftValues with
    | nil =>
      cases h : FlatSem.pmatchList state right rightValues bindings <;>
        simp [FlatSem.pmatchList, matchDecision, combineMatchDecisions, h]
    | cons _ _ => simp at lengths
  | cons pattern left ih =>
    cases leftValues with
    | nil => simp at lengths
    | cons value leftValues =>
      have tailLengths : left.length = leftValues.length := by simpa using lengths
      cases head : FlatSem.pmatch state pattern value bindings with
      | typeError => simp [FlatSem.pmatchList, head, matchDecision, combineMatchDecisions]
      | «match» next =>
        have recurse := ih leftValues next tailLengths
        have independent := pmatchList_decision_independent state right rightValues next bindings
        simpa [FlatSem.pmatchList, head, independent] using recurse
      | noMatch =>
        have recurse := ih leftValues bindings tailLengths
        cases firstResult : FlatSem.pmatchList state left leftValues bindings <;>
          cases full : FlatSem.pmatchList state (left ++ right) (leftValues ++ rightValues) bindings <;>
          cases last : FlatSem.pmatchList state right rightValues bindings <;>
          simp_all [FlatSem.pmatchList, matchDecision, combineMatchDecisions]

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

/-- The generated constructor guard tests exactly the constructor tag and
field count in the evaluated value. -/
theorem evaluate_tagLenEq {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (tag actual : Nat) (typeId : FlatLang.TypeId) (expected : Nat) (fields : List FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.conv (some (actual, typeId)) fields])) :
    FlatSem.evaluate env state [.app trace (.tagLenEq tag expected) [expression]] =
      (state, .val [FlatSem.boolValue (actual == tag && fields.length == expected)]) := by
  simp [FlatSem.evaluate, pure, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat]

/-- The naive constructor expansion preserves the subpattern order. -/
theorem naiveChildren_patterns (trace : Tra) (expression : FlatLang.Exp) (index : Nat)
    (patterns : List FlatLang.Pat) : (children trace expression index patterns).map Prod.fst = patterns := by
  induction patterns generalizing index with
  | nil => rfl
  | cons pattern patterns ih => simp [children, ih]

/-- The generated field expressions evaluate to the matching constructor
fields, starting after an arbitrary prefix. -/
theorem naiveChildren_pure_aux {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)) (front values : List FlatSem.Value)
    (patterns : List FlatLang.Pat) (lengths : patterns.length = values.length)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.conv stamp (front ++ values)])) :
    List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
      ((children trace expression front.length patterns).map Prod.snd) values := by
  induction patterns generalizing front values with
  | nil =>
    cases values with
    | nil => exact .nil
    | cons _ _ => simp at lengths
  | cons pattern patterns ih =>
    cases values with
    | nil => simp at lengths
    | cons value values =>
      simp only [children, List.map_cons]
      apply List.Forall₂.cons
      · exact evaluate_con_projection trace expression env state stamp (front ++ value :: values) front.length value pure (by simp)
      · have tailPure : FlatSem.evaluate env state [expression] =
            (state, .val [.conv stamp ((front ++ [value]) ++ values)]) := by
          simpa [List.append_assoc] using pure
        have h := ih (front ++ [value]) values (by simpa using lengths) tailPure
        simpa using h

/-- The complete generated projection list evaluates to the constructor's
fields in order. -/
theorem naiveChildren_pure {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)) (fields : List FlatSem.Value)
    (patterns : List FlatLang.Pat) (lengths : patterns.length = fields.length)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [.conv stamp fields])) :
    List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
      ((children trace expression 0 patterns).map Prod.snd) fields := by
  simpa using naiveChildren_pure_aux trace expression env state stamp [] fields patterns lengths pure

/-- When constructor stamps and arities match, expanding its fields into the
work list preserves the match decision, including later type errors. -/
theorem pmatchList_con_expanded_decision {C F : Type} (state : FlatSem.State C F)
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
  have combined := pmatchList_append_decision state patterns rest fields values bindings same.2
  cases first : FlatSem.pmatchList state patterns fields bindings with
  | typeError =>
    simp [first, matchDecision, combineMatchDecisions] at combined
    simpa [FlatSem.pmatchList, head, first, matchDecision] using combined.symm
  | noMatch =>
    cases tail : FlatSem.pmatchList state rest values bindings <;>
      simp_all [FlatSem.pmatchList, matchDecision, combineMatchDecisions]
  | «match» next =>
    have independent := pmatchList_decision_independent state rest values next bindings
    have comb : matchDecision (FlatSem.pmatchList state (patterns ++ rest) (fields ++ values) bindings) =
        matchDecision (FlatSem.pmatchList state rest values bindings) := by
      cases tail : FlatSem.pmatchList state rest values bindings <;>
        simpa [first, tail, matchDecision, combineMatchDecisions] using combined
    simp only [FlatSem.pmatchList, head, first]
    exact independent.trans comb.symm

/-- An incompatible constructor tag or arity gives a non-match unless the
remaining patterns raise a type error. -/
theorem pmatchList_con_failed_decision {C F : Type} (state : FlatSem.State C F)
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

/-- Constructor work items use their recursive field guard when the source
constructor and pattern have the same tag and arity. -/
theorem naiveList_con_matching {C F : Type} (trace : Tra)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeGroupId)) (patterns : List FlatLang.Pat)
    (expression : FlatLang.Exp) (rest : List (FlatLang.Pat × FlatLang.Exp))
    (ih : @NaiveListCorrect C F trace (children trace expression 0 patterns ++ rest))
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
      ((children trace expression 0 patterns ++ rest).map Prod.snd) (fields ++ values) := by
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
      ((children trace expression 0 patterns ++ rest).map Prod.fst) (fields ++ values) bindings) = some answer := by
    simpa [List.map_append, naiveChildren_patterns] using expanded.symm.trans decision
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
        (naivePatternMatch trace (children trace expression 0 patterns ++ rest)) (FlatLang.mkBool trace false)
        true env state guardTrue
      simpa [naivePatternMatch, evaluate_smartIf, branch] using nested

/-- Constructor case of the recursive naive work-list simulation. -/
theorem naiveList_con {C F : Type} (trace : Tra)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeGroupId)) (patterns : List FlatLang.Pat)
    (expression : FlatLang.Exp) (rest : List (FlatLang.Pat × FlatLang.Exp))
    (ih : @NaiveListCorrect C F trace (children trace expression 0 patterns ++ rest)) :
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
            | none => cases compatible <;> simp_all
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
                  (naivePatternMatch trace (children trace expression 0 patterns ++ rest)) (FlatLang.mkBool trace false)
                  false env state guardFalse
                cases result : FlatSem.pmatchList state (rest.map Prod.fst) values bindings <;>
                  simp [result, matchDecision, combineMatchDecisions] at failedDecision
                all_goals subst answer
                all_goals simpa [naivePatternMatch, evaluate_smartIf, branch] using evaluate_bool trace false env state
        · have head : FlatSem.pmatch state (.pcon stamp patterns) (.conv actual fields) bindings = .typeError := by
            simp [FlatSem.pmatch, compatible]
          simp [FlatSem.pmatchList, head, matchDecision] at decision

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

/-- Every naive work-list guard simulates the corresponding pattern-list
decision. The evaluator remains pending its HOL correspondence review. -/
theorem naiveList_all {C F : Type} (trace : Tra) (todo : List (FlatLang.Pat × FlatLang.Exp)) :
    @NaiveListCorrect C F trace todo := by
  induction todo using naivePatternMatch.induct trace with
  | case1 => exact naiveList_nil trace
  | case2 expression rest ih => exact naiveList_any trace expression rest ih
  | case3 expression rest name ih => exact naiveList_var trace name expression rest ih
  | case4 expression rest lit ih => exact naiveList_literal trace lit expression rest ih
  | case5 expression rest patterns ih => exact naiveList_con trace none patterns expression rest ih
  | case6 expression rest patterns tag group ih => exact naiveList_con trace (some (tag, group)) patterns expression rest ih
  | case7 expression rest pattern name ih => exact naiveList_as trace pattern name expression rest ih
  | case8 expression rest pattern ih => exact naiveList_ref trace pattern expression rest ih

/-- A pure scrutinee supplies the single-pattern guards for every row. -/
theorem naiveGuardCorrect_of_pure {C F : Type} (trace : Tra) (expression : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    NaiveGuardCorrect trace expression env state value := by
  intro pattern
  have work := naiveList_all trace [(pattern, expression)] env state [value] []
  have workPure : List.Forall₂ (fun expression value => FlatSem.evaluate env state [expression] = (state, .val [value]))
      ([(pattern, expression)].map Prod.snd) [value] := .cons pure .nil
  cases result : FlatSem.pmatch state pattern value [] with
  | typeError => simp
  | noMatch =>
    have decision : matchDecision (FlatSem.pmatchList state ([(pattern, expression)].map Prod.fst) [value] []) = some false := by
      simp [FlatSem.pmatchList, result, matchDecision]
    simpa [result] using work false workPure decision
  | «match» bindings =>
    have decision : matchDecision (FlatSem.pmatchList state ([(pattern, expression)].map Prod.fst) [value] []) = some true := by
      simp [FlatSem.pmatchList, result, matchDecision]
    simpa [result] using work true workPure decision

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

/-- The ordered naive dispatcher selects the same body as the source matcher
when its scrutinee evaluates purely and matching does not type-error. -/
theorem naivePatternMatches_correct {C F : Type} (trace : Tra) (expression default : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (rows : List (FlatLang.Pat × FlatLang.Exp))
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value]))
    (safe : FlatSem.pmatchRows rows state value ≠ .typeError) :
    FlatSem.evaluate env state [naivePatternMatches trace expression rows default] =
      FlatSem.evaluate env state [match FlatSem.pmatchRows rows state value with
        | .match (_, _, body) => body
        | _ => default] :=
  naivePatternMatches_from_guards trace expression default env state value
    (naiveGuardCorrect_of_pure trace expression env state value pure) rows safe

/-- Transform the body carried by a successful row result, preserving both
non-match and type-error results. -/
def mapRowResult {E E' : Type} (f : FlatLang.Pat → E → E') :
    Flapjack.SemanticPrimitivesHOL.MatchResult (List (VarN × FlatSem.Value) × FlatLang.Pat × E) →
    Flapjack.SemanticPrimitivesHOL.MatchResult (List (VarN × FlatSem.Value) × FlatLang.Pat × E')
  | .typeError => .typeError
  | .noMatch => .noMatch
  | .match (bindings, pattern, body) => .match (bindings, pattern, f pattern body)

/-- Replacing row bodies leaves row selection unchanged and transforms only
the body of a successful result. -/
theorem pmatchRows_map_bodies {C F E E' : Type} (state : FlatSem.State C F) (value : FlatSem.Value)
    (rows : List (FlatLang.Pat × E)) (f : FlatLang.Pat → E → E') :
    FlatSem.pmatchRows (rows.map fun (pattern, body) => (pattern, f pattern body)) state value =
      mapRowResult f (FlatSem.pmatchRows rows state value) := by
  induction rows with
  | nil => simp [FlatSem.pmatchRows, mapRowResult]
  | cons row rows ih =>
    obtain ⟨pattern, body⟩ := row
    cases head : FlatSem.pmatch state pattern value [] with
    | typeError => simp [FlatSem.pmatchRows, head, mapRowResult]
    | noMatch => simpa [FlatSem.pmatchRows, head] using ih
    | «match» bindings =>
      cases tail : FlatSem.pmatchRows rows state value with
      | typeError => simp [tail, mapRowResult] at ih; simp [FlatSem.pmatchRows, head, tail, ih, mapRowResult]
      | noMatch => simp [tail, mapRowResult] at ih; simp [FlatSem.pmatchRows, head, tail, ih, mapRowResult]
      | «match» selected =>
        rcases selected with ⟨tailBindings, tailPattern, tailBody⟩
        simp [tail, mapRowResult] at ih
        simp [FlatSem.pmatchRows, head, tail, ih, mapRowResult]

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
  have mappedResult := pmatchRows_map_bodies state value rows f
  have mappedSafe : FlatSem.pmatchRows mapped state value ≠ .typeError := by
    change FlatSem.pmatchRows (rows.map fun (pattern, body) => (pattern, f pattern body)) state value ≠ .typeError
    rw [mappedResult]
    cases h : FlatSem.pmatchRows rows state value <;> simp_all [mapRowResult]
  have dispatch := naivePatternMatches_correct trace expression default env state value mapped pure mappedSafe
  have compiledRows : List.zip (rows.map Prod.fst) (rows.map (compilePatRhs trace n expression)) = mapped := by
    simpa [mapped, f] using zip_row_bodies rows f
  cases original : FlatSem.pmatchRows rows state value with
  | typeError => exact (safe original).elim
  | noMatch =>
    have target : FlatSem.pmatchRows mapped state value = .noMatch := by
      simpa [mapped, original, mapRowResult] using mappedResult
    simpa [compilePats, compiledRows, mapped, f, original, target] using dispatch
  | «match» selected =>
    rcases selected with ⟨bindings, pattern, body⟩
    have target : FlatSem.pmatchRows mapped state value = .match (bindings, pattern, f pattern body) := by
      simpa [mapped, original, mapRowResult] using mappedResult
    simpa [compilePats, compiledRows, mapped, f, original, target] using dispatch

end Flapjack.Compiler.Backend.FlatPattern
