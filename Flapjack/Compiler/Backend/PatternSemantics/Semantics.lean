module

public import Flapjack.Compiler.Backend.PatternSemantics
public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Semantics of pattern-compiler inputs and decision trees. -/
namespace Flapjack.Compiler.Backend.PatternSemantics
open Flapjack Flapjack.AstHOL PatternCommon
open Flapjack.SemanticPrimitivesHOL (litSameType)

/-- Values observed by the pattern compiler's semantics. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "term"]
inductive Term where
  | term : Option Nat → List Term → Term
  | litv : Lit → Term
  | refPtr : Nat → Term
  | other

/-- Executable sibling membership at the tag-and-arity carrier; its agreement
with the polymorphic source operation is `isSibling_eq_HOL`. -/
def isSibling (item : Nat × Nat) : Option (List (Nat × Nat)) → Bool
  | none => true
  | some siblings => siblings.contains item

section SourcePolymorphic
open Classical

/-- HOL's unrestricted polymorphic sibling membership test. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "is_sibling_def"]
noncomputable def isSiblingHOL {α : Type} (item : α) : Option (List α) → Bool
  | none => true
  | some siblings => decide (item ∈ siblings)

/-- The executed test agrees with the source at tag-and-arity pairs. -/
theorem isSibling_eq_HOL (item : Nat × Nat) (siblings : Option (List (Nat × Nat))) :
    isSibling item siblings = isSiblingHOL item siblings := by
  cases siblings <;> simp [isSibling, isSiblingHOL]
end SourcePolymorphic

private def toBroad (refs : HolFiniteMapExact Nat Term) : Nat → Option Term :=
  refs.lookup

private def ofBroad (lookup : Nat → Option Term)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat Term := ⟨lookup, support⟩

/-- The canonical finite-map parameter roundtrips through its lookup view. -/
theorem holFmapAsFiniteSupportParamWitness_pmatch_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

theorem holFmapAsFiniteSupportParamWitness_pmatchList_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_matchRows_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_appPos_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_dtEvalGuard_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_refs refs key

theorem holFmapAsFiniteSupportParamWitness_dtEval_refs
    (refs : HolFiniteMapExact Nat Term) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_pmatch_refs refs key

mutual
/-- Match one pattern against an abstract term and finite reference map. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "pmatch_def"
  (fmap_as_finite_support_parameters := [refs])]
def pmatch (refs : HolFiniteMapExact Nat Term) (pattern : Pat) (value : Term) : PmatchResult :=
  match pattern, value with
  | .any, _ => .success
  | .lit lit, .litv actual =>
    if !litSameType lit actual then .typeFailure else if lit = actual then .success else .failure
  | .cons (some (tag, siblings)) patterns, .term (some actual) values =>
    if tag = actual ∧ patterns.length = values.length then pmatchList refs patterns values
    else if isSibling (actual, values.length) siblings then .failure else .typeFailure
  | .cons none patterns, .term none values => pmatchList refs patterns values
  | .ref pattern, .refPtr index =>
    match refs.lookup index with
    | none => .typeFailure
    | some value => pmatch refs pattern value
  | .or first second, value =>
    match pmatch refs first value with
    | .success => match pmatch refs second value with
      | .typeFailure => .typeFailure
      | _ => .success
    | .failure => pmatch refs second value
    | .typeFailure => .typeFailure
  | _, _ => .typeFailure
termination_by sizeOf pattern

/-- Match a list of patterns, retaining a later type error after a non-match. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "pmatch_def"
  (fmap_as_finite_support_parameters := [refs])]
def pmatchList (refs : HolFiniteMapExact Nat Term) (patterns : List Pat) (values : List Term) : PmatchResult :=
  match patterns, values with
  | [], [] => .success
  | pattern :: patterns, value :: values =>
    match pmatch refs pattern value with
    | .success => pmatchList refs patterns values
    | .failure => match pmatchList refs patterns values with
      | .typeFailure => .typeFailure
      | _ => .failure
    | .typeFailure => .typeFailure
  | _, _ => .typeFailure
termination_by sizeOf patterns
end

/-- Select the first matching row while still checking later rows for errors. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "match_def"
  (fmap_as_finite_support_parameters := [refs])]
def matchRows (refs : HolFiniteMapExact Nat Term) : List (Pat × Nat) → Term → Option MatchResult
  | [], _ => some .failure
  | (pattern, result) :: rows, value =>
    match pmatch refs pattern value with
    | .success => match matchRows refs rows value with
      | none => none
      | some _ => some (.success result)
    | .failure => matchRows refs rows value
    | .typeFailure => none

/-- Run an atomic decision-tree test. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "dt_test_def"]
def dtTest (test : DTest) (value : Term) : Option Bool :=
  match test, value with
  | .tagLenEq tag length, .term (some actual) values => some (decide (tag = actual ∧ length = values.length))
  | .litEq lit, .litv actual => if litSameType lit actual then some (decide (lit = actual)) else none
  | _, _ => none

/-- Follow a position through constructor fields or a reference. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "app_pos_def"
  (fmap_as_finite_support_parameters := [refs])]
def appPos (refs : HolFiniteMapExact Nat Term) : Position → Term → Option Term
  | .emptyPos, value => some value
  | .pos 0 rest, .refPtr address =>
    match refs.lookup address with
    | none => none
    | some value => appPos refs rest value
  | .pos 0 rest, .term _ (value :: _) => appPos refs rest value
  | .pos (index + 1) rest, .term tag (_ :: values) =>
    appPos refs (.pos index rest) (.term tag values)
  | .pos _ _, _ => none
termination_by position _ => sizeOf position
decreasing_by all_goals simp_wf

/-- Indexing form of the source traversal through a term's fields. This
Flapjack helper supports proofs that reason about successful list lookup. -/
theorem appPos_term (refs : HolFiniteMapExact Nat Term) (index : Nat) (rest : Position)
    (tag : Option Nat) (values : List Term) :
    appPos refs (.pos index rest) (.term tag values) =
      (values[index]?).bind (appPos refs rest) := by
  induction index generalizing values with
  | zero => cases values <;> simp [appPos]
  | succ index ih => cases values <;> simp [appPos, ih]

/-- Evaluate a guard with the source's short-circuit and error behavior. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "dt_eval_guard_def"
  (fmap_as_finite_support_parameters := [refs])]
def dtEvalGuard (refs : HolFiniteMapExact Nat Term) (value : Term) : DGuard → Option Bool
  | .true_ => some true
  | .posTest position test =>
    match appPos refs position value with
    | none => none
    | some selected => dtTest test selected
  | .not guard =>
    match dtEvalGuard refs value guard with
    | none => none
    | some result => some (!result)
  | .conj left right =>
    match dtEvalGuard refs value left with
    | none => none
    | some true => dtEvalGuard refs value right
    | some false => some false
  | .disj left right =>
    match dtEvalGuard refs value left with
    | none => none
    | some true => some true
    | some false => dtEvalGuard refs value right

/-- Evaluate a decision tree; a type-failure leaf produces `none`. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml" "dt_eval_def"
  (fmap_as_finite_support_parameters := [refs])]
def dtEval (refs : HolFiniteMapExact Nat Term) (value : Term) : DTree → Option MatchResult
  | .leaf index => some (.success index)
  | .fail => some .failure
  | .typeFail => none
  | .if_ guard yes no =>
    match dtEvalGuard refs value guard with
    | none => none
    | some selected => dtEval refs value (if selected then yes else no)
termination_by tree => sizeOf tree
decreasing_by all_goals split <;> simp_wf <;> omega

end Flapjack.Compiler.Backend.PatternSemantics
