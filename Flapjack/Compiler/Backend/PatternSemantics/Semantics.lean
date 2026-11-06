import Flapjack.Compiler.Backend.PatternSemantics
import Flapjack.SemanticPrimitivesHOL
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-! Semantics of pattern-compiler inputs and decision trees. The remaining
decision-tree and row evaluators await HOL source and carrier review. -/
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
  | .tagLenEq tag length, .term (some actual) values => some (tag == actual && length == values.length)
  | .litEq lit, .litv actual => if litSameType lit actual then some (decide (lit = actual)) else none
  | _, _ => none

/-- Follow a position through constructor fields or a reference. The direct
index lookup implements the source's recursion over the field list. -/
def appPos (refs : HolFiniteMapExact Nat Term) : Position → Term → Option Term
  | .emptyPos, value => some value
  | .pos index rest, .term _ values => do
    let value ← values[index]?
    appPos refs rest value
  | .pos 0 rest, .refPtr index => do
    let value ← refs.lookup index
    appPos refs rest value
  | .pos _ _, _ => none

/-- Evaluate a guard with the source's short-circuit and error behavior. -/
def dtEvalGuard (refs : HolFiniteMapExact Nat Term) (value : Term) : DGuard → Option Bool
  | .true_ => some true
  | .posTest position test => do
    let selected ← appPos refs position value
    dtTest test selected
  | .not guard => (dtEvalGuard refs value guard).map (! ·)
  | .conj left right => do
    let first ← dtEvalGuard refs value left
    if first then dtEvalGuard refs value right else some false
  | .disj left right => do
    let first ← dtEvalGuard refs value left
    if first then some true else dtEvalGuard refs value right

/-- Evaluate a decision tree; a type-failure leaf produces `none`. -/
def dtEval (refs : HolFiniteMapExact Nat Term) (value : Term) : DTree → Option MatchResult
  | .leaf index => some (.success index)
  | .fail => some .failure
  | .typeFail => none
  | .if_ guard yes no => do
    let selected ← dtEvalGuard refs value guard
    if selected then dtEval refs value yes else dtEval refs value no

end Flapjack.Compiler.Backend.PatternSemantics
