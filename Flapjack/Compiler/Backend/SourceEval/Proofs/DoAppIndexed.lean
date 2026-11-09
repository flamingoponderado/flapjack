import Flapjack.Compiler.Backend.SourceEval.Proofs.StateRelation
import Flapjack.SemanticPrimitivesHOL.Apply
import Flapjack.SemanticPrimitivesProps.ResultRelation
import Flapjack.Misc.ListLookupRel
import Flapjack.Misc.List
import Mathlib.Data.List.Forall2

/-! Shared indexed-operation prerequisites for the source primitive simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL

/-- Flapjack proof infrastructure: a successful indexed read leaves its state unchanged. -/
private theorem indexedReadState {F A : Type} (state out : Store Value × HolFfiState F)
    (isUnsafe : Bool) (index : Int) (items : List A) (toValue : A → Value) (r : Result Value Value)
    (run : readIndexed state isUnsafe items index toValue = some (out, r)) : out = state := by
  by_cases negative : index < 0
  · cases isUnsafe <;> simp [readIndexed, boundsFailure, negative] at run
    exact run.1.symm
  · cases found : items[index.toNat]? with
    | none =>
      cases isUnsafe <;> simp [readIndexed, boundsFailure, negative, found] at run
      exact run.1.symm
    | some value =>
      simp [readIndexed, negative, found] at run
      exact run.1.symm

/-- Flapjack infrastructure for the indexed-read clauses of `do_app_sim`.
The source evaluator factors those HOL cases through `readIndexed`; this
generic relation has no separate HOL declaration. -/
theorem indexedRead_related {F A B : Type} (oracle : EvalOracleState)
    (source target out : Store Value × HolFfiState F) (isUnsafe : Bool) (index : Int)
    (left : List A) (right : List B) (R : A → B → Prop) (toLeft : A → Value) (toRight : B → Value)
    (related : List.Forall₂ R left right)
    (values : ∀ a b, R a b → ValueRel oracle (toLeft a) (toRight b))
    (r : Result Value Value) (run : readIndexed source isUnsafe left index toLeft = some (out, r)) :
    out = source ∧ ∃ r', readIndexed target isUnsafe right index toRight = some (target, r') ∧
      resultRel (ValueRel oracle) (ValueRel oracle) r r' := by
  have same := indexedReadState source out isUnsafe index left toLeft r run
  subst out
  refine ⟨rfl, ?_⟩
  by_cases negative : index < 0
  · cases isUnsafe <;> simp [readIndexed, boundsFailure, negative] at run ⊢
    subst r
    exact ValueRel.con .nil
  · cases found : left[index.toNat]? with
    | none =>
      have absent : right[index.toNat]? = none := by
        have relatedLookup := Flapjack.forall₂_lookupRel related index.toNat
        cases targetFound : right[index.toNat]? with
        | none => rfl
        | some value => simp [found, targetFound, Flapjack.optionRel] at relatedLookup
      cases isUnsafe <;> simp [readIndexed, boundsFailure, negative, found, absent] at run ⊢
      subst r
      exact ValueRel.con .nil
    | some value =>
      obtain ⟨value', found', same⟩ := Flapjack.forall₂_lookup related index.toNat value found
      simp [readIndexed, negative, found] at run
      subst r
      exact ⟨.val (toRight value'), by simp [readIndexed, negative, found'], values value value' same⟩

/-- Flapjack infrastructure for the indexed-update clauses of `do_app_sim`.
The source evaluator factors those HOL cases through `updateIndexed`; this
generic relation has no separate HOL declaration. -/
theorem indexedUpdate_related {F A B : Type} (oracle : EvalOracleState) (source target : Store Value)
    (ffi ffi' : HolFfiState F) (unsafeFlag : Bool) (address : Nat) (index : Int)
    (left : List A) (right : List B) (x : A) (y : B) (R : A → B → Prop)
    (asLeft : List A → StoreValue Value) (asRight : List B → StoreValue Value)
    (stores : List.Forall₂ (storeValueRel (ValueRel oracle)) source target)
    (items : List.Forall₂ R left right) (values : R x y)
    (entry : ∀ a b, List.Forall₂ R a b → storeValueRel (ValueRel oracle) (asLeft a) (asRight b))
    (out : Store Value) (r : Result Value Value)
    (run : updateIndexed (source, ffi) unsafeFlag address left index x asLeft = some ((out, ffi'), r)) :
    ∃ out' r', updateIndexed (target, ffi) unsafeFlag address right index y asRight = some ((out', ffi'), r') ∧
      List.Forall₂ (storeValueRel (ValueRel oracle)) out out' ∧
      resultRel (ValueRel oracle) (ValueRel oracle) r r' := by
  have lengths := items.length_eq
  by_cases outside : index < 0 ∨ left.length ≤ index.toNat
  · cases unsafeFlag <;> simp [updateIndexed, boundsFailure, outside] at run ⊢
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
    refine ⟨target, .err (.raise subExnV), ?_, stores, ?_⟩
    · simp [outside, ← lengths]
    · exact ValueRel.con .nil
  · have sameOutside : ¬(index < 0 ∨ right.length ≤ index.toNat) := by simpa [← lengths] using outside
    simp only [updateIndexed, Bool.or_eq_true, decide_eq_true_eq, outside, ↓reduceIte] at run
    cases assigned : storeAssign address (asLeft (left.set index.toNat x)) source with
    | none => simp [assigned] at run
    | some updated =>
      have updatedEntries := entry _ _ (Flapjack.forall₂_set R left right x y index.toNat ⟨values, items⟩)
      obtain ⟨targetUpdated, targetAssigned, targetStores⟩ := storeAssign_related stores address updatedEntries assigned
      simp [assigned] at run
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
      refine ⟨targetUpdated, .val (.conv none []), ?_, targetStores, ?_⟩
      · simp [updateIndexed, sameOutside, targetAssigned]
      · exact ValueRel.con .nil

end Flapjack.Compiler.Backend.SourceEval.Proofs
