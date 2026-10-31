import Flapjack.Compiler.Backend.BviTmc.Proofs.StateRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.HoleRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.WordRelation
import Flapjack.Compiler.Backend.BviTailrec.Proofs.PrimitiveRelation

/-! Primitive-operation cases of the TMC evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem BviSem

namespace OperationWitness
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end OperationWitness

private def integerValue : Value → Prop
  | .number _ => True
  | _ => False

private theorem intArgsEqual (f : HolFiniteMapExact Nat Nat) (op : ClosLang.IntOp)
    (values relatedValues : List Value) (value : Value)
    (run : BviTailrec.intPrimitiveResult op values = some value)
    (related : List.Forall₂ (valueRel f) values relatedValues) : relatedValues = values := by
  have allInteger : ∀ v ∈ values, integerValue v := by
    unfold BviTailrec.intPrimitiveResult at run
    repeat' split at run
    all_goals try (unfold BvlSem.doIntApp at run; repeat' split at run)
    all_goals simp_all [integerValue]
  clear run
  induction related with
  | nil => rfl
  | @cons a b xs ys head tail ih =>
    have scalarHead := allInteger a (by simp)
    have tailAll : ∀ v ∈ xs, integerValue v := by
      intro v member
      exact allInteger v (by simp [member])
    cases head <;> simp_all [integerValue]

private theorem intResultRelated (f : HolFiniteMapExact Nat Nat) (op : ClosLang.IntOp)
    (values : List Value) (value : Value)
    (run : BviTailrec.intPrimitiveResult op values = some value) : valueRel f value value := by
  unfold BviTailrec.intPrimitiveResult at run
  repeat' split at run
  all_goals try (unfold BvlSem.doIntApp at run; repeat' split at run)
  all_goals try contradiction
  all_goals simp only [Option.some.injEq] at run
  all_goals subst value
  all_goals first | exact .number _ | exact .block _ [] [] .nil

/-- The word-operation case of the source primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_word {C F : Type} (f : HolFiniteMapExact Nat Nat) (op : ClosLang.WordOp)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.wordOp op) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.wordOp op)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.wordOp op) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  rw [BviTailrec.doApp_wordOp_pure] at run
  cases result : doWordApp op values with
  | none => simp [result] at run
  | some actual =>
    simp [result] at run
    obtain ⟨rfl, rfl⟩ := run
    have sameValues := doWordApp_rel f op values relatedValues actual result valuesRelated
    subst relatedValues
    refine ⟨f, actual, target, ?_, doWordApp_result_rel f op values actual result, statesRelated, ?_,
      onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
    · simp [BviTailrec.doApp_wordOp_pure, result]
    · intro key item found
      exact found

/-- The integer-operation case of the source primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_int {C F : Type} (f : HolFiniteMapExact Nat Nat) (op : ClosLang.IntOp)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.intOp op) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.intOp op)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.intOp op) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  rw [BviTailrec.doApp_intOp_pure] at run
  cases result : BviTailrec.intPrimitiveResult op values with
  | none => simp [result] at run
  | some actual =>
    simp [result] at run
    obtain ⟨rfl, rfl⟩ := run
    have sameValues := intArgsEqual f op values relatedValues actual result valuesRelated
    subst relatedValues
    refine ⟨f, actual, target, ?_, intResultRelated f op values actual result, statesRelated, ?_,
      onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
    · simp [BviTailrec.doApp_intOp_pure, result]
    · intro key item found
      exact found

end Flapjack.Compiler.Backend.BviTmc
