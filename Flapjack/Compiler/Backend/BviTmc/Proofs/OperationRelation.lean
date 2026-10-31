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

/-- The label case uses code-domain preservation to retain code pointers
even when TMC rewrites the function body. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_label {C F : Type} (f : HolFiniteMapExact Nat Nat) (label : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.label label) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.label label)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.label label) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | cons head tail => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    cases valuesRelated
    cases sourceLookup : sptLookup label source.code with
    | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceLookup] at run
    | some entry =>
      have sourceMem : sptMem label source.code := (sptMem_iff_lookup label source.code).mpr ⟨entry, sourceLookup⟩
      have targetMem := codeRel_domain source.code target.code (stateRel_codeRel f source target statesRelated) label sourceMem
      obtain ⟨targetEntry, targetLookup⟩ := (sptMem_iff_lookup label target.code).mp targetMem
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceLookup] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨f, .codePtr label, target, ?_, .codePtr label, statesRelated, ?_,
        onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
      · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, targetLookup]
      · intro key item found
        exact found

/-- Reading the globals pointer preserves its translation through the
TMC pointer map. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_globalsPtr {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.globOp .globalsPtr) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.globOp .globalsPtr)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.globOp .globalsPtr) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | cons head tail => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    cases valuesRelated
    cases sourceGlobal : source.global with
    | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal] at run
    | some ptr =>
      cases targetGlobal : target.global with
      | none => simp [stateRel, sourceGlobal, targetGlobal] at statesRelated
      | some targetPtr =>
        have mapped : f.lookup ptr = some targetPtr := by
          simpa [sourceGlobal, targetGlobal] using statesRelated.2.2.1
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨f, .refPtr true targetPtr, target, ?_, .refPtr ptr targetPtr true mapped,
          statesRelated, ?_, onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅,
          holesStill_refl f target.refs⟩
        · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, targetGlobal]
        · intro key item found
          exact found

/-- Setting the globals pointer preserves the translated state relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_setGlobalsPtr {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.globOp .setGlobalsPtr) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.globOp .setGlobalsPtr)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.globOp .setGlobalsPtr) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons head tail =>
    cases tail with
    | cons next rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | nil =>
      cases head with
      | number n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | block tag xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | refPtr flag ptr =>
        cases flag with
        | false => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        | true =>
          cases valuesRelated with
          | cons headRel tailRel =>
            cases tailRel
            cases headRel with
            | refPtr _ targetPtr _ mapped =>
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
              obtain ⟨rfl, rfl⟩ := run
              have nextRelated : stateRel f { source with global := some ptr } { target with global := some targetPtr } := by
                exact ⟨statesRelated.1, statesRelated.2.1, mapped, statesRelated.2.2.2⟩
              refine ⟨f, unitValue, { target with global := some targetPtr }, ?_, ?_, nextRelated, ?_,
                onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
              · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux]
              · exact .block _ [] [] .nil
              · intro key item found
                exact found

/-- Allocating globals is rejected by the BVI primitive dispatcher, so its
successful-execution simulation case is impossible. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_allocGlobal {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.globOp .allocGlobal) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.globOp .allocGlobal)) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.globOp .allocGlobal) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run

end Flapjack.Compiler.Backend.BviTmc
