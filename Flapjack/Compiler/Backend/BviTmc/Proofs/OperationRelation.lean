import Flapjack.Compiler.Backend.BviTmc.Proofs.StateRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.HoleRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.WordRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.Allocation
import Flapjack.Compiler.Backend.BviTmc.Proofs.Equality
import Flapjack.Compiler.Backend.BviTmc.Proofs.BuildRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.ThunkRelation
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

private theorem related_getElem (f : HolFiniteMapExact Nat Nat) {xs ys : List Value}
    (related : List.Forall₂ (valueRel f) xs ys) (index : Nat) (x : Value)
    (found : xs[index]? = some x) : ∃ y, ys[index]? = some y ∧ valueRel f x y := by
  induction related generalizing index with
  | nil => simp at found
  | @cons a b xs ys head tail ih =>
    cases index with
    | zero =>
      simp at found
      subst x
      exact ⟨b, rfl, head⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found ⊢
      exact ih index found

private theorem related_set (f : HolFiniteMapExact Nat Nat) {xs ys : List Value}
    (related : List.Forall₂ (valueRel f) xs ys) (index : Nat) (x y : Value)
    (valuesRelated : valueRel f x y) : List.Forall₂ (valueRel f) (xs.set index x) (ys.set index y) := by
  induction related generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simpa using List.Forall₂.cons valuesRelated tail
    | succ index => simpa using List.Forall₂.cons head (ih index)

/-- Reading a global follows the translated pointer into related arrays. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_global {C F : Type} (f : HolFiniteMapExact Nat Nat) (index : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.globOp (.global index)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.globOp (.global index))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.globOp (.global index)) relatedValues target = .val (value', targetNext) ∧
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
        obtain ⟨sourceCell, targetCell, sourceFound, targetFound, cells⟩ :=
          stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
        cases cells with
        | byteArray b bytes =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, sourceFound] at run
        | thunk mode x y rel =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, sourceFound] at run
        | valueArray xs ys rel =>
          cases element : xs[index]? with
          | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, sourceFound, element] at run
          | some found =>
            have ⟨found', targetElement, valuesRel⟩ := related_getElem f rel index found element
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, sourceFound, element] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨f, found', target, ?_, valuesRel, statesRelated, ?_, onlyFresh_refl f target.refs,
              holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
            · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, targetGlobal, targetFound, targetElement]
            · intro key item found
              exact found

/-- Writing a global updates related arrays while preserving separate holes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_setGlobal {C F : Type} (f : HolFiniteMapExact Nat Nat) (index : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.globOp (.setGlobal index)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.globOp (.setGlobal index))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.globOp (.setGlobal index)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons head tail =>
    cases tail with
    | cons next rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | nil =>
      cases valuesRelated with
      | @cons a b xs ys headRel tailRel =>
        cases tailRel
        cases sourceGlobal : source.global with
        | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal] at run
        | some ptr =>
          cases targetGlobal : target.global with
          | none => simp [stateRel, sourceGlobal, targetGlobal] at statesRelated
          | some targetPtr =>
            have mapped : f.lookup ptr = some targetPtr := by
              simpa [sourceGlobal, targetGlobal] using statesRelated.2.2.1
            obtain ⟨sourceCell, targetCell, sourceFound, targetFound, cells⟩ :=
              stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
            cases cells with
            | byteArray b bytes =>
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, sourceFound] at run
            | thunk mode x y rel =>
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, sourceFound] at run
            | valueArray xs ys rel =>
              by_cases bound : index < xs.length
              · have bound' : index < ys.length := by simpa [List.Forall₂.length_eq rel] using bound
                simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, sourceFound, bound] at run
                obtain ⟨rfl, rfl⟩ := run
                have nextRelated : stateRel f
                    { source with refs := source.refs.updateEq (ptr, .valueArray (xs.set index head)) }
                    { target with refs := target.refs.updateEq (targetPtr, .valueArray (ys.set index b)) } := by
                  exact ⟨stateRefRel_update f source.refs target.refs ptr targetPtr _ _ statesRelated.1
                    statesRelated.2.2.2.2.2.2.2.2.2.2 mapped (.valueArray _ _ (related_set f rel index _ _ headRel)),
                    statesRelated.2⟩
                have nextRelated' : stateRel f
                    { source with global := some ptr, refs := source.refs.updateEq (ptr, .valueArray (xs.set index head)) }
                    { target with refs := target.refs.updateEq (targetPtr, .valueArray (ys.set index b)) } := by
                  simpa [sourceGlobal] using nextRelated
                refine ⟨f, unitValue, { target with refs := target.refs.updateEq (targetPtr, .valueArray (ys.set index b)) },
                  ?_, ?_, nextRelated', ?_, onlyFresh_refl f target.refs,
                  holesUnchanged_rangeUpdate f ptr targetPtr _ target.refs mapped,
                  holesStill_rangeUpdate f ptr targetPtr _ target.refs mapped⟩
                · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, targetGlobal, targetFound, bound']
                · exact .block _ [] [] .nil
                · intro key item found
                  exact found
              · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, sourceFound, bound] at run

/-- All global operations satisfy the primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_glob {C F : Type} (f : HolFiniteMapExact Nat Nat) (op : ClosLang.GlobOp)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.globOp op) values source = .val (value, sourceNext))
    (noMutcons : noMutconsOp (.globOp op)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.globOp op) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases op with
  | global index => exact doApp_op_rel_global f index values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | setGlobal index => exact doApp_op_rel_setGlobal f index values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | allocGlobal => exact doApp_op_rel_allocGlobal f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | globalsPtr => exact doApp_op_rel_globalsPtr f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | setGlobalsPtr => exact doApp_op_rel_setGlobalsPtr f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated

private theorem finalise_related_identity (f : HolFiniteMapExact Nat Nat) (v w : Value)
    (source target : HolFiniteMapExact Nat (Ref Value)) (values : valueRel f v w)
    (heaps : stateRefRel f source target) :
    BviSem.finaliseCons v source = some (v, source) ∧ BviSem.finaliseCons w target = some (w, target) := by
  cases values with
  | number i => simp [BviSem.finaliseCons]
  | word64 w => simp [BviSem.finaliseCons]
  | block tag xs ys related => simp [BviSem.finaliseCons]
  | codePtr n => simp [BviSem.finaliseCons]
  | refPtr n m flag mapped =>
    obtain ⟨sourceCell, targetCell, sourceFound, targetFound, cells⟩ :=
      stateRefRel_lookup f n m source target mapped heaps
    cases cells <;> constructor
    all_goals rw [BviSem.finaliseCons.eq_def]
    all_goals dsimp only
    all_goals first | rw [sourceFound] | rw [targetFound]

/-- Finalising a related value leaves both related heaps unchanged, since
the source heap relation excludes mutable constructor blocks. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_finalise_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, refsNext, nextMap, targetRefsNext])]
theorem doApp_op_finalise_rel {C F : Type} (v : Value) (refsNext : HolFiniteMapExact Nat (Ref Value))
    (relatedValue result : Value) (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F)
    (run : BviSem.finaliseCons v source.refs = some (result, refsNext))
    (statesRelated : stateRel f source target) (valuesRelated : valueRel f v relatedValue) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (result' : Value)
      (targetRefsNext : HolFiniteMapExact Nat (Ref Value)),
      BviSem.finaliseCons relatedValue target.refs = some (result', targetRefsNext) ∧
      finiteSubmap f nextMap ∧ valueRel nextMap result result' ∧
      stateRel nextMap { source with refs := refsNext } { target with refs := targetRefsNext } ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetRefsNext ∅ ∧
      holesStillNotFinalised f target.refs targetRefsNext := by
  have ⟨sourceRun, targetRun⟩ := finalise_related_identity f v relatedValue source.refs target.refs valuesRelated statesRelated.1
  rw [sourceRun] at run
  cases run
  refine ⟨f, relatedValue, target.refs, targetRun, ?_, valuesRelated, ?_, onlyFresh_refl f target.refs,
    holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
  · intro key item found
    exact found
  · simpa using statesRelated

/-- The finalise-cons primitive preserves related values and heaps. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_finaliseCons {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .finaliseCons) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .finaliseCons)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .finaliseCons) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons head tail =>
    cases tail with
    | cons next rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | nil =>
      cases valuesRelated with
      | @cons a b xs ys headRel tailRel =>
        cases tailRel
        have ⟨sourceRun, targetRun⟩ := finalise_related_identity f head b source.refs target.refs headRel statesRelated.1
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceRun] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨f, b, target, ?_, headRel, statesRelated, ?_, onlyFresh_refl f target.refs,
          holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
        · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, targetRun]
        · intro key item found
          exact found

/-- Updating a mutable constructor cannot succeed in a related source heap. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_updateCons {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .updateCons) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .updateCons)) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .updateCons) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  rw [BviTailrec.doApp_updateCons_effect] at run
  cases effect : BviTailrec.updateConsEffect values source.refs with
  | none => simp [effect] at run
  | some refs =>
    unfold BviTailrec.updateConsEffect at effect
    repeat' split at effect
    all_goals try contradiction
    rename_i args flag ptr index child other tag finalised left old right found condition
    exact (no_mutblock f source.refs target.refs ptr tag finalised left old right statesRelated.1 found).elim

/-- Allocating an array of related values extends the pointer renaming with
the fresh source and target addresses. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_ref {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .ref) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .ref)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .ref) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  let src := leastUnusedRef source.refs
  let tgt := leastUnusedRef target.refs
  have srcFresh : src ∉ source.refs.domain := by simp [HolFiniteMapExact.domain, src, leastUnusedRef_unused]
  have tgtFresh : tgt ∉ target.refs.domain := by simp [HolFiniteMapExact.domain, tgt, leastUnusedRef_unused]
  have rangeFresh : tgt ∉ mapRange f := by
    rintro ⟨key, mapped⟩
    obtain ⟨_, _, _, found, _⟩ := stateRefRel_lookup f key tgt source.refs target.refs mapped statesRelated.1
    have absent : target.refs.lookup tgt = none := by simpa [HolFiniteMapExact.domain] using tgtFresh
    rw [absent] at found
    contradiction
  have srcMissing : f.lookup src = none := by
    have absent : src ∉ f.domain := by rw [statesRelated.1.1]; exact srcFresh
    simpa [HolFiniteMapExact.domain] using absent
  have extension : finiteSubmap f (f.updateEq (src, tgt)) := by
    intro key item found
    have different : key ≠ src := by
      intro equal
      subst key
      rw [srcMissing] at found
      contradiction
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found
  have cells : refRel (f.updateEq (src, tgt)) (.valueArray values) (.valueArray relatedValues) :=
    .valueArray _ _ (listRel_submap f _ values relatedValues valuesRelated extension)
  have ⟨mapped, nextStates, submap, fresh, holes, unfinalised⟩ :=
    stateRel_alloc f source target src tgt _ _ statesRelated srcFresh tgtFresh rangeFresh cells
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
    BviSem.toBvl, BviSem.fromBvl] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨f.updateEq (src, tgt), .refPtr true tgt,
    { target with refs := target.refs.updateEq (tgt, .valueArray relatedValues) }, ?_,
    .refPtr src tgt true mapped, nextStates, submap, fresh, holes, unfinalised⟩
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
    BviSem.toBvl, BviSem.fromBvl, tgt]

private theorem allocate_related {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (v w : Ref Value)
    (states : stateRel f source target) (cells : refRel f v w) :
    let src := leastUnusedRef source.refs
    let tgt := leastUnusedRef target.refs
    let next := f.updateEq (src, tgt)
    next.lookup src = some tgt ∧
    stateRel next { source with refs := source.refs.updateEq (src, v) }
      { target with refs := target.refs.updateEq (tgt, w) } ∧
    finiteSubmap f next ∧ onlyFresh f next target.refs ∧
    holesUnchangedExcept f target.refs (target.refs.updateEq (tgt, w)) ∅ ∧
    holesStillNotFinalised f target.refs (target.refs.updateEq (tgt, w)) := by
  dsimp only
  let src := leastUnusedRef source.refs
  let tgt := leastUnusedRef target.refs
  have srcFresh : src ∉ source.refs.domain := by simp [HolFiniteMapExact.domain, src, leastUnusedRef_unused]
  have tgtFresh : tgt ∉ target.refs.domain := by simp [HolFiniteMapExact.domain, tgt, leastUnusedRef_unused]
  have rangeFresh : tgt ∉ mapRange f := by
    rintro ⟨key, mapped⟩
    obtain ⟨_, _, _, found, _⟩ := stateRefRel_lookup f key tgt source.refs target.refs mapped states.1
    have absent : target.refs.lookup tgt = none := by simpa [HolFiniteMapExact.domain] using tgtFresh
    rw [absent] at found
    contradiction
  have srcMissing : f.lookup src = none := by
    have absent : src ∉ f.domain := by rw [states.1.1]; exact srcFresh
    simpa [HolFiniteMapExact.domain] using absent
  have extension : finiteSubmap f (f.updateEq (src, tgt)) := by
    intro key item found
    have different : key ≠ src := by
      intro equal
      subst key
      rw [srcMissing] at found
      contradiction
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found
  exact stateRel_alloc f source target src tgt v w states srcFresh tgtFresh rangeFresh
    (refRel_submap f _ v w cells extension)

private theorem replicate_related (f : HolFiniteMapExact Nat Nat) (count : Nat) (v w : Value)
    (related : valueRel f v w) : List.Forall₂ (valueRel f) (List.replicate count v) (List.replicate count w) := by
  induction count with
  | zero => exact .nil
  | succ count ih => simpa only [List.replicate_succ] using List.Forall₂.cons related ih

/-- Allocating repeated values extends the renaming at both fresh addresses. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_refArray {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .refArray) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .refArray)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .refArray) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons initial rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases first with
        | number count =>
          cases valuesRelated with
          | @cons a b xs ys countRel tailRel =>
            cases countRel
            cases tailRel with
            | @cons a b xs ys initialRel tailRel =>
              cases tailRel
              by_cases nonnegative : count < 0
              · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, nonnegative] at run
              · have ⟨mapped, nextStates, submap, fresh, holes, unfinalised⟩ :=
                  allocate_related f source target (.valueArray (List.replicate count.toNat initial))
                    (.valueArray (List.replicate count.toNat b)) statesRelated
                    (.valueArray _ _ (replicate_related f _ initial b initialRel))
                simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                  BviSem.toBvl, BviSem.fromBvl, nonnegative] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨f.updateEq (leastUnusedRef source.refs, leastUnusedRef target.refs),
                  .refPtr true (leastUnusedRef target.refs),
                  { target with refs := target.refs.updateEq (leastUnusedRef target.refs, .valueArray (List.replicate count.toNat b)) },
                  ?_, .refPtr _ _ true mapped, nextStates, submap, fresh, holes, unfinalised⟩
                simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                  BviSem.toBvl, BviSem.fromBvl, nonnegative]
        | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | block tag xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | refPtr flag ptr => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run

/-- Byte-array allocation preserves bytes and maps the fresh pointer. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_refByte {C F : Type} (f : HolFiniteMapExact Nat Nat) (flag : Bool)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp (.refByte flag)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp (.refByte flag))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp (.refByte flag)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | nil =>
        cases first <;> cases second <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        rename_i count byte
        cases valuesRelated with
        | @cons a b xs ys countRel tailRel =>
          cases countRel
          cases tailRel with
          | @cons a b xs ys byteRel tailRel =>
            cases byteRel
            cases tailRel
            by_cases negative : count < 0
            · simp [negative] at run
            · cases byteValue : ClosSem.intToByte byte with
              | none => simp [negative, byteValue] at run
              | some actual =>
                have ⟨mapped, nextStates, submap, fresh, holes, unfinalised⟩ :=
                  allocate_related f source target (.byteArray flag (List.replicate count.toNat actual))
                    (.byteArray flag (List.replicate count.toNat actual)) statesRelated (.byteArray flag _)
                simp [negative, byteValue] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨f.updateEq (leastUnusedRef source.refs, leastUnusedRef target.refs),
                  .refPtr true (leastUnusedRef target.refs),
                  { target with refs := target.refs.updateEq (leastUnusedRef target.refs, .byteArray flag (List.replicate count.toNat actual)) },
                  ?_, .refPtr _ _ true mapped, nextStates, submap, fresh, holes, unfinalised⟩
                simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, negative, byteValue]

/-- The length of a value array is unchanged by pointer renaming. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_length {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .length) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .length)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .length) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | nil =>
      cases first with
      | number i => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | block tag xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | refPtr flag ptr =>
        cases valuesRelated with
        | cons headRel tailRel =>
          cases tailRel
          cases headRel with
          | refPtr _ targetPtr _ mapped =>
            obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
              stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
            cases cells with
            | byteArray b bytes =>
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, sourceFound] at run
            | thunk mode x y rel =>
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, sourceFound] at run
            | valueArray xs ys rel =>
              have lengths := List.Forall₂.length_eq rel
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                BviSem.toBvl, BviSem.fromBvl, sourceFound] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨f, .number xs.length, target, ?_, .number _, statesRelated, ?_, onlyFresh_refl f target.refs,
                holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
              · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                  BviSem.toBvl, BviSem.fromBvl, targetFound, lengths]
              · intro key item found
                exact found

/-- The length of a byte array is unchanged by pointer renaming. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_lengthByte {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .lengthByte) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .lengthByte)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .lengthByte) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | nil =>
      cases first with
      | number i => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | block tag xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | refPtr flag ptr =>
        cases valuesRelated with
        | cons headRel tailRel =>
          cases tailRel
          cases headRel with
          | refPtr _ targetPtr _ mapped =>
            obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
              stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
            cases cells with
            | valueArray xs ys rel =>
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, sourceFound] at run
            | thunk mode x y rel =>
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, sourceFound] at run
            | byteArray b bytes =>
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                BviSem.toBvl, BviSem.fromBvl, sourceFound] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨f, .number bytes.length, target, ?_, .number _, statesRelated, ?_, onlyFresh_refl f target.refs,
                holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
              · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                  BviSem.toBvl, BviSem.fromBvl, targetFound]
              · intro key item found
                exact found

/-- Element reads return related values from either blocks or reference arrays. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_el {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .el) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .el)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .el) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases second with
        | number index =>
          cases valuesRelated with
          | @cons a b xs ys firstRel tailRel =>
            cases tailRel with
            | cons indexRel tailRel =>
              cases indexRel
              cases tailRel
              cases firstRel with
              | number i => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
              | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
              | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
              | block tag xs ys rel =>
                by_cases negative : index < 0
                · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, negative] at run
                · cases found : xs[index.toNat]? with
                  | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, negative, found] at run
                  | some v =>
                    obtain ⟨w, found', related⟩ := related_getElem f rel index.toNat v found
                    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                      BviSem.fromBvl_toBvl, negative, found] at run
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨f, w, target, ?_, related, statesRelated, ?_, onlyFresh_refl f target.refs,
                      holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                    · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                        BviSem.fromBvl_toBvl, negative, found']
                    · intro key item found
                      exact found
              | refPtr ptr targetPtr flag mapped =>
                obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
                  stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
                cases cells with
                | byteArray b bytes => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, sourceFound] at run
                | thunk mode x y rel => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, sourceFound] at run
                | valueArray xs ys rel =>
                  by_cases negative : index < 0
                  · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, sourceFound, negative] at run
                  · cases found : xs[index.toNat]? with
                    | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl, sourceFound, negative, found] at run
                    | some v =>
                      obtain ⟨w, found', related⟩ := related_getElem f rel index.toNat v found
                      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                        BviSem.toBvl, BviSem.fromBvl, sourceFound, negative, found] at run
                      obtain ⟨rfl, rfl⟩ := run
                      refine ⟨f, w, target, ?_, related, statesRelated, ?_, onlyFresh_refl f target.refs,
                        holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                      · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                          BviSem.toBvl, BviSem.fromBvl, targetFound, negative, found']
                      · intro key item found
                        exact found
        | word64 w => cases first <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | block tag xs => cases first <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | codePtr n => cases first <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | refPtr flag ptr => cases first <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run

/-- Reading a byte through a mapped pointer returns the same integer. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_derefByte {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .derefByte) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .derefByte)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .derefByte) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases first <;> cases second <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run
        rename_i flag ptr index
        cases valuesRelated with
        | cons ptrRel tailRel =>
          cases ptrRel with
          | refPtr _ targetPtr _ mapped =>
            cases tailRel with
            | cons indexRel tailRel =>
              cases indexRel
              cases tailRel
              obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
                stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
              cases cells with
              | valueArray xs ys rel => simp [sourceFound] at run
              | thunk mode x y rel => simp [sourceFound] at run
              | byteArray b bytes =>
                by_cases negative : index < 0
                · simp [sourceFound, negative] at run
                · cases found : bytes[index.toNat]? with
                  | none => simp [sourceFound, negative, found] at run
                  | some byte =>
                    simp [sourceFound, negative, found, BviSem.fromBvl] at run
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨f, .number byte.toNat, target, ?_, .number _, statesRelated, ?_,
                      onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                    · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                        BviSem.toBvl, BviSem.fromBvl, targetFound, negative, found]
                    · intro key item present
                      exact present

/-- Byte-array bounds checks agree for mapped pointers. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_boundsCheckByte {C F : Type} (f : HolFiniteMapExact Nat Nat) (loose : Bool)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp (.boundsCheckByte loose)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp (.boundsCheckByte loose))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp (.boundsCheckByte loose)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases first <;> cases second <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run
        rename_i flag ptr index
        cases valuesRelated with
        | cons ptrRel tailRel =>
          cases ptrRel with
          | refPtr _ targetPtr _ mapped =>
            cases tailRel with
            | cons indexRel tailRel =>
              cases indexRel
              cases tailRel
              obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
                stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
              cases cells with
              | valueArray xs ys rel => simp [sourceFound] at run
              | thunk mode x y rel => simp [sourceFound] at run
              | byteArray b bytes =>
                simp [sourceFound, BviSem.fromBvl] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨f, boolValue (decide (0 ≤ index ∧ if loose then index ≤ Int.ofNat bytes.length else index < Int.ofNat bytes.length)),
                  target, ?_, ?_, statesRelated, ?_,
                  onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                    BviSem.toBvl, BviSem.fromBvl, targetFound]
                · cases loose <;> by_cases h : 0 ≤ index <;> simp [h]
                  all_goals exact .block _ [] [] .nil
                · intro key item present
                  exact present

/-- Bounds checks agree for related value arrays of equal length. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_boundsCheckArray {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .boundsCheckArray) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .boundsCheckArray)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .boundsCheckArray) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases first <;> cases second <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run
        rename_i flag ptr index
        cases valuesRelated with
        | cons ptrRel tailRel =>
          cases ptrRel with
          | refPtr _ targetPtr _ mapped =>
            cases tailRel with
            | cons indexRel tailRel =>
              cases indexRel
              cases tailRel
              obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
                stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
              cases cells with
              | byteArray b bytes => simp [sourceFound] at run
              | thunk mode x y rel => simp [sourceFound] at run
              | valueArray xs ys rel =>
                have lengths := List.Forall₂.length_eq rel
                simp [sourceFound, BviSem.fromBvl] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨f, boolValue (decide (0 ≤ index ∧ index < Int.ofNat xs.length)),
                  target, ?_, ?_, statesRelated, ?_,
                  onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                    BviSem.toBvl, BviSem.fromBvl, targetFound, lengths]
                · by_cases h : 0 ≤ index <;> simp [h]
                  all_goals exact .block _ [] [] .nil
                · intro key item present
                  exact present

/-- Updating a value array preserves related cells and unrelated holes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_update {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .update) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .update)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .update) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | cons newValue rest =>
        cases rest with
        | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | nil =>
          cases first <;> cases second <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
            BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run
          rename_i flag ptr index
          cases valuesRelated with
          | cons ptrRel tailRel =>
            cases ptrRel with
            | refPtr _ targetPtr _ mapped =>
              cases tailRel with
              | cons indexRel tailRel =>
                cases indexRel
                cases tailRel with
                | @cons a b xs ys newRel tailRel =>
                  cases tailRel
                  obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
                    stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
                  cases cells with
                  | byteArray flag bytes => simp [sourceFound] at run
                  | thunk mode x y rel => simp [sourceFound] at run
                  | valueArray xs ys rel =>
                    by_cases invalid : index < 0 ∨ index.toNat ≥ xs.length
                    · simp [sourceFound, invalid] at run
                    · have invalid' : ¬(index < 0 ∨ index.toNat ≥ ys.length) := by
                        simpa [List.Forall₂.length_eq rel] using invalid
                      simp [sourceFound, invalid, BviSem.fromBvl] at run
                      obtain ⟨rfl, rfl⟩ := run
                      have nextRelated : stateRel f
                          { source with refs := source.refs.updateEq (ptr, .valueArray (xs.set index.toNat newValue)) }
                          { target with refs := target.refs.updateEq (targetPtr, .valueArray (ys.set index.toNat b)) } := by
                        exact ⟨stateRefRel_update f source.refs target.refs ptr targetPtr _ _ statesRelated.1
                          statesRelated.2.2.2.2.2.2.2.2.2.2 mapped
                          (.valueArray _ _ (related_set f rel index.toNat _ _ newRel)), statesRelated.2⟩
                      refine ⟨f, unitValue,
                        { target with refs := target.refs.updateEq (targetPtr, .valueArray (ys.set index.toNat b)) },
                        ?_, ?_, nextRelated, ?_, onlyFresh_refl f target.refs,
                        holesUnchanged_rangeUpdate f ptr targetPtr _ target.refs mapped,
                        holesStill_rangeUpdate f ptr targetPtr _ target.refs mapped⟩
                      · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                          BviSem.toBvl, BviSem.fromBvl, targetFound, invalid']
                      · exact .block _ [] [] .nil
                      · intro key item present
                        exact present

/-- Updating a byte array preserves its contents on both sides and leaves holes intact. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_updateByte {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .updateByte) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .updateByte)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .updateByte) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | cons third rest =>
        cases rest with
        | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | nil =>
          cases first <;> cases second <;> cases third <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
            BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run
          rename_i ptrFlag ptr index byte
          cases valuesRelated with
          | cons ptrRel tailRel =>
            cases ptrRel with
            | refPtr _ targetPtr _ mapped =>
              cases tailRel with
              | cons indexRel tailRel =>
                cases indexRel
                cases tailRel with
                | cons byteRel tailRel =>
                  cases byteRel
                  cases tailRel
                  obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
                    stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
                  cases cells with
                  | valueArray xs ys rel => simp [sourceFound] at run
                  | thunk mode x y rel => simp [sourceFound] at run
                  | byteArray flag bytes =>
                    by_cases invalid : index < 0 ∨ index.toNat ≥ bytes.length
                    · simp [sourceFound, invalid] at run
                    · cases converted : ClosSem.intToByte byte with
                      | none => simp [sourceFound, invalid, converted] at run
                      | some actual =>
                        simp [sourceFound, invalid, converted, BviSem.fromBvl] at run
                        obtain ⟨rfl, rfl⟩ := run
                        have nextRelated : stateRel f
                            { source with refs := source.refs.updateEq (ptr, .byteArray flag (bytes.set index.toNat actual)) }
                            { target with refs := target.refs.updateEq (targetPtr, .byteArray flag (bytes.set index.toNat actual)) } := by
                          exact ⟨stateRefRel_update f source.refs target.refs ptr targetPtr _ _ statesRelated.1
                            statesRelated.2.2.2.2.2.2.2.2.2.2 mapped (.byteArray _ _), statesRelated.2⟩
                        refine ⟨f, unitValue,
                          { target with refs := target.refs.updateEq (targetPtr, .byteArray flag (bytes.set index.toNat actual)) },
                          ?_, ?_, nextRelated, ?_, onlyFresh_refl f target.refs,
                          holesUnchanged_rangeUpdate f ptr targetPtr _ target.refs mapped,
                          holesStill_rangeUpdate f ptr targetPtr _ target.refs mapped⟩
                        · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                            BviSem.toBvl, BviSem.fromBvl, targetFound, invalid, converted]
                        · exact .block _ [] [] .nil
                        · intro key item present
                          exact present

/-- Comparing byte arrays gives the same result after pointer renaming. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_stringCmp {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (fast : Bool) (op : Opb) (values relatedValues : List Value)
    (source sourceNext : BviState (Nat × C) F) (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp (.stringCmp fast op)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp (.stringCmp fast op))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp (.stringCmp fast op)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases first <;> cases second <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run
        rename_i flag1 ptr1 flag2 ptr2
        cases valuesRelated with
        | cons ptrRel tailRel =>
          cases ptrRel with
          | refPtr _ targetPtr1 _ mapped1 =>
            cases tailRel with
            | cons ptrRel tailRel =>
              cases ptrRel with
              | refPtr _ targetPtr2 _ mapped2 =>
                cases tailRel
                obtain ⟨_, _, sourceFound1, targetFound1, cells1⟩ :=
                  stateRefRel_lookup f ptr1 targetPtr1 source.refs target.refs mapped1 statesRelated.1
                obtain ⟨_, _, sourceFound2, targetFound2, cells2⟩ :=
                  stateRefRel_lookup f ptr2 targetPtr2 source.refs target.refs mapped2 statesRelated.1
                cases cells1 with
                | valueArray xs ys rel => simp [sourceFound1] at run
                | thunk mode x y rel => simp [sourceFound1] at run
                | byteArray b1 bytes1 =>
                  cases cells2 with
                  | valueArray xs ys rel => simp [sourceFound1, sourceFound2] at run
                  | thunk mode x y rel => simp [sourceFound1, sourceFound2] at run
                  | byteArray b2 bytes2 =>
                    simp [sourceFound1, sourceFound2, BviSem.fromBvl] at run
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨f, boolValue (SemanticPrimitivesHOL.strCmp fast op
                      (Basis.Pure.MlString.MlString.implode bytes1) (Basis.Pure.MlString.MlString.implode bytes2)),
                      target, ?_, ?_, statesRelated, ?_, onlyFresh_refl f target.refs,
                      holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                    · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                        BviSem.toBvl, BviSem.fromBvl, targetFound1, targetFound2]
                    · exact .block _ [] [] .nil
                    · intro key item present
                      exact present

/-- Bytewise XOR updates corresponding destination arrays identically. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_xorByte {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .xorByte) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .xorByte)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .xorByte) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases first <;> cases second <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyMemory, BviSem.toBvl] at run
        rename_i flag1 ptr1 flag2 ptr2
        cases valuesRelated with
        | cons ptrRel tailRel =>
          cases ptrRel with
          | refPtr _ targetPtr1 _ mapped1 =>
            cases tailRel with
            | cons ptrRel tailRel =>
              cases ptrRel with
              | refPtr _ targetPtr2 _ mapped2 =>
                cases tailRel
                obtain ⟨_, _, sourceFound1, targetFound1, cells1⟩ :=
                  stateRefRel_lookup f ptr1 targetPtr1 source.refs target.refs mapped1 statesRelated.1
                obtain ⟨_, _, sourceFound2, targetFound2, cells2⟩ :=
                  stateRefRel_lookup f ptr2 targetPtr2 source.refs target.refs mapped2 statesRelated.1
                cases cells2 with
                | valueArray xs ys rel => simp [sourceFound2] at run
                | thunk mode x y rel => simp [sourceFound2] at run
                | byteArray b2 bytes2 =>
                  cases cells1 with
                  | valueArray xs ys rel => simp [sourceFound1, sourceFound2] at run
                  | thunk mode x y rel => simp [sourceFound1, sourceFound2] at run
                  | byteArray b1 bytes1 =>
                    cases result : SemanticPrimitivesHOL.xorBytes bytes2 bytes1 with
                    | none => simp [sourceFound1, sourceFound2, result] at run
                    | some updated =>
                      simp [sourceFound1, sourceFound2, result, BviSem.fromBvl] at run
                      obtain ⟨rfl, rfl⟩ := run
                      have nextRelated : stateRel f
                          { source with refs := source.refs.updateEq (ptr1, .byteArray b1 updated) }
                          { target with refs := target.refs.updateEq (targetPtr1, .byteArray b1 updated) } := by
                        exact ⟨stateRefRel_update f source.refs target.refs ptr1 targetPtr1 _ _ statesRelated.1
                          statesRelated.2.2.2.2.2.2.2.2.2.2 mapped1 (.byteArray _ _), statesRelated.2⟩
                      refine ⟨f, unitValue, { target with refs := target.refs.updateEq (targetPtr1, .byteArray b1 updated) },
                        ?_, ?_, nextRelated, ?_, onlyFresh_refl f target.refs,
                        holesUnchanged_rangeUpdate f ptr1 targetPtr1 _ target.refs mapped1,
                        holesStill_rangeUpdate f ptr1 targetPtr1 _ target.refs mapped1⟩
                      · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                          BviSem.toBvl, BviSem.fromBvl, targetFound1, targetFound2, result]
                      · exact .block _ [] [] .nil
                      · intro key item present
                        exact present

/-- Garbage-collector configuration leaves related states unchanged. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_configGC {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .configGC) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .configGC)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .configGC) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | nil =>
        cases first <;> cases second <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyMemory, BviSem.fromBvl_toBvl] at run
        obtain ⟨rfl, rfl⟩ := run
        cases valuesRelated with
        | cons firstRel tailRel =>
          cases firstRel
          cases tailRel with
          | cons secondRel tailRel =>
            cases secondRel
            cases tailRel
            refine ⟨f, unitValue, target, ?_, ?_, statesRelated, ?_, onlyFresh_refl f target.refs,
              holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
            · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                BviSem.fromBvl_toBvl]
            · exact .block _ [] [] .nil
            · intro key item present
              exact present

/-- Flapjack infrastructure for memory cases rejected by the BVI dispatcher. -/
private theorem rejected_memory_simulation {C F : Type} (f : HolFiniteMapExact Nat Nat) (op : ClosLang.MemOp)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value) (rejected : BviTailrec.memoryRejected op = true)
    (run : BviSem.doApp (.memOp op) values source = .val (value, sourceNext)) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp op) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  rw [BviTailrec.doApp_memory_rejected op values source rejected] at run
  contradiction

/-- The directly rejected byte-list conversion case. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_fromListByte {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .fromListByte) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .fromListByte)) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .fromListByte) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs :=
  rejected_memory_simulation f .fromListByte values relatedValues source sourceNext target value rfl run

/-- The directly rejected byte-array-to-list conversion case. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_toListByte {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .toListByte) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .toListByte)) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .toListByte) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs :=
  rejected_memory_simulation f .toListByte values relatedValues source sourceNext target value rfl run

/-- The directly rejected byte-vector concatenation case. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_concatByteVec {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .concatByteVec) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .concatByteVec)) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .concatByteVec) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs :=
  rejected_memory_simulation f .concatByteVec values relatedValues source sourceNext target value rfl run

/-- The directly rejected allocating byte-copy case. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_copyByte_new {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp (.copyByte true)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp (.copyByte true))) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp (.copyByte true)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs :=
  rejected_memory_simulation f (.copyByte true) values relatedValues source sourceNext target value rfl run

/-- Mutable-constructor allocation is excluded by the original pass premise. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_mutCons {C F : Type} (f : HolFiniteMapExact Nat Nat) (tag index : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (_run : BviSem.doApp (.memOp (.mutCons tag index)) values source = .val (value, sourceNext))
    (noMutcons : noMutconsOp (.memOp (.mutCons tag index))) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp (.mutCons tag index)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  exact (noMutcons tag index rfl).elim

/-- Byte-vector length is rejected by the delegated BVL dispatcher. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_lengthByteVec {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .lengthByteVec) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .lengthByteVec)) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .lengthByteVec) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run

/-- Byte-vector dereference is rejected by the delegated BVL dispatcher. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_derefByteVec {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp .derefByteVec) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp .derefByteVec)) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp .derefByteVec) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run

/-- In-place byte copying preserves related heaps for independently mapped
source and destination pointers, including when the pointers alias. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_copyByte_inPlace {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp (.copyByte false)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.memOp (.copyByte false))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp (.copyByte false)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | cons third rest =>
        cases rest with
        | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | cons fourth rest =>
          cases rest with
          | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | cons fifth rest =>
            cases rest with
            | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
            | nil =>
              cases first <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
              cases second <;> try simp at run
              cases third <;> try simp at run
              cases fourth <;> try simp at run
              cases fifth <;> simp [BviSem.toBvl] at run
              rename_i srcFlag src offset count dstFlag dst dstOffset
              cases valuesRelated with
              | cons srcRel tailRel =>
                cases srcRel with
                | refPtr _ targetSrc _ srcMapped =>
                  cases tailRel with
                  | cons offsetRel tailRel =>
                    cases offsetRel
                    cases tailRel with
                    | cons countRel tailRel =>
                      cases countRel
                      cases tailRel with
                      | cons dstRel tailRel =>
                        cases dstRel with
                        | refPtr _ targetDst _ dstMapped =>
                          cases tailRel with
                          | cons dstOffsetRel tailRel =>
                            cases dstOffsetRel
                            cases tailRel
                            obtain ⟨_, _, sourceFound, targetFound, sourceCells⟩ :=
                              stateRefRel_lookup f src targetSrc source.refs target.refs srcMapped statesRelated.1
                            obtain ⟨_, _, destFound, targetDestFound, destCells⟩ :=
                              stateRefRel_lookup f dst targetDst source.refs target.refs dstMapped statesRelated.1
                            cases sourceCells with
                            | valueArray xs ys rel => simp [sourceFound] at run
                            | thunk mode x y rel => simp [sourceFound] at run
                            | byteArray sourceFlag sourceBytes =>
                              cases destCells with
                              | valueArray xs ys rel => simp [sourceFound, destFound] at run
                              | thunk mode x y rel => simp [sourceFound, destFound] at run
                              | byteArray destFlag destBytes =>
                                cases copied : SemanticPrimitivesHOL.copyArray (sourceBytes, offset) count (some (destBytes, dstOffset)) with
                                | none => simp [sourceFound, destFound, copied] at run
                                | some updated =>
                                  simp [sourceFound, destFound, copied, BviSem.fromBvl] at run
                                  obtain ⟨rfl, rfl⟩ := run
                                  have nextRelated : stateRel f
                                      { source with refs := source.refs.updateEq (dst, .byteArray destFlag updated) }
                                      { target with refs := target.refs.updateEq (targetDst, .byteArray destFlag updated) } := by
                                    exact ⟨stateRefRel_update f source.refs target.refs dst targetDst _ _ statesRelated.1
                                      statesRelated.2.2.2.2.2.2.2.2.2.2 dstMapped (.byteArray _ _), statesRelated.2⟩
                                  refine ⟨f, unitValue,
                                    { target with refs := target.refs.updateEq (targetDst, .byteArray destFlag updated) },
                                    ?_, ?_, nextRelated, ?_, onlyFresh_refl f target.refs,
                                    holesUnchanged_rangeUpdate f dst targetDst _ target.refs dstMapped,
                                    holesStill_rangeUpdate f dst targetDst _ target.refs dstMapped⟩
                                  · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
                                      BviSem.toBvl, BviSem.fromBvl, targetFound, targetDestFound, copied]
                                  · exact .block _ [] [] .nil
                                  · intro key item present
                                    exact present

/-- Every memory operation satisfies the source primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_mem {C F : Type} (f : HolFiniteMapExact Nat Nat) (op : ClosLang.MemOp)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.memOp op) values source = .val (value, sourceNext))
    (noMutcons : noMutconsOp (.memOp op)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.memOp op) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases op with
  | ref => exact doApp_op_rel_ref f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | update => exact doApp_op_rel_update f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | el => exact doApp_op_rel_el f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | length => exact doApp_op_rel_length f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | lengthByte => exact doApp_op_rel_lengthByte f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | refByte flag => exact doApp_op_rel_refByte f flag values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | refArray => exact doApp_op_rel_refArray f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | derefByte => exact doApp_op_rel_derefByte f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | updateByte => exact doApp_op_rel_updateByte f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | concatByteVec => exact doApp_op_rel_concatByteVec f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | copyByte flag =>
    cases flag with
    | false => exact doApp_op_rel_copyByte_inPlace f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
    | true => exact doApp_op_rel_copyByte_new f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | fromListByte => exact doApp_op_rel_fromListByte f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | toListByte => exact doApp_op_rel_toListByte f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | lengthByteVec => exact doApp_op_rel_lengthByteVec f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | derefByteVec => exact doApp_op_rel_derefByteVec f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | stringCmp fast comparison => exact doApp_op_rel_stringCmp f fast comparison values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | xorByte => exact doApp_op_rel_xorByte f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | boundsCheckArray => exact doApp_op_rel_boundsCheckArray f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | boundsCheckByte loose => exact doApp_op_rel_boundsCheckByte f loose values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | mutCons tag index => exact doApp_op_rel_mutCons f tag index values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | updateCons => exact doApp_op_rel_updateCons f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | finaliseCons => exact doApp_op_rel_finaliseCons f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | configGC => exact doApp_op_rel_configGC f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated

/-- Structural equality gives the same result on related values and heaps. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_equal {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp .equal) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp .equal)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp .equal) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | nil =>
        cases valuesRelated with
        | @cons a first' xs ys firstRel tailRel =>
          cases tailRel with
          | @cons a second' xs ys secondRel tailRel =>
            cases tailRel
            have equalResult := (doEq_value_rel f).1 source.refs first second target.refs first' second'
              firstRel secondRel statesRelated.1 statesRelated.2.2.2.2.2.2.2.2.2.2
            cases result : doEq source.refs first second with
            | typeError => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                BviSem.toBvl, result] at run
            | val boolean =>
              have targetResult : doEq target.refs first' second' = .val boolean := by rw [← equalResult, result]
              simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                BviSem.toBvl, BviSem.fromBvl, result] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨f, boolValue boolean, target, ?_, .block _ [] [] .nil, statesRelated, ?_,
                onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
              · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                  BviSem.toBvl, BviSem.fromBvl, targetResult]
              · intro key item present
                exact present

/-- Constructing a block preserves its pointwise-related fields. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_cons {C F : Type} (f : HolFiniteMapExact Nat Nat) (tag : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.cons tag)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.cons tag))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.cons tag)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
    BviSem.fromBvl_toBvl] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨f, .block tag relatedValues, target, ?_, .block _ _ _ valuesRelated, statesRelated, ?_,
    onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
  · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
      BviSem.fromBvl_toBvl]
  · intro key item present
    exact present

/-- Converting a related list to a block preserves all of its fields. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_fromList {C F : Type} (f : HolFiniteMapExact Nat Nat) (tag : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.fromList tag)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.fromList tag))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.fromList tag)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons length rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | cons list rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | nil =>
        cases length <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        rename_i count
        cases valuesRelated with
        | cons lengthRel tailRel =>
          cases lengthRel
          cases tailRel with
          | @cons a targetList xs ys listRel tailRel =>
            cases tailRel
            cases decoded : valueToList list with
            | none => simp [decoded] at run
            | some fields =>
              obtain ⟨targetFields, targetDecoded, fieldsRel⟩ := valueToList_rel f list fields targetList decoded listRel
              by_cases countOk : count = Int.ofNat fields.length
              · have countOk' : count = Int.ofNat targetFields.length := by simpa [List.Forall₂.length_eq fieldsRel] using countOk
                simp [decoded, countOk] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨f, .block tag targetFields, target, ?_, .block _ _ _ fieldsRel, statesRelated, ?_,
                  onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, targetDecoded, countOk']
                · intro key item present
                  exact present
              · simp [decoded] at run
                change count ≠ (fields.length : Int) at countOk
                simp [countOk] at run

private theorem related_append (f : HolFiniteMapExact Nat Nat) {xs ys xs' ys' : List Value}
    (first : List.Forall₂ (valueRel f) xs ys) (second : List.Forall₂ (valueRel f) xs' ys') :
    List.Forall₂ (valueRel f) (xs ++ xs') (ys ++ ys') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

/-- Appending related list values produces related lists. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_listAppend {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp .listAppend) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp .listAppend)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp .listAppend) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | nil =>
        cases valuesRelated with
        | @cons a targetFirst xs ys firstRel tailRel =>
          cases tailRel with
          | @cons a targetSecond xs ys secondRel tailRel =>
            cases tailRel
            cases decodedFirst : valueToList first with
            | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, decodedFirst] at run
            | some fieldsFirst =>
              cases decodedSecond : valueToList second with
              | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, decodedFirst, decodedSecond] at run
              | some fieldsSecond =>
                obtain ⟨targetFieldsFirst, targetDecodedFirst, firstFieldsRel⟩ :=
                  valueToList_rel f first fieldsFirst targetFirst decodedFirst firstRel
                obtain ⟨targetFieldsSecond, targetDecodedSecond, secondFieldsRel⟩ :=
                  valueToList_rel f second fieldsSecond targetSecond decodedSecond secondRel
                simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                  BviSem.fromBvl_toBvl, decodedFirst, decodedSecond] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨f, listToValue (targetFieldsFirst ++ targetFieldsSecond), target, ?_,
                  listToValue_rel f _ _ (related_append f firstFieldsRel secondFieldsRel), statesRelated, ?_,
                  onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                    BviSem.fromBvl_toBvl, targetDecodedFirst, targetDecodedSecond]
                · intro key item present
                  exact present

private theorem elemAt_eq_el {C F : Type} (index : Nat) (argument : Value) (state : BviState C F) :
    BviSem.doApp (.blockOp (.elemAt index)) [argument] state =
      BviSem.doApp (.memOp .el) [argument, .number (Int.ofNat index)] state := by
  have nonnegative : ¬((index : Int) < 0) := by omega
  cases argument <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyBlock, BvlSem.applyMemory, nonnegative]
  rename_i flag ptr
  cases found : (BviSem.toBvl state).refs.lookup ptr with
  | none => simp
  | some cell => cases cell <;> simp

/-- Indexed block access agrees with the corresponding array-element read. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_elemAt {C F : Type} (f : HolFiniteMapExact Nat Nat) (index : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.elemAt index)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.elemAt index))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.elemAt index)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases valuesRelated with
      | @cons a targetFirst xs ys firstRel tailRel =>
        cases tailRel
        rw [elemAt_eq_el] at run
        obtain ⟨nextMap, value', targetNext, targetRun, valueRel, stateRel, submap, fresh, holes, unfinalised⟩ :=
          doApp_op_rel_el f [first, .number (Int.ofNat index)] [targetFirst, .number (Int.ofNat index)]
            source sourceNext target value run (by simp [noMutconsOp])
            (.cons firstRel (.cons (.number _) .nil)) statesRelated
        exact ⟨nextMap, value', targetNext, (elemAt_eq_el index targetFirst target).trans targetRun,
          valueRel, stateRel, submap, fresh, holes, unfinalised⟩

/-- Related blocks have the same length. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_lengthBlock {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp .lengthBlock) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp .lengthBlock)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp .lengthBlock) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases valuesRelated with
      | cons firstRel tailRel =>
        cases tailRel
        cases firstRel with
        | number i => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | refPtr a b flag mapped => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | block tag xs ys rel =>
          have lengths := List.Forall₂.length_eq rel
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
            BviSem.fromBvl_toBvl] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨f, .number xs.length, target, ?_, .number _, statesRelated, ?_, onlyFresh_refl f target.refs,
            holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
          · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
              BviSem.fromBvl_toBvl, lengths]
          · intro key item present
            exact present

/-- Tag and length tests agree on related blocks. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_tagLenEq {C F : Type} (f : HolFiniteMapExact Nat Nat) (tag length : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.tagLenEq tag length)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.tagLenEq tag length))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.tagLenEq tag length)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases valuesRelated with
      | cons firstRel tailRel =>
        cases tailRel
        cases firstRel with
        | number i => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | refPtr a b flag mapped => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | block actual xs ys rel =>
          have lengths := List.Forall₂.length_eq rel
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
            BviSem.fromBvl_toBvl] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨f, boolValue (actual == tag && xs.length == length), target, ?_, .block _ [] [] .nil, statesRelated, ?_,
            onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
          · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
              BviSem.fromBvl_toBvl, lengths]
          · intro key item present
            exact present


/-- Length tests agree on related blocks. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_lenEq {C F : Type} (f : HolFiniteMapExact Nat Nat) (length : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.lenEq length)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.lenEq length))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.lenEq length)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases valuesRelated with
      | cons firstRel tailRel =>
        cases tailRel
        cases firstRel with
        | number i => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | refPtr a b flag mapped => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | block actual xs ys rel =>
          have lengths := List.Forall₂.length_eq rel
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
            BviSem.fromBvl_toBvl] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨f, boolValue (xs.length == length), target, ?_, .block _ [] [] .nil, statesRelated, ?_,
            onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
          · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
              BviSem.fromBvl_toBvl, lengths]
          · intro key item present
            exact present


/-- Tag tests agree on related blocks. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_tagEq {C F : Type} (f : HolFiniteMapExact Nat Nat) (tag : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.tagEq tag)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.tagEq tag))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.tagEq tag)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases valuesRelated with
      | cons firstRel tailRel =>
        cases tailRel
        cases firstRel with
        | number i => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | refPtr a b flag mapped => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | block actual xs ys rel =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
            BviSem.fromBvl_toBvl] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨f, boolValue (actual == tag), target, ?_, .block _ [] [] .nil, statesRelated, ?_,
            onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
          · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
              BviSem.fromBvl_toBvl]
          · intro key item present
            exact present

private theorem asBool_related (f : HolFiniteMapExact Nat Nat) (v w : Value)
    (related : valueRel f v w) : asBool v = asBool w := by
  cases related with
  | number i => rfl
  | word64 w => rfl
  | codePtr n => rfl
  | refPtr n m flag mapped => rfl
  | block tag xs ys fields =>
    cases fields <;> simp [asBool]

/-- Boolean negation agrees on related values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_boolNot {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp .boolNot) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp .boolNot)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp .boolNot) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases valuesRelated with
      | @cons a targetFirst xs ys firstRel tailRel =>
        cases tailRel
        have same := asBool_related f first targetFirst firstRel
        cases decoded : asBool first with
        | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, decoded] at run
        | some boolean =>
          have targetDecoded : asBool targetFirst = some boolean := by rw [← same, decoded]
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
            BviSem.fromBvl_toBvl, decoded] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨f, boolValue (!boolean), target, ?_, .block _ [] [] .nil, statesRelated, ?_,
            onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
          · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
              BviSem.fromBvl_toBvl, targetDecoded]
          · intro key item present
            exact present

/-- Boolean tests agree on related operands. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_boolTest {C F : Type} (f : HolFiniteMapExact Nat Nat) (test : AstHOL.Test)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.boolTest test)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.boolTest test))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.boolTest test)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | nil =>
        cases valuesRelated with
        | @cons a targetFirst xs ys firstRel tailRel =>
          cases tailRel with
          | @cons a targetSecond xs ys secondRel tailRel =>
            cases tailRel
            have sameFirst := asBool_related f first targetFirst firstRel
            have sameSecond := asBool_related f second targetSecond secondRel
            cases decodedFirst : asBool first with
            | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, decodedFirst] at run
            | some firstBool =>
              cases decodedSecond : asBool second with
              | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, decodedFirst, decodedSecond] at run
              | some secondBool =>
                have targetFirstDecoded : asBool targetFirst = some firstBool := by rw [← sameFirst, decodedFirst]
                have targetSecondDecoded : asBool targetSecond = some secondBool := by rw [← sameSecond, decodedSecond]
                simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                  BviSem.fromBvl_toBvl, decodedFirst, decodedSecond] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨f, boolValue (firstBool == secondBool), target, ?_, .block _ [] [] .nil, statesRelated, ?_,
                  onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                    BviSem.fromBvl_toBvl, targetFirstDecoded, targetSecondDecoded]
                · intro key item present
                  exact present

/-- Bounds checks return the same boolean for related blocks. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_boundsCheckBlock {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp .boundsCheckBlock) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp .boundsCheckBlock)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp .boundsCheckBlock) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | nil =>
        cases first <;> cases second <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyBlock, BviSem.fromBvl_toBvl] at run
        rename_i tag fields index
        cases valuesRelated with
        | cons blockRel tailRel =>
          cases blockRel with
          | block _ _ targetFields fieldsRel =>
            cases tailRel with
            | cons indexRel tailRel =>
              cases indexRel
              cases tailRel
              have lengths := List.Forall₂.length_eq fieldsRel
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨f, boolValue (decide (0 ≤ index ∧ index < Int.ofNat fields.length)),
                target, ?_, ?_, statesRelated, ?_, onlyFresh_refl f target.refs,
                holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
              · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                  BviSem.fromBvl_toBvl, lengths]
              · by_cases h : 0 ≤ index <;> simp [h]
                all_goals exact .block _ [] [] .nil
              · intro key item present
                exact present

/-- Constant construction preserves the state relation across fresh strings. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_build {C F : Type} (f : HolFiniteMapExact Nat Nat) (parts : List ClosLang.ConstPart)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.build parts)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.build parts))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.build parts)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | cons first rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | nil =>
    cases valuesRelated
    cases built : doBuildConst parts source.refs with
    | mk builtValue builtRefs =>
      obtain ⟨nextMap, targetValue, targetRefs, targetRun, valueRel, heaps, inj, submap, fresh, holes, still⟩ :=
        doBuildConst_value_rel parts source.refs builtValue builtRefs f target.refs built statesRelated.1
          statesRelated.2.2.2.2.2.2.2.2.2.2
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
        BviSem.toBvl, BviSem.fromBvl, built] at run
      obtain ⟨rfl, rfl⟩ := run
      have nextStates : stateRel nextMap { source with refs := builtRefs } { target with refs := targetRefs } := by
        rcases statesRelated with ⟨_, clock, global, ffi, oracle, compiler, code, names, inputs, workers, _⟩
        refine ⟨heaps, clock, ?_, ffi, oracle, compiler, code, names, inputs, workers, inj⟩
        cases hs : source.global <;> cases ht : target.global <;> simp_all
        exact submap _ _ global
      refine ⟨nextMap, targetValue, { target with refs := targetRefs }, ?_, valueRel, nextStates, submap, fresh, holes, still⟩
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
        BviSem.toBvl, BviSem.fromBvl, targetRun]

/-- Block extension preserves the related prefix and selected slice. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_consExtend {C F : Type} (f : HolFiniteMapExact Nat Nat) (tag : Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.consExtend tag)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.consExtend tag))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.consExtend tag)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | cons second rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
      | cons third rest =>
        cases rest with
        | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
        | cons fourth initial =>
          cases first <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
          cases second <;> try simp at run
          cases third <;> try simp at run
          cases fourth <;> try simp at run
          rename_i oldTag fields lower len total
          cases valuesRelated with
          | cons blockRel tailRel =>
            cases blockRel with
            | block _ _ targetFields fieldsRel =>
              cases tailRel with
              | cons lowerRel tailRel =>
                cases lowerRel
                cases tailRel with
                | cons lenRel tailRel =>
                  cases lenRel
                  cases tailRel with
                  | @cons a b xs targetInitial totalRel initialRel =>
                    cases totalRel
                    have lengths := List.Forall₂.length_eq fieldsRel
                    have initialLengths := List.Forall₂.length_eq initialRel
                    by_cases invalid : lower < 0 ∨ len < 0 ∨ (fields.length : Int) < lower + len ∨
                        total = 0 ∨ total ≠ (initial.length : Int) + len
                    · simp [invalid] at run
                    · have invalid' : ¬(lower < 0 ∨ len < 0 ∨ (targetFields.length : Int) < lower + len ∨
                          total = 0 ∨ total ≠ (targetInitial.length : Int) + len) := by
                        simpa [lengths, initialLengths] using invalid
                      simp [invalid, BviSem.fromBvl_toBvl] at run
                      obtain ⟨rfl, rfl⟩ := run
                      have fieldsRelated : List.Forall₂ (valueRel f)
                          (initial ++ (fields.drop lower.toNat).take len.toNat)
                          (targetInitial ++ (targetFields.drop lower.toNat).take len.toNat) :=
                        related_append f initialRel (List.forall₂_take _ (List.forall₂_drop _ fieldsRel))
                      refine ⟨f, .block tag _, target, ?_, .block _ _ _ fieldsRelated, statesRelated, ?_,
                        onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
                      · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                          BviSem.fromBvl_toBvl, invalid']
                      · intro key item present
                        exact present

/-- Constant comparison agrees for related values, including string references. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_equalConst {C F : Type} (f : HolFiniteMapExact Nat Nat) (part : ClosLang.ConstPart)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.equalConst part)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.equalConst part))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.equalConst part)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
    | nil =>
      cases valuesRelated with
      | cons firstRel tailRel =>
        cases tailRel
        cases part <;> cases firstRel <;> simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, BviSem.fromBvl] at run
        case int.number =>
          rename_i constant number
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨f, boolValue (decide (constant = number)), target, ?_, .block _ [] [] .nil,
            statesRelated, ?_, onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
          · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
              BviSem.toBvl, BviSem.fromBvl]
          · intro key item present
            exact present
        case w64.word64 =>
          rename_i constant word
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨f, boolValue (decide (constant = word)), target, ?_, .block _ [] [] .nil,
            statesRelated, ?_, onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
          · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
              BviSem.toBvl, BviSem.fromBvl]
          · intro key item present
            exact present
        case str.refPtr =>
          rename_i text ptr targetPtr flag mapped
          obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
            stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
          cases cells with
          | valueArray xs ys rel => simp [sourceFound] at run
          | thunk mode x y rel => simp [sourceFound] at run
          | byteArray mutable bytes =>
            cases mutable with
            | false => simp [sourceFound] at run
            | true =>
              simp [sourceFound] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨f, boolValue (decide (bytes = text.explode)), target, ?_, .block _ [] [] .nil,
                statesRelated, ?_, onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
              · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock,
                  BviSem.toBvl, BviSem.fromBvl, targetFound]
              · intro key item present
                exact present

/-- The BVI/BVL dispatcher rejects the obsolete constant operation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_constant {C F : Type} (f : HolFiniteMapExact Nat Nat) (constant : ClosLang.Const)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp (.constant constant)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.blockOp (.constant constant))) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp (.constant constant)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run

/-- Every block operation satisfies the source primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_block {C F : Type} (f : HolFiniteMapExact Nat Nat) (op : ClosLang.BlockOp)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.blockOp op) values source = .val (value, sourceNext))
    (noMutcons : noMutconsOp (.blockOp op)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.blockOp op) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases op with
  | cons tag => exact doApp_op_rel_cons f tag values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | elemAt index => exact doApp_op_rel_elemAt f index values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | tagLenEq tag length => exact doApp_op_rel_tagLenEq f tag length values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | lenEq length => exact doApp_op_rel_lenEq f length values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | tagEq tag => exact doApp_op_rel_tagEq f tag values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | lengthBlock => exact doApp_op_rel_lengthBlock f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | boolTest test => exact doApp_op_rel_boolTest f test values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | boolNot => exact doApp_op_rel_boolNot f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | boundsCheckBlock => exact doApp_op_rel_boundsCheckBlock f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | consExtend tag => exact doApp_op_rel_consExtend f tag values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | fromList tag => exact doApp_op_rel_fromList f tag values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | listAppend => exact doApp_op_rel_listAppend f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | constant constant => exact doApp_op_rel_constant f constant values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | equal => exact doApp_op_rel_equal f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | equalConst part => exact doApp_op_rel_equalConst f part values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | build parts => exact doApp_op_rel_build f parts values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated

/-- Allocating a thunk preserves its related payload and extends the pointer map. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_allocThunk {C F : Type} (f : HolFiniteMapExact Nat Nat) (mode : AstHOL.ThunkMode)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.thunkOp (.allocThunk mode)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.thunkOp (.allocThunk mode))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.thunkOp (.allocThunk mode)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
  | cons first rest =>
    cases rest with
    | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
    | nil =>
      cases valuesRelated with
      | @cons a targetFirst xs ys firstRel tailRel =>
        cases tailRel
        by_cases bad : BvlSem.badThunkUpdate mode first source.refs
        · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, bad] at run
        · have targetGood := goodThunkUpdate_rel mode first targetFirst source.refs target.refs f bad firstRel statesRelated.1
          have ⟨mapped, nextStates, submap, fresh, holes, unfinalised⟩ :=
            allocate_related f source target (.thunk mode first) (.thunk mode targetFirst) statesRelated
              (.thunk mode first targetFirst firstRel)
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
            BviSem.toBvl, BviSem.fromBvl, bad] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨f.updateEq (leastUnusedRef source.refs, leastUnusedRef target.refs),
            .refPtr false (leastUnusedRef target.refs),
            { target with refs := target.refs.updateEq (leastUnusedRef target.refs, .thunk mode targetFirst) },
            ?_, .refPtr _ _ false mapped, nextStates, submap, fresh, holes, unfinalised⟩
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
            BviSem.toBvl, BviSem.fromBvl, targetGood]

/-- Updating a thunk preserves related payloads and untouched mutable holes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_updateThunk {C F : Type} (f : HolFiniteMapExact Nat Nat) (mode : AstHOL.ThunkMode)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.thunkOp (.updateThunk mode)) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.thunkOp (.updateThunk mode))) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.thunkOp (.updateThunk mode)) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases values with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
    | cons payload rest =>
      cases rest with
      | cons extra rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
      | nil =>
        cases first with
        | number i => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | word64 w => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | block tag xs => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | codePtr n => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
        | refPtr flag ptr =>
          cases flag with
          | true => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run
          | false =>
            cases valuesRelated with
            | cons ptrRel tailRel =>
              cases ptrRel with
              | refPtr _ targetPtr _ mapped =>
                cases tailRel with
                | @cons a targetPayload xs ys payloadRel tailRel =>
                  cases tailRel
                  by_cases bad : BvlSem.badThunkUpdate mode payload source.refs
                  · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, bad] at run
                  · have targetGood := goodThunkUpdate_rel mode payload targetPayload source.refs target.refs f bad payloadRel statesRelated.1
                    obtain ⟨_, _, sourceFound, targetFound, cells⟩ :=
                      stateRefRel_lookup f ptr targetPtr source.refs target.refs mapped statesRelated.1
                    cases cells with
                    | byteArray b bytes => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, bad, sourceFound] at run
                    | valueArray xs ys rel => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, bad, sourceFound] at run
                    | thunk oldMode oldValue targetOld rel =>
                      cases oldMode with
                      | evaluated => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BviSem.toBvl, bad, sourceFound] at run
                      | notEvaluated =>
                        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
                          BviSem.toBvl, BviSem.fromBvl, bad, sourceFound] at run
                        obtain ⟨rfl, rfl⟩ := run
                        have nextStates : stateRel f
                            { source with refs := source.refs.updateEq (ptr, .thunk mode payload) }
                            { target with refs := target.refs.updateEq (targetPtr, .thunk mode targetPayload) } := by
                          exact ⟨stateRefRel_update f source.refs target.refs ptr targetPtr _ _ statesRelated.1
                            statesRelated.2.2.2.2.2.2.2.2.2.2 mapped (.thunk _ _ _ payloadRel), statesRelated.2⟩
                        refine ⟨f, unitValue, { target with refs := target.refs.updateEq (targetPtr, .thunk mode targetPayload) },
                          ?_, .block _ [] [] .nil, nextStates, ?_, onlyFresh_refl f target.refs,
                          holesUnchanged_rangeUpdate f ptr targetPtr _ target.refs mapped,
                          holesStill_rangeUpdate f ptr targetPtr _ target.refs mapped⟩
                        · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
                            BviSem.toBvl, BviSem.fromBvl, targetGood, targetFound]
                        · intro key item present
                          exact present

/-- The force-thunk primitive is rejected by the BVL dispatcher. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_forceThunk {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.thunkOp .forceThunk) values source = .val (value, sourceNext))
    (_noMutcons : noMutconsOp (.thunkOp .forceThunk)) (_valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (_statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.thunkOp .forceThunk) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp] at run

/-- Every thunk operation satisfies the source primitive simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f, nextMap])]
theorem doApp_op_rel_thunk {C F : Type} (f : HolFiniteMapExact Nat Nat) (op : AstHOL.ThunkOp)
    (values relatedValues : List Value) (source sourceNext : BviState (Nat × C) F)
    (target : BviState C F) (value : Value)
    (run : BviSem.doApp (.thunkOp op) values source = .val (value, sourceNext))
    (noMutcons : noMutconsOp (.thunkOp op)) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues)
    (statesRelated : stateRel f source target) :
    ∃ (nextMap : HolFiniteMapExact Nat Nat) (value' : Value) (targetNext : BviState C F),
      BviSem.doApp (.thunkOp op) relatedValues target = .val (value', targetNext) ∧
      valueRel nextMap value value' ∧ stateRel nextMap sourceNext targetNext ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs targetNext.refs ∅ ∧
      holesStillNotFinalised f target.refs targetNext.refs := by
  cases op with
  | allocThunk mode => exact doApp_op_rel_allocThunk f mode values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | updateThunk mode => exact doApp_op_rel_updateThunk f mode values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated
  | forceThunk => exact doApp_op_rel_forceThunk f values relatedValues source sourceNext target value run noMutcons valuesRelated statesRelated

end Flapjack.Compiler.Backend.BviTmc
