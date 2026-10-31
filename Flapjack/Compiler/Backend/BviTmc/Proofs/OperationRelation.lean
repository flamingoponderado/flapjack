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

end Flapjack.Compiler.Backend.BviTmc
