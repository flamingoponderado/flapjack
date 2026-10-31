import Flapjack.Compiler.Backend.BviTmc.Proofs.StateRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.HoleRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.WordRelation
import Flapjack.Compiler.Backend.BviTmc.Proofs.Allocation
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

end Flapjack.Compiler.Backend.BviTmc
