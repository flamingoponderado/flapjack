import Flapjack.Compiler.Backend.BviTmc.Proofs.OperationRelation

/-! FFI error simulation for the TMC operation case. -/
namespace Flapjack.Compiler.Backend.BviTmc.OperationError
open BviTmc BviSem BvlSem

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- A final FFI error is identical for related argument values and states. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "do_app_op_err_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f])]
theorem doApp_op_err_rel {C F : Type} (name : Basis.Pure.MlString.MlString)
    (values relatedValues : List Value) (source : BviState (Nat × C) F) (target : BviState C F)
    (f : HolFiniteMapExact Nat Nat) (outcome : HolFinalEvent)
    (run : BviSem.doApp (.ffi name) values source = .err (.abort (.ffiError outcome)))
    (statesRelated : stateRel f source target) (valuesRelated : List.Forall₂ (valueRel f) values relatedValues) :
    BviSem.doApp (.ffi name) relatedValues target = .err (.abort (.ffiError outcome)) := by
  rw [BviTailrec.doApp_ffi_effect] at run ⊢
  cases values with
  | nil => simp [BviTailrec.ffiEffect] at run
  | cons first rest =>
    cases rest with
    | nil => simp [BviTailrec.ffiEffect] at run
    | cons second rest =>
      cases rest with
      | cons extra rest => simp [BviTailrec.ffiEffect] at run
      | nil =>
        cases first <;> cases second <;> simp [BviTailrec.ffiEffect] at run
        rename_i configFlag configPtr dataFlag dataPtr
        cases valuesRelated with
        | cons configRel tailRel =>
          cases configRel with
          | refPtr _ targetConfigPtr _ configMapped =>
            cases tailRel with
            | cons dataRel tailRel =>
              cases dataRel with
              | refPtr _ targetDataPtr _ dataMapped =>
                cases tailRel
                obtain ⟨_, _, sourceConfig, targetConfig, configCells⟩ :=
                  stateRefRel_lookup f configPtr targetConfigPtr source.refs target.refs configMapped statesRelated.1
                obtain ⟨_, _, sourceData, targetData, dataCells⟩ :=
                  stateRefRel_lookup f dataPtr targetDataPtr source.refs target.refs dataMapped statesRelated.1
                cases configCells with
                | valueArray xs ys rel => simp [sourceConfig] at run
                | thunk mode x y rel => simp [sourceConfig] at run
                | byteArray configMutable config =>
                  cases configMutable with
                  | false => simp [sourceConfig] at run
                  | true =>
                    cases dataCells with
                    | valueArray xs ys rel => simp [sourceConfig, sourceData] at run
                    | thunk mode x y rel => simp [sourceConfig, sourceData] at run
                    | byteArray dataMutable bytes =>
                      cases dataMutable with
                      | true => simp [sourceConfig, sourceData] at run
                      | false =>
                        cases call : callFFIHOL source.ffi (.extCall name) config bytes with
                        | final event =>
                          simp [sourceConfig, sourceData, call] at run
                          subst event
                          simp [BviTailrec.ffiEffect, targetConfig, targetData, statesRelated.2.2.2.1, call]
                        | ret nextFfi updated => simp [sourceConfig, sourceData, call] at run

end Flapjack.Compiler.Backend.BviTmc.OperationError
