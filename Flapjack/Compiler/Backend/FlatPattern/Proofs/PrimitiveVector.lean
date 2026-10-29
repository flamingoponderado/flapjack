import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveAccess
import Flapjack.Compiler.Backend.FlatPattern.Proofs.DynamicEvaluation
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveGlobals

/-! List and vector primitive simulations for the proof-side flat pattern
relations, which remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The flat list decoder inverts the canonical list constructor. -/
theorem valueToList_listToValue (values : List FlatSem.Value) :
    FlatSem.valueToList (FlatSem.listToValue values) = some values := by
  induction values with
  | nil => simp [FlatSem.valueToList, FlatSem.listToValue, BackendCommon.nilTag, FlatSem.listId]
  | cons head tail ih => simp [FlatSem.valueToList, FlatSem.listToValue, BackendCommon.consTag, FlatSem.listId, ih]

/-- Decoding related lists produces pointwise related elements. -/
theorem valueToList_related (value value' : FlatSem.Value) (values : List FlatSem.Value)
    (related : ValueRel value value') (decoded : FlatSem.valueToList value = some values) :
    ∃ values', FlatSem.valueToList value' = some values' ∧ List.Forall₂ ValueRel values values' := by
  have encoded := valueToList_inverse value values decoded
  rw [← encoded] at related
  obtain ⟨values', rfl, valuesRel⟩ := listToValue_related values value' related
  exact ⟨values', valueToList_listToValue values', valuesRel⟩

/-- Constructing flat lists from related elements produces related values. -/
theorem listToValue_pair_related {values values' : List FlatSem.Value} (related : List.Forall₂ ValueRel values values') :
    ValueRel (FlatSem.listToValue values) (FlatSem.listToValue values') := by
  induction related with
  | nil => exact (valueRel_conv _ [] _).2 ⟨[], rfl, .nil⟩
  | cons head _ ih => exact (valueRel_conv _ _ _).2 ⟨_, rfl, .cons head (.cons ih .nil)⟩

/-- List-to-vector conversion preserves arbitrary successful primitive results. -/
theorem doApp_vectorFromList_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .vfromList) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .vfromList) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      cases decoded : FlatSem.valueToList value with
      | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded] at run
      | some items =>
        obtain ⟨items', decoded', itemsRel⟩ := valueToList_related value value' items valueRel decoded
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, .val (.vectorv items'), ?_, states, .value ?_⟩
        · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded']
        · exact (valueRel_vector items _).2 ⟨items', rfl, itemsRel⟩

/-- Vector length preserves arbitrary successful primitive results. -/
theorem doApp_vectorLength_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .vlength) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .vlength) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      cases value with
      | vectorv items =>
        obtain ⟨items', rfl, itemsRel⟩ := (valueRel_vector items value').1 valueRel
        have lengths := forall₂_length itemsRel
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .val (.litv (.intLit items.length)),
          by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, ← lengths],
          states, .value ((valueRel_lit _ _).2 rfl)⟩
      | litv _ | conv _ _ | loc _ _ | closure _ _ _ | recclosure _ _ _ =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run

/-- List append preserves arbitrary successful primitive results. -/
theorem doApp_listAppend_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .listAppend) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .listAppend) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons first first' tail tail' firstRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | @cons second second' tail tail' secondRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        cases left : FlatSem.valueToList first with
        | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, left] at run
        | some xs =>
          cases right : FlatSem.valueToList second with
          | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, left, right] at run
          | some ys =>
            obtain ⟨xs', left', xsRel⟩ := valueToList_related first first' xs firstRel left
            obtain ⟨ys', right', ysRel⟩ := valueToList_related second second' ys secondRel right
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, left, right] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, .val (FlatSem.listToValue (xs' ++ ys')), ?_, states, .value ?_⟩
            · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, left', right']
            · exact listToValue_pair_related (forall₂_append_lists xsRel ysRel)

/-- Checked and unsafe vector reads preserve related values and errors. -/
theorem doApp_vectorRead_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (unsafeOp : Bool) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (if unsafeOp then .vsubUnsafe else .vsub)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (if unsafeOp then .vsubUnsafe else .vsub)) values' =
      some (targetFinal, result') ∧ StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons vector vector' tail tail' vectorRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | cons _ _ => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        cases vector with
        | vectorv items =>
          obtain ⟨items', rfl, itemsRel⟩ := (valueRel_vector items vector').1 vectorRel
          cases idx with
          | litv literal =>
            have eq := (valueRel_lit literal idx').1 idxRel
            subst idx'
            cases literal with
            | intLit index =>
              have unequal : (Op.vsub == Op.vsubUnsafe) = false := by decide
              have read : FlatSem.readIndexed source unsafeOp items index id = some (sourceFinal, result) := by
                cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, unequal] using run
              have stateEq := readIndexed_state source sourceFinal unsafeOp items index id result read
              subst sourceFinal
              obtain ⟨result', targetRead, resultRel⟩ := readIndexed_related source target unsafeOp items items' index itemsRel result read
              refine ⟨target, result', ?_, states, resultRel⟩
              cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, unequal] using targetRead
            | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
              cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
          | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
        | litv _ | conv _ _ | loc _ _ | closure _ _ _ | recclosure _ _ _ =>
          cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
end Flapjack.Compiler.Backend.FlatPattern
