import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveByteArray

/-! Array-access primitives for the proof-side flat pattern simulation. The
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result storeLookup)

/-- An indexed read never changes the state when it returns a result. -/
theorem readIndexed_state {C F A : Type} (state next : FlatSem.State C F) (unsafeOp : Bool)
    (items : List A) (index : Int) (convert : A → FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (run : FlatSem.readIndexed state unsafeOp items index convert = some (next, result)) : next = state := by
  by_cases negative : index < 0
  · cases unsafeOp <;> simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at run
    exact run.1.symm
  · cases found : items[index.toNat]? with
    | none =>
      cases unsafeOp <;> simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, found] at run
      exact run.1.symm
    | some _ =>
      simp [FlatSem.readIndexed, negative, found] at run
      exact run.1.symm

/-- Value-array length preserves arbitrary successful primitive results. -/
theorem doApp_arrayLength_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .alength) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .alength) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons value value' tail tail' values rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | nil =>
      cases value with
      | loc flag address =>
        have eq := (valueRel_loc flag address value').1 values
        subst value'
        cases found : storeLookup address source.refs with
        | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
        | some entry =>
          cases entry with
          | varray items =>
            obtain ⟨value, sourceRun, targetRun, valueRel⟩ := doApp_arrayLength_related cfg source target flag address items states found
            have equal := sourceRun.symm.trans run
            cases equal
            exact ⟨target, .val value, targetRun, states, .value valueRel⟩
          | refv _ | w8array _ | thunk _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
      | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

/-- Byte-array length preserves arbitrary successful primitive results. -/
theorem doApp_byteArrayLength_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .aw8length) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .aw8length) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons value value' tail tail' values rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | nil =>
      cases value with
      | loc flag address =>
        have eq := (valueRel_loc flag address value').1 values
        subst value'
        cases found : storeLookup address source.refs with
        | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
        | some entry =>
          cases entry with
          | w8array bytes =>
            obtain ⟨value, sourceRun, targetRun, valueRel⟩ := doApp_byteArrayLength_related cfg source target flag address bytes states found
            have equal := sourceRun.symm.trans run
            cases equal
            exact ⟨target, .val value, targetRun, states, .value valueRel⟩
          | refv _ | varray _ | thunk _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
      | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

/-- Value-array updates preserve arbitrary successful primitive results. -/
theorem doApp_arrayUpdate_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (unsafeOp : Bool) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (if unsafeOp then .aupdateUnsafe else .aupdate)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (if unsafeOp then .aupdateUnsafe else .aupdate)) values' =
      some (targetFinal, result') ∧ StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | @cons value value' tail tail' valueRel rest =>
        cases rest with
        | cons _ _ => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
        | nil =>
          cases loc with
          | loc flag address =>
            have eq := (valueRel_loc flag address loc').1 locRel
            subst loc'
            cases idx with
            | litv literal =>
              have eq := (valueRel_lit literal idx').1 idxRel
              subst idx'
              cases literal with
              | intLit index =>
                cases found : storeLookup address source.refs with
                | none => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
                | some entry =>
                  cases entry with
                  | varray items => exact doApp_arrayUpdate_related cfg source target sourceFinal unsafeOp flag address index items value value' result states valueRel found run
                  | refv _ | w8array _ | thunk _ _ =>
                    cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
              | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
                cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
            | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
          | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

/-- Value-array reads preserve arbitrary successful primitive results. -/
theorem doApp_arrayRead_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (unsafeOp : Bool) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (if unsafeOp then .asubUnsafe else .asub)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (if unsafeOp then .asubUnsafe else .asub)) values' =
      some (targetFinal, result') ∧ StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | cons _ _ => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | nil =>
        cases loc with
        | loc flag address =>
          have eq := (valueRel_loc flag address loc').1 locRel
          subst loc'
          cases idx with
          | litv literal =>
            have eq := (valueRel_lit literal idx').1 idxRel
            subst idx'
            cases literal with
            | intLit index =>
              cases found : storeLookup address source.refs with
              | none => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
              | some entry =>
                cases entry with
                | varray items =>
                  have unequal : (Op.asub == Op.asubUnsafe) = false := by decide
                  have read : FlatSem.readIndexed source unsafeOp items index id = some (sourceFinal, result) := by
                    cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found, unequal] using run
                  have stateEq := readIndexed_state source sourceFinal unsafeOp items index id result read
                  subst sourceFinal
                  obtain ⟨result', targetRun, resultRel⟩ := doApp_arrayRead_related cfg source target unsafeOp flag address index items result states found run
                  exact ⟨target, result', targetRun, states, resultRel⟩
                | refv _ | w8array _ | thunk _ _ =>
                  cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
            | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
              cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
          | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
        | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run


/-- Byte-array reads preserve arbitrary successful primitive results. -/
theorem doApp_byteArrayRead_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (unsafeOp : Bool) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (if unsafeOp then .aw8subUnsafe else .aw8sub)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (if unsafeOp then .aw8subUnsafe else .aw8sub)) values' =
      some (targetFinal, result') ∧ StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | cons _ _ => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | nil =>
        cases loc with
        | loc flag address =>
          have eq := (valueRel_loc flag address loc').1 locRel
          subst loc'
          cases idx with
          | litv literal =>
            have eq := (valueRel_lit literal idx').1 idxRel
            subst idx'
            cases literal with
            | intLit index =>
              cases found : storeLookup address source.refs with
              | none => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
              | some entry =>
                cases entry with
                | w8array items =>
                  have unequal : (Op.aw8sub == Op.aw8subUnsafe) = false := by decide
                  have read : FlatSem.readIndexed source unsafeOp items index (.litv ∘ Lit.word8) = some (sourceFinal, result) := by
                    cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found, unequal] using run
                  have stateEq := readIndexed_state source sourceFinal unsafeOp items index (.litv ∘ Lit.word8) result read
                  subst sourceFinal
                  obtain ⟨targetRun, resultRel⟩ := doApp_byteArrayRead_related cfg source target unsafeOp flag address index items result states found run
                  exact ⟨target, result, targetRun, states, resultRel⟩
                | refv _ | varray _ | thunk _ _ =>
                  cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
            | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
              cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
          | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
        | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

/-- Byte-array updates preserve arbitrary successful primitive results. -/
theorem doApp_byteArrayUpdate_complete {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (unsafeOp : Bool) (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src (if unsafeOp then .aw8updateUnsafe else .aw8update)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (if unsafeOp then .aw8updateUnsafe else .aw8update)) values' =
      some (targetFinal, result') ∧ StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | nil => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | @cons value value' tail tail' valueRel rest =>
        cases rest with
        | cons _ _ => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
        | nil =>
          cases loc with
          | loc flag address =>
            have eq := (valueRel_loc flag address loc').1 locRel
            subst loc'
            cases idx with
            | litv literal =>
              have eq := (valueRel_lit literal idx').1 idxRel
              subst idx'
              cases literal with
              | intLit index =>
                cases value with
                | litv literal =>
                  have eq := (valueRel_lit literal value').1 valueRel
                  subst value'
                  cases literal with
                  | word8 byte =>
                    cases found : storeLookup address source.refs with
                    | none => cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
                    | some entry =>
                      cases entry with
                      | w8array bytes =>
                        obtain ⟨targetFinal, targetRun, finalStates, results⟩ :=
                          doApp_byteArrayUpdate_related cfg source target sourceFinal unsafeOp flag address index bytes byte result states found run
                        exact ⟨targetFinal, result, targetRun, finalStates, results⟩
                      | refv _ | varray _ | thunk _ _ =>
                        cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found] at run
                  | intLit _ | word64 _ | char _ | strLit _ | float64 _ =>
                    cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
                | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
                  cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
              | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
                cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
            | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
          | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

end Flapjack.Compiler.Backend.FlatPattern
