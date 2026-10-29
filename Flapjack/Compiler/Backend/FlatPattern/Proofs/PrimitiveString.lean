import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveVector

/-! String primitive simulations for the proof-side flat pattern relations,
which remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A list of literal values is related to itself. -/
theorem literalValues_related (literals : List Lit) :
    List.Forall₂ ValueRel (literals.map FlatSem.Value.litv) (literals.map FlatSem.Value.litv) := by
  induction literals with
  | nil => exact .nil
  | cons lit _ ih => exact .cons ((valueRel_lit lit _).2 rfl) ih

/-- String length preserves arbitrary successful primitive results. -/
theorem doApp_stringLength_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .strlen) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .strlen) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      cases value with
      | litv lit =>
        have eq := (valueRel_lit lit value').1 valueRel
        subst value'
        cases lit with
        | strLit string =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (.litv (.intLit string.explode.length)),
            by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData],
            states, .value ((valueRel_lit _ _).2 rfl)⟩
        | intLit _ | word8 _ | word64 _ | char _ | float64 _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run

/-- Exploding a string produces related character lists. -/
theorem doApp_stringExplode_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .explode) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .explode) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | nil =>
      cases value with
      | litv lit =>
        have eq := (valueRel_lit lit value').1 valueRel
        subst value'
        cases lit with
        | strLit string =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨target, .val (FlatSem.listToValue (string.explode.map (.litv ∘ Lit.char))), ?_, states, .value ?_⟩
          · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData]
          · apply listToValue_pair_related
            simpa [List.map_map, Function.comp_def] using literalValues_related (string.explode.map Lit.char)
        | intLit _ | word8 _ | word64 _ | char _ | float64 _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run

/-- An indexed read from the same literal sequence preserves its result,
including checked bounds exceptions. -/
theorem readIndexed_literals_related {C F A : Type} (source target : FlatSem.State C F) (items : List A)
    (index : Int) (literal : A → Lit) (result : Result FlatSem.Value FlatSem.Value)
    (run : FlatSem.readIndexed source false items index (.litv ∘ literal) = some (source, result)) :
    FlatSem.readIndexed target false items index (.litv ∘ literal) = some (target, result) ∧ PrimitiveResultRel result result := by
  by_cases negative : index < 0
  · simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at run
    subst result
    exact ⟨by simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative], .error (.raise subscriptExn_related)⟩
  · cases found : items[index.toNat]? with
    | none =>
      simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, found] at run
      subst result
      exact ⟨by simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, found], .error (.raise subscriptExn_related)⟩
    | some item =>
      simp [FlatSem.readIndexed, negative, found] at run
      subst result
      exact ⟨by simp [FlatSem.readIndexed, negative, found], .value ((valueRel_lit _ _).2 rfl)⟩

/-- String indexing preserves returned bytes and checked bounds exceptions. -/
theorem doApp_stringSub_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .strsub) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .strsub) values' = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
      | nil =>
        cases value with
        | litv literal =>
          have eq := (valueRel_lit literal value').1 valueRel
          subst value'
          cases literal with
          | strLit string =>
            cases idx with
            | litv literal =>
              have eq := (valueRel_lit literal idx').1 idxRel
              subst idx'
              cases literal with
              | intLit index =>
                have read : FlatSem.readIndexed source false string.explode index (.litv ∘ Lit.char) = some (sourceFinal, result) := by
                  simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] using run
                have eq := readIndexed_state source sourceFinal false string.explode index (.litv ∘ Lit.char) result read
                subst sourceFinal
                obtain ⟨targetRead, resultRel⟩ := readIndexed_literals_related source target string.explode index Lit.char result read
                exact ⟨target, result, by simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] using targetRead,
                  states, resultRel⟩
              | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
                simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
            | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
          | intLit _ | word8 _ | word64 _ | char _ | float64 _ =>
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run
        | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData] at run

/-- Concatenating related lists of strings returns the same byte string. -/
theorem valuesToString_related {values values' : List FlatSem.Value} (related : List.Forall₂ ValueRel values values')
    (result : Flapjack.Basis.Pure.MlString.MlString) (run : FlatSem.valuesToString values = some result) :
    FlatSem.valuesToString values' = some result := by
  induction related generalizing result with
  | nil => simpa [FlatSem.valuesToString] using run
  | @cons value value' tail tail' valueRel tailRel ih =>
    cases value with
    | litv literal =>
      have eq := (valueRel_lit literal value').1 valueRel
      subst value'
      cases literal with
      | strLit string =>
        cases tailRun : FlatSem.valuesToString tail with
        | none => simp [FlatSem.valuesToString, tailRun] at run
        | some rest =>
          have targetTail := ih rest tailRun
          simpa [FlatSem.valuesToString, tailRun, targetTail] using run
      | intLit _ | word8 _ | word64 _ | char _ | float64 _ => simp [FlatSem.valuesToString] at run
    | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ => simp [FlatSem.valuesToString] at run

/-- String concatenation preserves arbitrary successful primitive results. -/
theorem doApp_stringConcat_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (values values' : List FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (run : FlatSem.doApp source (.src .strcat) values = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .strcat) values' = some (targetFinal, result') ∧
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
        cases concatenated : FlatSem.valuesToString items with
        | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded, concatenated] at run
        | some string =>
          obtain ⟨items', decoded', itemsRel⟩ := valueToList_related value value' items valueRel decoded
          have concatenated' := valuesToString_related itemsRel string concatenated
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded, concatenated] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (.litv (.strLit string)),
            by simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.doAppData, decoded', concatenated'],
            states, .value ((valueRel_lit _ _).2 rfl)⟩

end Flapjack.Compiler.Backend.FlatPattern
