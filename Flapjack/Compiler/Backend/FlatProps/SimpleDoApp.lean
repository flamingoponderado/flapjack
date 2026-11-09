module

public import Flapjack.Misc.RichList
public import Flapjack.Compiler.Backend.FlatProps.SimpleType
public import Flapjack.Compiler.Backend.FlatProps.SimpleStore
public import Flapjack.Compiler.Backend.FlatProps.SimpleConversions
public import Flapjack.Compiler.Backend.FlatProps.SimpleEquality
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply
public import Flapjack.SemanticPrimitivesProps.ResultRelation

@[expose] public section
/-! General primitive simulation for simple flat value and state relations.
Private case lemmas follow the operation split in the original HOL proof. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)
open Flapjack.SemanticPrimitivesProps
private theorem basicRelLit (vr : Value → Value → Prop) (simple : simpleValueRel vr) (lit : Lit) :
    vr (.litv lit) (.litv lit) := by
  apply (simple.2 _ _ (by simp [isClosure])).mpr
  simp [simpleBasicValRel, valueContainerXs]
private theorem basicRelConvNil (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)) : vr (.conv stamp []) (.conv stamp []) := by
  apply (simple.2 _ _ (by simp [isClosure])).mpr
  simp [simpleBasicValRel, valueContainerXs]
private theorem basicRelVectorNil (vr : Value → Value → Prop) (simple : simpleValueRel vr) :
    vr (.vectorv []) (.vectorv []) := by
  apply (simple.2 _ _ (by simp [isClosure])).mpr
  simp [simpleBasicValRel, valueContainerXs]
private theorem basicRelBool (vr : Value → Value → Prop) (simple : simpleValueRel vr) (b : Bool) :
    vr (boolValue b) (boolValue b) := by
  cases b <;> exact basicRelConvNil vr simple _
private theorem simpleFlatToValue (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (value value' : Value) (related : vr value value') : flatToValue value = flatToValue value' := by
  cases value with
  | litv lit =>
    have h := ((simple.2 _ _ (by simp [isClosure])).mp related).1
    change value' = .litv lit at h
    subst value'
    rfl
  | loc flag index =>
    have h := ((simple.2 _ _ (by simp [isClosure])).mp related).1
    change value' = .loc flag index at h
    subst value'
    rfl
  | conv stamp fields =>
    have h := (simple.2 _ _ (by simp [isClosure])).mp related
    obtain ⟨fields', rfl⟩ := h.1
    cases fields with
    | nil =>
      cases h.2
      rfl
    | cons first rest =>
      cases h.2
      cases stamp with
      | none => rfl
      | some pair =>
        obtain ⟨tag, typeId⟩ := pair
        cases typeId <;> rfl
  | vectorv fields =>
    have h := (simple.2 _ _ (by simp [isClosure])).mp related
    obtain ⟨fields', rfl⟩ := h.1
    rfl
  | closure env name body =>
    have h := (simple.1 _ _ related).mp (by simp [isClosure])
    rcases h with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  | recclosure env funs name =>
    have h := (simple.1 _ _ related).mp (by simp [isClosure])
    rcases h with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl

private theorem simpleValueToFlat (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (value : SemanticPrimitivesHOL.Value) : vr (valueToFlat value) (valueToFlat value) := by
  cases value with
  | litv lit => exact basicRelLit vr simple lit
  | conv stamp fields =>
    cases stamp with
    | none => exact basicRelVectorNil vr simple
    | some stamp =>
      cases stamp with
      | typeStamp name number =>
        cases number with
        | zero =>
          cases fields with
          | nil =>
            simp only [valueToFlat]
            split
            · exact basicRelBool vr simple true
            · split
              · exact basicRelBool vr simple false
              · exact basicRelVectorNil vr simple
          | cons _ _ => exact basicRelVectorNil vr simple
        | succ _ => exact basicRelVectorNil vr simple
      | exnStamp _ => exact basicRelVectorNil vr simple
  | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ | env _ =>
    exact basicRelVectorNil vr simple

private theorem simpleFlatToValueMap (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    {values values' : List Value} (related : List.Forall₂ vr values values') :
    values.map flatToValue = values'.map flatToValue := by
  induction related with
  | nil => rfl
  | cons head _ ih => simp [simpleFlatToValue vr simple _ _ head, ih]

private theorem simpleNumericProjection {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (op : Op) (values values' : List Value) (errorValue : Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values') (errorRel : vr errorValue errorValue)
    (run : applyNumericProjection source op values errorValue = some (sourceFinal, result)) :
    ∃ targetFinal result', applyNumericProjection target op values' errorValue = some (targetFinal, result') ∧
      sr sourceFinal targetFinal ∧ resultRel vr vr result result' := by
  have arguments := simpleFlatToValueMap vr simple related
  have ffi := simpleState.2.2.2.2.1 source target states
  cases called : SemanticPrimitivesHOL.doApp ([], source.ffi) op (values.map flatToValue) with
  | none => simp [applyNumericProjection, called] at run
  | some output =>
    obtain ⟨ignored, output⟩ := output
    cases output with
    | val value =>
      simp [applyNumericProjection, called] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨target, .val (valueToFlat value), ?_, states, simpleValueToFlat vr simple value⟩
      simp [applyNumericProjection, ← ffi, ← arguments, called]
    | err error =>
      cases error with
      | raise raised =>
        simp [applyNumericProjection, called] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, .err (.raise errorValue), ?_, states, errorRel⟩
        simp [applyNumericProjection, ← ffi, ← arguments, called]
      | abort abort =>
        simp [applyNumericProjection, called] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, .err (.abort abort), ?_, states, rfl⟩
        simp [applyNumericProjection, ← ffi, ← arguments, called]

private theorem simpleArith {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (action : Arith) (typ : PrimType) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (.arith action typ)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (.arith action typ)) values' = some (targetFinal, result') := by
  have run' : applyNumericProjection source (.arith action typ) values divExnV = some (sourceFinal, result) := by
    simpa [doApp, doAppNumeric] using run
  obtain ⟨targetFinal, result', targetRun, finalStates, resultRel⟩ :=
    simpleNumericProjection vr sr simple simpleState source target sourceFinal (.arith action typ) values values' divExnV result
      states related (basicRelConvNil vr simple _) run'
  exact ⟨targetFinal, result', resultRel, finalStates, by simpa [doApp, doAppNumeric] using targetRun⟩

private theorem simpleFromTo {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (sourceTyp targetTyp : PrimType) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (.fromTo sourceTyp targetTyp)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (.fromTo sourceTyp targetTyp)) values' = some (targetFinal, result') := by
  have run' : applyNumericProjection source (.fromTo sourceTyp targetTyp) values chrExnV = some (sourceFinal, result) := by
    simpa [doApp, doAppNumeric] using run
  obtain ⟨targetFinal, result', targetRun, finalStates, resultRel⟩ :=
    simpleNumericProjection vr sr simple simpleState source target sourceFinal (.fromTo sourceTyp targetTyp) values values' chrExnV result
      states related (basicRelConvNil vr simple _) run'
  exact ⟨targetFinal, result', resultRel, finalStates, by simpa [doApp, doAppNumeric] using targetRun⟩

private theorem simpleShift {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (width : WordSize) (shift : Shift) (amount : Nat) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (.shift width shift amount)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (.shift width shift amount)) values' = some (targetFinal, result') := by
  have run' : applyNumericProjection source (.shift width shift amount) values divExnV = some (sourceFinal, result) := by
    simpa [doApp_shift_projection] using run
  obtain ⟨targetFinal, result', targetRun, finalStates, resultRel⟩ :=
    simpleNumericProjection vr sr simple simpleState source target sourceFinal (.shift width shift amount) values values' divExnV result
      states related (basicRelConvNil vr simple _) run'
  exact ⟨targetFinal, result', resultRel, finalStates, by simpa [doApp_shift_projection] using targetRun⟩

private theorem simpleEquality {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .equality) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .equality) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric] at run
  | @cons first first' tail tail' firstRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric] at run
    | @cons second second' tail tail' secondRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric] at run
      | nil =>
        cases compared : doEq first second with
        | typeError => simp [doApp, doAppNumeric, compared] at run
        | val boolean =>
          have compared' := simpleDoEq vr first second first' second' boolean ⟨simple, compared, firstRel, secondRel⟩
          simp [doApp, doAppNumeric, compared] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (boolValue boolean), basicRelBool vr simple boolean, states,
            by simp [doApp, doAppNumeric, compared']⟩

private theorem simpleCheckTypeEq (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (typ : PrimType) (value value' : Value) (related : vr value value')
    (valid : checkType typ value = true) : value' = value := by
  cases value with
  | litv lit =>
    have h := ((simple.2 _ _ (by simp [isClosure])).mp related).1
    exact h
  | conv stamp fields =>
    have h := (simple.2 _ _ (by simp [isClosure])).mp related
    obtain ⟨fields', rfl⟩ := h.1
    cases fields with
    | nil => cases h.2; rfl
    | cons _ _ => cases typ <;> simp [checkType] at valid
  | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
    cases typ <;> simp [checkType] at valid

private theorem simpleDoTestTypes (test : Test) (typ : PrimType) (first second : Value) (result : Bool)
    (run : doTest test typ first second = .val result) :
    checkType typ first = true ∧ checkType typ second = true := by
  cases test with
  | equal =>
    by_cases check : checkType typ first && checkType typ second
    · simpa using check
    · simp [doTest, check] at run
  | compare ordering =>
    cases typ <;> cases first <;> cases second <;> simp [doTest, checkType] at run ⊢
    all_goals repeat' (split at run) <;> simp_all
  | altCompare ordering =>
    cases typ <;> cases first <;> cases second <;> simp [doTest, checkType] at run ⊢
    all_goals repeat' (split at run) <;> simp_all

private theorem simpleTest {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (test : Test) (typ : PrimType) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (.test test typ)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (.test test typ)) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric] at run
  | @cons first first' tail tail' firstRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric] at run
    | @cons second second' tail tail' secondRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric] at run
      | nil =>
        cases tested : doTest test typ first second with
        | typeError => simp [doApp, doAppNumeric, tested] at run
        | val boolean =>
          have ⟨firstType, secondType⟩ := simpleDoTestTypes test typ first second boolean tested
          have firstEq := simpleCheckTypeEq vr simple typ first first' firstRel firstType
          have secondEq := simpleCheckTypeEq vr simple typ second second' secondRel secondType
          have tested' : doTest test typ first' second' = .val boolean := by simpa [firstEq, secondEq] using tested
          simp [doApp, doAppNumeric, tested] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (boolValue boolean), basicRelBool vr simple boolean, states,
            by simp [doApp, doAppNumeric, tested']⟩

private theorem simpleId {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source .id values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target .id values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppFlat] at run
  | @cons value value' tail tail' values rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppFlat] at run
    | nil =>
      simp [doApp, doAppFlat] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, .val value', values, states, by simp [doApp, doAppFlat]⟩

private theorem simpleGlobalAlloc {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (count : Nat) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.globalVarAlloc count) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.globalVarAlloc count) values' = some (targetFinal, result') := by
  cases related with
  | cons _ _ => simp [doApp, doAppFlat] at run
  | nil =>
    simp [doApp, doAppFlat] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨{ target with globals := target.globals ++ List.replicate count none }, .val unitValue,
      basicRelConvNil vr simple none, ?_, by simp [doApp, doAppFlat]⟩
    apply simpleState.2.2.2.1 source target _ _
    refine ⟨states, List.rel_append (simpleState.2.2.1 source target states) ?_⟩
    exact (forall₂_replicate_iff (optionRel vr) count none none).mpr (fun _ => trivial)

private theorem simpleGlobalInit {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (index : Nat) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.globalVarInit index) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.globalVarInit index) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppFlat] at run
  | @cons value value' tail tail' values rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppFlat] at run
    | nil =>
      cases found : source.globals[index]? with
      | none => simp [doApp, doAppFlat, found] at run
      | some slot =>
        cases slot with
        | some _ => simp [doApp, doAppFlat, found] at run
        | none =>
          obtain ⟨slot', found', slotRel⟩ := forall₂_lookup (simpleState.2.2.1 source target states) index none found
          cases slot' with
          | some _ => simp [optionRel] at slotRel
          | none =>
            simp [doApp, doAppFlat, found] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ target with globals := target.globals.set index (some value') }, .val unitValue,
              basicRelConvNil vr simple none, ?_, by simp [doApp, doAppFlat, found']⟩
            apply simpleState.2.2.2.1 source target _ _
            exact ⟨states, Flapjack.forall₂_set _ _ _ _ _ index
              ⟨(show optionRel vr (some value) (some value') from values), simpleState.2.2.1 source target states⟩⟩

private theorem simpleGlobalLookup {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (index : Nat) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.globalVarLookup index) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.globalVarLookup index) values' = some (targetFinal, result') := by
  cases related with
  | cons _ _ => simp [doApp, doAppFlat] at run
  | nil =>
    cases found : source.globals[index]? with
    | none => simp [doApp, doAppFlat, found] at run
    | some slot =>
      cases slot with
      | none => simp [doApp, doAppFlat, found] at run
      | some value =>
        obtain ⟨slot', found', slotRel⟩ := forall₂_lookup (simpleState.2.2.1 source target states) index (some value) found
        cases slot' with
        | none => simp [optionRel] at slotRel
        | some value' =>
          simp [doApp, doAppFlat, found] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val value', slotRel, states, by simp [doApp, doAppFlat, found']⟩

private theorem simpleRelConv (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (stamp : Option (FlatLang.CtorId × FlatLang.TypeId)) (fields : List Value) (value' : Value)
    (related : vr (.conv stamp fields) value') :
    ∃ fields', value' = .conv stamp fields' ∧ List.Forall₂ vr fields fields' := by
  have h := (simple.2 _ _ (by simp [isClosure])).mp related
  obtain ⟨fields', rfl⟩ := h.1
  exact ⟨fields', rfl, h.2⟩

private theorem simpleRelLoc (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (flag : Bool) (index : Nat) (value' : Value) (related : vr (.loc flag index) value') :
    value' = .loc flag index := by
  exact ((simple.2 _ _ (by simp [isClosure])).mp related).1

private theorem simpleLenEq {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (length : Nat) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.lenEq length) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.lenEq length) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppFlat] at run
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppFlat] at run
    | nil =>
      cases value with
      | conv tag fields =>
        obtain ⟨fields', rfl, fieldsRel⟩ := simpleRelConv vr simple tag fields value' head
        have lengths := List.Forall₂.length_eq fieldsRel
        simp [doApp, doAppFlat] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .val (boolValue (fields.length == length)), basicRelBool vr simple _, states,
          by simp [doApp, doAppFlat, ← lengths]⟩
      | litv _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [doApp, doAppFlat] at run

private theorem simpleTagLenEq {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (tag length : Nat) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.tagLenEq tag length) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.tagLenEq tag length) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppFlat] at run
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppFlat] at run
    | nil =>
      cases value with
      | conv stamp fields =>
        cases stamp with
        | none => simp [doApp, doAppFlat] at run
        | some pair =>
          obtain ⟨actual, typeId⟩ := pair
          obtain ⟨fields', rfl, fieldsRel⟩ := simpleRelConv vr simple (some (actual, typeId)) fields value' head
          have lengths := List.Forall₂.length_eq fieldsRel
          simp [doApp, doAppFlat] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (boolValue (actual == tag && fields.length == length)), basicRelBool vr simple _, states,
            by simp [doApp, doAppFlat, ← lengths]⟩
      | litv _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [doApp, doAppFlat] at run

private theorem simpleEl {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (index : Nat) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.el index) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.el index) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppFlat] at run
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppFlat] at run
    | nil =>
      cases value with
      | conv tag fields =>
        obtain ⟨fields', rfl, fieldsRel⟩ := simpleRelConv vr simple tag fields value' head
        cases found : fields[index]? with
        | none => simp [doApp, doAppFlat, found] at run
        | some field =>
          simp [doApp, doAppFlat, found] at run
          rcases run with ⟨rfl, rfl⟩
          obtain ⟨field', found', fieldRel⟩ := forall₂_lookup fieldsRel index field found
          exact ⟨target, .val field', fieldRel, states, by simp [doApp, doAppFlat, found']⟩
      | loc flag address =>
        have eq := simpleRelLoc vr simple flag address value' head
        subst value'
        cases index with
        | succ _ => simp [doApp, doAppFlat] at run
        | zero =>
          cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
          | none => simp [doApp, doAppFlat, found] at run
          | some entry =>
            cases entry with
            | refv field =>
              simp [doApp, doAppFlat, found] at run
              rcases run with ⟨rfl, rfl⟩
              obtain ⟨entry', found', entryRel⟩ := simpleStateRel_storeLookup vr sr address source (.refv field) target
                ⟨simpleState, found, states⟩
              cases entry' with
              | refv field' =>
                exact ⟨target, .val field', entryRel, states, by simp [doApp, doAppFlat, found']⟩
              | w8array _ | varray _ | thunk _ _ => simp [storeValueRel] at entryRel
            | w8array _ | varray _ | thunk _ _ => simp [doApp, doAppFlat, found] at run
      | litv _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [doApp, doAppFlat] at run

private theorem basicRelLoc (vr : Value → Value → Prop) (simple : simpleValueRel vr) (flag : Bool) (index : Nat) :
    vr (.loc flag index) (.loc flag index) := by
  apply (simple.2 _ _ (by simp [isClosure])).mpr
  simp [simpleBasicValRel, valueContainerXs]

private theorem simpleOpref {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .opref) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .opref) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory] at run
    | nil =>
      simp [doApp, doAppNumeric, doAppMemory, SemanticPrimitivesHOL.storeAlloc] at run
      rcases run with ⟨rfl, rfl⟩
      have refs := simpleState.1 source target states
      have lengths : target.refs.length = source.refs.length := (List.Forall₂.length_eq refs).symm
      refine ⟨{ target with refs := target.refs ++ [.refv value'] }, .val (.loc true target.refs.length), ?_, ?_, ?_⟩
      · change vr (.loc true source.refs.length) (.loc true target.refs.length)
        simpa [lengths] using basicRelLoc vr simple true source.refs.length
      · exact simpleState.2.1 source target _ _ ⟨states, List.rel_append refs (.cons head .nil)⟩
      · simp [doApp, doAppNumeric, doAppMemory, SemanticPrimitivesHOL.storeAlloc]

private theorem simpleAallocFixed {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .aallocFixed) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .aallocFixed) values' = some (targetFinal, result') := by
  simp [doApp, doAppNumeric, doAppMemory, SemanticPrimitivesHOL.storeAlloc] at run
  rcases run with ⟨rfl, rfl⟩
  have refs := simpleState.1 source target states
  have lengths : target.refs.length = source.refs.length := (List.Forall₂.length_eq refs).symm
  refine ⟨{ target with refs := target.refs ++ [.varray values'] }, .val (.loc true source.refs.length),
    basicRelLoc vr simple true source.refs.length, ?_, ?_⟩
  · exact simpleState.2.1 source target _ _ ⟨states, List.rel_append refs (.cons related .nil)⟩
  · simp [doApp, doAppNumeric, doAppMemory, SemanticPrimitivesHOL.storeAlloc, lengths]

private theorem simpleOpassign {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .opassign) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .opassign) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric, doAppMemory] at run
    | @cons value value' tail tail' valueRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric, doAppMemory] at run
      | nil =>
        cases loc with
        | loc flag index =>
          have eq := simpleRelLoc vr simple flag index loc' locRel
          subst loc'
          cases assigned : SemanticPrimitivesHOL.storeAssign index (.refv value) source.refs with
          | none => simp [doApp, doAppNumeric, doAppMemory, assigned] at run
          | some refs =>
            obtain ⟨refs', assignTarget, finalStates⟩ :=
              simpleStateRel_storeAssign vr sr index (.refv value) source refs target (.refv value')
                ⟨simpleState, assigned, states, valueRel⟩
            simp [doApp, doAppNumeric, doAppMemory, assigned] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨{ target with refs := refs' }, .val unitValue, basicRelConvNil vr simple none, finalStates,
              by simp [doApp, doAppNumeric, doAppMemory, assignTarget]⟩
        | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [doApp, doAppNumeric, doAppMemory] at run

private theorem simpleRelLit (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (lit : Lit) (value' : Value) (related : vr (.litv lit) value') : value' = .litv lit := by
  exact ((simple.2 _ _ (by simp [isClosure])).mp related).1

private theorem simpleStrlen {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .strlen) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .strlen) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | nil =>
      cases value with
      | litv lit =>
        have eq := simpleRelLit vr simple lit value' valueRel
        subst value'
        cases lit with
        | strLit string =>
          simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (.litv (.intLit string.explode.length)), basicRelLit vr simple _, states,
            by simp [doApp, doAppNumeric, doAppMemory, doAppData]⟩
        | intLit _ | word8 _ | word64 _ | char _ | float64 _ =>
          simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
      | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [doApp, doAppNumeric, doAppMemory, doAppData] at run

private theorem simpleConfigGC {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .configGC) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .configGC) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons first first' tail tail' firstRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | @cons second second' tail tail' secondRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
      | nil =>
        cases first with
        | litv literal =>
          have eq := simpleRelLit vr simple literal first' firstRel
          subst first'
          cases literal with
          | intLit first =>
            cases second with
            | litv literal =>
              have eq := simpleRelLit vr simple literal second' secondRel
              subst second'
              cases literal with
              | intLit second =>
                simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
                rcases run with ⟨rfl, rfl⟩
                exact ⟨target, .val unitValue, basicRelConvNil vr simple none, states,
                  by simp [doApp, doAppNumeric, doAppMemory, doAppData]⟩
              | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
                simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
            | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
          | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
            simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
        | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [doApp, doAppNumeric, doAppMemory, doAppData] at run

private theorem simpleRelVector (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (fields : List Value) (value' : Value) (related : vr (.vectorv fields) value') :
    ∃ fields', value' = .vectorv fields' ∧ List.Forall₂ vr fields fields' := by
  have h := (simple.2 _ _ (by simp [isClosure])).mp related
  obtain ⟨fields', rfl⟩ := h.1
  exact ⟨fields', rfl, h.2⟩

private theorem basicRelVector (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (fields fields' : List Value) (related : List.Forall₂ vr fields fields') :
    vr (.vectorv fields) (.vectorv fields') := by
  apply (simple.2 _ _ (by simp [isClosure])).mpr
  exact ⟨⟨fields', rfl⟩, related⟩

private theorem simpleVectorFromList {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .vfromList) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .vfromList) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | nil =>
      cases decoded : valueToList value with
      | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded] at run
      | some items =>
        obtain ⟨items', decoded', itemsRel⟩ := simpleValueToList vr simple value value' items valueRel decoded
        simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .val (.vectorv items'), basicRelVector vr simple items items' itemsRel, states,
          by simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded']⟩

private theorem simpleVectorLength {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .vlength) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .vlength) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | nil =>
      cases value with
      | vectorv items =>
        obtain ⟨items', rfl, itemsRel⟩ := simpleRelVector vr simple items value' valueRel
        have lengths := List.Forall₂.length_eq itemsRel
        simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .val (.litv (.intLit items.length)), basicRelLit vr simple _, states,
          by simp [doApp, doAppNumeric, doAppMemory, doAppData, ← lengths]⟩
      | litv _ | conv _ _ | loc _ _ | closure _ _ _ | recclosure _ _ _ =>
        simp [doApp, doAppNumeric, doAppMemory, doAppData] at run

private theorem simpleListAppend {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .listAppend) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .listAppend) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons first first' tail tail' firstRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | @cons second second' tail tail' secondRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
      | nil =>
        cases left : valueToList first with
        | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, left] at run
        | some xs =>
          cases right : valueToList second with
          | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, left, right] at run
          | some ys =>
            obtain ⟨xs', left', xsRel⟩ := simpleValueToList vr simple first first' xs firstRel left
            obtain ⟨ys', right', ysRel⟩ := simpleValueToList vr simple second second' ys secondRel right
            simp [doApp, doAppNumeric, doAppMemory, doAppData, left, right] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨target, .val (listToValue (xs' ++ ys')),
              simpleListToValue vr simple _ _ (List.rel_append xsRel ysRel), states,
              by simp [doApp, doAppNumeric, doAppMemory, doAppData, left', right']⟩

private theorem readIndexedState {C F A : Type} (state next : State C F) (unsafeOp : Bool)
    (items : List A) (index : Int) (convert : A → Value) (result : Result Value Value)
    (run : readIndexed state unsafeOp items index convert = some (next, result)) : next = state := by
  by_cases negative : index < 0
  · cases unsafeOp <;> simp [readIndexed, boundsFailure, negative] at run
    exact run.1.symm
  · cases found : items[index.toNat]? with
    | none =>
      cases unsafeOp <;> simp [readIndexed, boundsFailure, negative, found] at run
      exact run.1.symm
    | some _ =>
      simp [readIndexed, negative, found] at run
      exact run.1.symm

private theorem simpleReadIndexed {C D F : Type} (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (unsafeOp : Bool) (items items' : List Value) (index : Int)
    (related : List.Forall₂ vr items items') (result : Result Value Value)
    (run : readIndexed source unsafeOp items index id = some (source, result)) :
    ∃ result', readIndexed target unsafeOp items' index id = some (target, result') ∧ resultRel vr vr result result' := by
  by_cases negative : index < 0
  · cases unsafeOp with
    | true => simp [readIndexed, boundsFailure, negative] at run
    | false =>
      simp [readIndexed, boundsFailure, negative] at run
      subst result
      exact ⟨.err (.raise subscriptExnV), by simp [readIndexed, boundsFailure, negative], basicRelConvNil vr simple _⟩
  · cases found : items[index.toNat]? with
    | none =>
      have absent : items'[index.toNat]? = none := by
        rw [List.getElem?_eq_none_iff] at found ⊢
        simpa [List.Forall₂.length_eq related] using found
      cases unsafeOp with
      | true => simp [readIndexed, boundsFailure, negative, found] at run
      | false =>
        simp [readIndexed, boundsFailure, negative, found] at run
        subst result
        exact ⟨.err (.raise subscriptExnV), by simp [readIndexed, boundsFailure, negative, absent], basicRelConvNil vr simple _⟩
    | some value =>
      obtain ⟨value', found', valueRel⟩ := forall₂_lookup related index.toNat value found
      simp [readIndexed, negative, found] at run
      subst result
      exact ⟨.val value', by simp [readIndexed, negative, found'], valueRel⟩

private theorem simpleVectorRead {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (unsafeOp : Bool) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (if unsafeOp then .vsubUnsafe else .vsub)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (if unsafeOp then .vsubUnsafe else .vsub)) values' = some (targetFinal, result') := by
  cases related with
  | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons vector vector' tail tail' vectorRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | cons _ _ => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
      | nil =>
        cases vector with
        | vectorv items =>
          obtain ⟨items', rfl, itemsRel⟩ := simpleRelVector vr simple items vector' vectorRel
          cases idx with
          | litv literal =>
            have eq := simpleRelLit vr simple literal idx' idxRel
            subst idx'
            cases literal with
            | intLit index =>
              have unequal : (Op.vsub == Op.vsubUnsafe) = false := by decide
              have read : readIndexed source unsafeOp items index id = some (sourceFinal, result) := by
                cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, doAppData, unequal] using run
              have stateEq := readIndexedState source sourceFinal unsafeOp items index id result read
              subst sourceFinal
              obtain ⟨result', targetRead, resultRel⟩ := simpleReadIndexed vr simple source target unsafeOp items items' index itemsRel result read
              refine ⟨target, result', resultRel, states, ?_⟩
              cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, doAppData, unequal] using targetRead
            | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
              cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
          | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
        | litv _ | conv _ _ | loc _ _ | closure _ _ _ | recclosure _ _ _ =>
          cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, doAppData] at run

private theorem simpleImplode {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .implode) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .implode) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | nil =>
      cases decoded : valueToCharList value with
      | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded] at run
      | some chars =>
        have decoded' := simpleValueToCharList vr simple value value' chars valueRel decoded
        simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .val (.litv (.strLit (.implode chars))), basicRelLit vr simple _, states,
          by simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded']⟩

private theorem simpleStrcat {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .strcat) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .strcat) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | nil =>
      cases decoded : valueToList value with
      | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded] at run
      | some items =>
        cases concatenated : valuesToString items with
        | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded, concatenated] at run
        | some string =>
          obtain ⟨items', decoded', itemsRel⟩ := simpleValueToList vr simple value value' items valueRel decoded
          have concatenated' := simpleValuesToString vr simple _ _ string itemsRel concatenated
          simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded, concatenated] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨target, .val (.litv (.strLit string)), basicRelLit vr simple _, states,
            by simp [doApp, doAppNumeric, doAppMemory, doAppData, decoded', concatenated']⟩

private theorem simpleLiteralValues (vr : Value → Value → Prop) (simple : simpleValueRel vr) (literals : List Lit) :
    List.Forall₂ vr (literals.map Value.litv) (literals.map Value.litv) := by
  induction literals with
  | nil => exact .nil
  | cons lit _ ih => exact .cons (basicRelLit vr simple lit) ih

private theorem simpleExplode {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .explode) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .explode) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | nil =>
      cases value with
      | litv lit =>
        have eq := simpleRelLit vr simple lit value' valueRel
        subst value'
        cases lit with
        | strLit string =>
          simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨target, .val (listToValue (string.explode.map (.litv ∘ Lit.char))), ?_, states, ?_⟩
          · apply simpleListToValue vr simple
            simpa [List.map_map, Function.comp_def] using simpleLiteralValues vr simple (string.explode.map Lit.char)
          · simp [doApp, doAppNumeric, doAppMemory, doAppData]
        | intLit _ | word8 _ | word64 _ | char _ | float64 _ =>
          simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
      | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [doApp, doAppNumeric, doAppMemory, doAppData] at run

private theorem simpleLookupArray {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (states : sr source target)
    (address : Nat) (items : List Value)
    (found : SemanticPrimitivesHOL.storeLookup address source.refs = some (.varray items)) :
    ∃ items', SemanticPrimitivesHOL.storeLookup address target.refs = some (.varray items') ∧ List.Forall₂ vr items items' := by
  obtain ⟨entry, lookup, relation⟩ := simpleStateRel_storeLookup vr sr address source (.varray items) target
    ⟨simpleState, found, states⟩
  cases entry <;> simp [storeValueRel] at relation
  case varray items' => exact ⟨items', lookup, relation⟩

private theorem simpleLookupBytes {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (states : sr source target)
    (address : Nat) (bytes : List (BitVec 8))
    (found : SemanticPrimitivesHOL.storeLookup address source.refs = some (.w8array bytes)) :
    SemanticPrimitivesHOL.storeLookup address target.refs = some (.w8array bytes) := by
  obtain ⟨entry, lookup, relation⟩ := simpleStateRel_storeLookup vr sr address source (.w8array bytes) target
    ⟨simpleState, found, states⟩
  cases entry <;> simp [storeValueRel] at relation
  case w8array bytes' => simpa [← relation] using lookup

private theorem simpleArrayLength {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .alength) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .alength) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory] at run
    | nil =>
      cases value with
      | loc flag address =>
        have eq := simpleRelLoc vr simple flag address value' valueRel
        subst value'
        cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
        | none => simp [doApp, doAppNumeric, doAppMemory, found] at run
        | some entry =>
          cases entry with
          | varray items =>
            obtain ⟨items', found', itemsRel⟩ := simpleLookupArray vr sr simpleState source target states address items found
            have lengths := List.Forall₂.length_eq itemsRel
            simp [doApp, doAppNumeric, doAppMemory, found] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨target, .val (.litv (.intLit items.length)), basicRelLit vr simple _, states,
              by simp [doApp, doAppNumeric, doAppMemory, found', ← lengths]⟩
          | refv _ | w8array _ | thunk _ _ => simp [doApp, doAppNumeric, doAppMemory, found] at run
      | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [doApp, doAppNumeric, doAppMemory] at run

private theorem simpleByteArrayLength {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .aw8length) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .aw8length) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory] at run
    | nil =>
      cases value with
      | loc flag address =>
        have eq := simpleRelLoc vr simple flag address value' valueRel
        subst value'
        cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
        | none => simp [doApp, doAppNumeric, doAppMemory, found] at run
        | some entry =>
          cases entry with
          | w8array bytes =>
            have found' := simpleLookupBytes vr sr simpleState source target states address bytes found
            simp [doApp, doAppNumeric, doAppMemory, found] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨target, .val (.litv (.intLit bytes.length)), basicRelLit vr simple _, states,
              by simp [doApp, doAppNumeric, doAppMemory, found']⟩
          | refv _ | varray _ | thunk _ _ => simp [doApp, doAppNumeric, doAppMemory, found] at run
      | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
        simp [doApp, doAppNumeric, doAppMemory] at run

private theorem simpleArrayAlloc {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .aalloc) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .aalloc) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons size size' tail tail' sizeRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric, doAppMemory] at run
    | @cons value value' tail tail' valueRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric, doAppMemory] at run
      | nil =>
        cases size with
        | litv literal =>
          have eq := simpleRelLit vr simple literal size' sizeRel
          subst size'
          cases literal with
          | intLit size =>
            by_cases negative : size < 0
            · simp [doApp, doAppNumeric, doAppMemory, boundsFailure, negative] at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨target, .err (.raise subscriptExnV), basicRelConvNil vr simple _, states,
                by simp [doApp, doAppNumeric, doAppMemory, boundsFailure, negative]⟩
            · simp [doApp, doAppNumeric, doAppMemory, SemanticPrimitivesHOL.storeAlloc, negative] at run
              rcases run with ⟨rfl, rfl⟩
              have refs := simpleState.1 source target states
              have lengths : target.refs.length = source.refs.length := (List.Forall₂.length_eq refs).symm
              refine ⟨{ target with refs := target.refs ++ [.varray (List.replicate size.toNat value')] },
                .val (.loc true source.refs.length), basicRelLoc vr simple true source.refs.length, ?_, ?_⟩
              · apply simpleState.2.1 source target _ _
                refine ⟨states, List.rel_append refs (.cons ?_ .nil)⟩
                exact (forall₂_replicate_iff vr size.toNat value value').mpr (fun _ => valueRel)
              · simp [doApp, doAppNumeric, doAppMemory, SemanticPrimitivesHOL.storeAlloc, negative, lengths]
          | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
            simp [doApp, doAppNumeric, doAppMemory] at run
        | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [doApp, doAppNumeric, doAppMemory] at run

private theorem simpleArrayRead {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (unsafeOp : Bool) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (if unsafeOp then .asubUnsafe else .asub)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (if unsafeOp then .asubUnsafe else .asub)) values' = some (targetFinal, result') := by
  cases related with
  | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | cons _ _ => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
      | nil =>
        cases loc with
        | loc flag address =>
          have eq := simpleRelLoc vr simple flag address loc' locRel
          subst loc'
          cases idx with
          | litv literal =>
            have eq := simpleRelLit vr simple literal idx' idxRel
            subst idx'
            cases literal with
            | intLit index =>
              cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
              | none => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, found] at run
              | some entry =>
                cases entry with
                | varray items =>
                  obtain ⟨items', found', itemsRel⟩ := simpleLookupArray vr sr simpleState source target states address items found
                  have unequal : (Op.asub == Op.asubUnsafe) = false := by decide
                  have read : readIndexed source unsafeOp items index id = some (sourceFinal, result) := by
                    cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, found, unequal] using run
                  have stateEq := readIndexedState source sourceFinal unsafeOp items index id result read
                  subst sourceFinal
                  obtain ⟨result', targetRead, resultRel⟩ := simpleReadIndexed vr simple source target unsafeOp items items' index itemsRel result read
                  refine ⟨target, result', resultRel, states, ?_⟩
                  cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, found', unequal] using targetRead
                | refv _ | w8array _ | thunk _ _ =>
                  cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, found] at run
            | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
              cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
          | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
        | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run

private theorem simpleUpdateIndexedArray {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (unsafeOp : Bool) (address : Nat) (items items' : List Value) (index : Int)
    (value value' : Value) (result : Result Value Value) (states : sr source target)
    (itemsRel : List.Forall₂ vr items items') (values : vr value value')
    (run : updateIndexed source unsafeOp address items index value .varray = some (sourceFinal, result)) :
    ∃ targetFinal result', updateIndexed target unsafeOp address items' index value' .varray = some (targetFinal, result') ∧
      sr sourceFinal targetFinal ∧ resultRel vr vr result result' := by
  have lengths : items'.length = items.length := (List.Forall₂.length_eq itemsRel).symm
  by_cases bounds : index < 0 ∨ items.length ≤ index.toNat
  · have bounds' : index < 0 ∨ items'.length ≤ index.toNat := by simpa [lengths] using bounds
    cases unsafeOp with
    | true => simp [updateIndexed, boundsFailure, bounds] at run
    | false =>
      simp [updateIndexed, boundsFailure, bounds] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, .err (.raise subscriptExnV), by simp [updateIndexed, boundsFailure, bounds'], states,
        basicRelConvNil vr simple _⟩
  · have bounds' : ¬ (index < 0 ∨ items'.length ≤ index.toNat) := by simpa [lengths] using bounds
    cases assigned : SemanticPrimitivesHOL.storeAssign address (.varray (items.set index.toNat value)) source.refs with
    | none => simp [updateIndexed, bounds, assigned] at run
    | some refs =>
      have entries : storeValueRel vr (.varray (items.set index.toNat value))
          (.varray (items'.set index.toNat value')) := Flapjack.forall₂_set _ _ _ _ _ index.toNat ⟨values, itemsRel⟩
      obtain ⟨refs', assigned', finalStates⟩ := simpleStateRel_storeAssign vr sr address
        (.varray (items.set index.toNat value)) source refs target (.varray (items'.set index.toNat value'))
        ⟨simpleState, assigned, states, entries⟩
      simp [updateIndexed, bounds, assigned] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨{ target with refs := refs' }, .val unitValue, by simp [updateIndexed, bounds', assigned'],
        finalStates, basicRelConvNil vr simple none⟩

private theorem simpleArrayUpdate {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (unsafeOp : Bool) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (if unsafeOp then .aupdateUnsafe else .aupdate)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (if unsafeOp then .aupdateUnsafe else .aupdate)) values' = some (targetFinal, result') := by
  cases related with
  | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
      | @cons value value' tail tail' valueRel rest =>
        cases rest with
        | cons _ _ => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
        | nil =>
          cases loc with
          | loc flag address =>
            have eq := simpleRelLoc vr simple flag address loc' locRel
            subst loc'
            cases idx with
            | litv literal =>
              have eq := simpleRelLit vr simple literal idx' idxRel
              subst idx'
              cases literal with
              | intLit index =>
                cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
                | none => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, found] at run
                | some entry =>
                  cases entry with
                  | varray items =>
                    obtain ⟨items', found', itemsRel⟩ := simpleLookupArray vr sr simpleState source target states address items found
                    have unequal : (Op.aupdate == Op.aupdateUnsafe) = false := by decide
                    have update : updateIndexed source unsafeOp address items index value .varray = some (sourceFinal, result) := by
                      cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, found, unequal] using run
                    obtain ⟨targetFinal, result', update', finalStates, results⟩ :=
                      simpleUpdateIndexedArray vr sr simple simpleState source target sourceFinal unsafeOp address items items'
                        index value value' result states itemsRel valueRel update
                    refine ⟨targetFinal, result', results, finalStates, ?_⟩
                    cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, found', unequal] using update'
                  | refv _ | w8array _ | thunk _ _ =>
                    cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, found] at run
              | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
                cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
            | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
          | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run

private theorem simpleReadIndexedBytes {C D F : Type} (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (unsafeOp : Bool) (bytes : List (BitVec 8)) (index : Int)
    (result : Result Value Value)
    (run : readIndexed source unsafeOp bytes index (.litv ∘ Lit.word8) = some (source, result)) :
    readIndexed target unsafeOp bytes index (.litv ∘ Lit.word8) = some (target, result) ∧ resultRel vr vr result result := by
  by_cases negative : index < 0
  · cases unsafeOp with
    | true => simp [readIndexed, boundsFailure, negative] at run
    | false =>
      simp [readIndexed, boundsFailure, negative] at run
      subst result
      exact ⟨by simp [readIndexed, boundsFailure, negative], basicRelConvNil vr simple _⟩
  · cases found : bytes[index.toNat]? with
    | none =>
      cases unsafeOp with
      | true => simp [readIndexed, boundsFailure, negative, found] at run
      | false =>
        simp [readIndexed, boundsFailure, negative, found] at run
        subst result
        exact ⟨by simp [readIndexed, boundsFailure, negative, found], basicRelConvNil vr simple _⟩
    | some byte =>
      simp [readIndexed, negative, found] at run
      subst result
      exact ⟨by simp [readIndexed, negative, found], basicRelLit vr simple _⟩

private theorem simpleByteArrayRead {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (unsafeOp : Bool) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (if unsafeOp then .aw8subUnsafe else .aw8sub)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (if unsafeOp then .aw8subUnsafe else .aw8sub)) values' = some (targetFinal, result') := by
  cases related with
  | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | cons _ _ => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
      | nil =>
        cases loc with
        | loc flag address =>
          have eq := simpleRelLoc vr simple flag address loc' locRel
          subst loc'
          cases idx with
          | litv literal =>
            have eq := simpleRelLit vr simple literal idx' idxRel
            subst idx'
            cases literal with
            | intLit index =>
              cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
              | none => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, found] at run
              | some entry =>
                cases entry with
                | w8array bytes =>
                  have found' := simpleLookupBytes vr sr simpleState source target states address bytes found
                  have unequal : (Op.aw8sub == Op.aw8subUnsafe) = false := by decide
                  have read : readIndexed source unsafeOp bytes index (.litv ∘ Lit.word8) = some (sourceFinal, result) := by
                    cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, found, unequal] using run
                  have stateEq := readIndexedState source sourceFinal unsafeOp bytes index (.litv ∘ Lit.word8) result read
                  subst sourceFinal
                  obtain ⟨targetRead, resultRel⟩ := simpleReadIndexedBytes vr simple source target unsafeOp bytes index result read
                  refine ⟨target, result, resultRel, states, ?_⟩
                  cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, found', unequal] using targetRead
                | refv _ | varray _ | thunk _ _ =>
                  cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, found] at run
            | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
              cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
          | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
        | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run

private theorem simpleUpdateIndexedBytes {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (unsafeOp : Bool) (address : Nat) (bytes : List (BitVec 8)) (index : Int) (byte : BitVec 8)
    (result : Result Value Value) (states : sr source target)
    (run : updateIndexed source unsafeOp address bytes index byte .w8array = some (sourceFinal, result)) :
    ∃ targetFinal, updateIndexed target unsafeOp address bytes index byte .w8array = some (targetFinal, result) ∧
      sr sourceFinal targetFinal ∧ resultRel vr vr result result := by
  by_cases bounds : index < 0 ∨ bytes.length ≤ index.toNat
  · cases unsafeOp with
    | true => simp [updateIndexed, boundsFailure, bounds] at run
    | false =>
      simp [updateIndexed, boundsFailure, bounds] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, by simp [updateIndexed, boundsFailure, bounds], states, basicRelConvNil vr simple _⟩
  · cases assigned : SemanticPrimitivesHOL.storeAssign address (.w8array (bytes.set index.toNat byte)) source.refs with
    | none => simp [updateIndexed, bounds, assigned] at run
    | some refs =>
      obtain ⟨refs', assigned', finalStates⟩ := simpleStateRel_storeAssign vr sr address
        (.w8array (bytes.set index.toNat byte)) source refs target (.w8array (bytes.set index.toNat byte))
        ⟨simpleState, assigned, states, rfl⟩
      simp [updateIndexed, bounds, assigned] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨{ target with refs := refs' }, by simp [updateIndexed, bounds, assigned'], finalStates,
        basicRelConvNil vr simple none⟩

private theorem simpleByteArrayUpdate {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (unsafeOp : Bool) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (if unsafeOp then .aw8updateUnsafe else .aw8update)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (if unsafeOp then .aw8updateUnsafe else .aw8update)) values' = some (targetFinal, result') := by
  cases related with
  | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | nil => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
      | @cons value value' tail tail' valueRel rest =>
        cases rest with
        | cons _ _ => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
        | nil =>
          cases loc with
          | loc flag address =>
            have eq := simpleRelLoc vr simple flag address loc' locRel
            subst loc'
            cases idx with
            | litv literal =>
              have eq := simpleRelLit vr simple literal idx' idxRel
              subst idx'
              cases literal with
              | intLit index =>
                cases value with
                | litv literal =>
                  have eq := simpleRelLit vr simple literal value' valueRel
                  subst value'
                  cases literal with
                  | word8 byte =>
                    cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
                    | none => cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, found] at run
                    | some entry =>
                      cases entry with
                      | w8array bytes =>
                        have found' := simpleLookupBytes vr sr simpleState source target states address bytes found
                        have unequal : (Op.aw8update == Op.aw8updateUnsafe) = false := by decide
                        have update : updateIndexed source unsafeOp address bytes index byte .w8array = some (sourceFinal, result) := by
                          cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, found, unequal] using run
                        obtain ⟨targetFinal, update', finalStates, results⟩ :=
                          simpleUpdateIndexedBytes vr sr simple simpleState source target sourceFinal unsafeOp address bytes index byte result states update
                        refine ⟨targetFinal, result, results, finalStates, ?_⟩
                        cases unsafeOp <;> simpa [doApp, doAppNumeric, doAppMemory, found', unequal] using update'
                      | refv _ | varray _ | thunk _ _ =>
                        cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory, found] at run
                  | intLit _ | word64 _ | char _ | strLit _ | float64 _ =>
                    cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
                | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
                  cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
              | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
                cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
            | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run
          | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
            cases unsafeOp <;> simp [doApp, doAppNumeric, doAppMemory] at run

private theorem simpleByteArrayAlloc {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .aw8alloc) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .aw8alloc) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory] at run
  | @cons size size' tail tail' sizeRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric, doAppMemory] at run
    | @cons value value' tail tail' valueRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric, doAppMemory] at run
      | nil =>
        cases size with
        | litv literal =>
          have eq := simpleRelLit vr simple literal size' sizeRel
          subst size'
          cases literal with
          | intLit size =>
            cases value with
            | litv literal =>
              have eq := simpleRelLit vr simple literal value' valueRel
              subst value'
              cases literal with
              | word8 byte =>
                by_cases negative : size < 0
                · simp [doApp, doAppNumeric, doAppMemory, boundsFailure, negative] at run
                  rcases run with ⟨rfl, rfl⟩
                  exact ⟨target, .err (.raise subscriptExnV), basicRelConvNil vr simple _, states,
                    by simp [doApp, doAppNumeric, doAppMemory, boundsFailure, negative]⟩
                · simp [doApp, doAppNumeric, doAppMemory, SemanticPrimitivesHOL.storeAlloc, negative] at run
                  rcases run with ⟨rfl, rfl⟩
                  have refs := simpleState.1 source target states
                  have lengths : target.refs.length = source.refs.length := (List.Forall₂.length_eq refs).symm
                  refine ⟨{ target with refs := target.refs ++ [.w8array (List.replicate size.toNat byte)] },
                    .val (.loc true source.refs.length), basicRelLoc vr simple true source.refs.length, ?_, ?_⟩
                  · exact simpleState.2.1 source target _ _ ⟨states, List.rel_append refs (.cons rfl .nil)⟩
                  · simp [doApp, doAppNumeric, doAppMemory, SemanticPrimitivesHOL.storeAlloc, negative, lengths]
              | intLit _ | word64 _ | char _ | strLit _ | float64 _ =>
                simp [doApp, doAppNumeric, doAppMemory] at run
            | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              simp [doApp, doAppNumeric, doAppMemory] at run
          | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
            simp [doApp, doAppNumeric, doAppMemory] at run
        | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [doApp, doAppNumeric, doAppMemory] at run

private theorem simpleFFI {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (name : Flapjack.Basis.Pure.MlString.MlString) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (.ffi name)) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (.ffi name)) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons config config' tail tail' configRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | @cons loc loc' tail tail' locRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
      | nil =>
        cases config with
        | litv literal =>
          have configEq := simpleRelLit vr simple literal config' configRel
          subst config'
          cases literal with
          | strLit configuration =>
            cases loc with
            | loc flag address =>
              have locEq := simpleRelLoc vr simple flag address loc' locRel
              subst loc'
              cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
              | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, found] at run
              | some entry =>
                cases entry with
                | w8array bytes =>
                  have found' := simpleLookupBytes vr sr simpleState source target states address bytes found
                  have ffiEq := simpleState.2.2.2.2.1 source target states
                  cases called : Flapjack.callFFIHOL source.ffi (.extCall name) configuration.explode bytes with
                  | final event =>
                    simp [doApp, doAppNumeric, doAppMemory, doAppData, found, called] at run
                    rcases run with ⟨rfl, rfl⟩
                    exact ⟨target, .err (.abort (.ffiError event)), rfl, states,
                      by simp [doApp, doAppNumeric, doAppMemory, doAppData, found', ← ffiEq, called]⟩
                  | ret ffi bytes' =>
                    cases assigned : SemanticPrimitivesHOL.storeAssign address (.w8array bytes') source.refs with
                    | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, found, called, assigned] at run
                    | some refs =>
                      obtain ⟨refs', assigned', refsRel⟩ := simpleStateRel_storeAssign vr sr address
                        (.w8array bytes') source refs target (.w8array bytes') ⟨simpleState, assigned, states, rfl⟩
                      simp [doApp, doAppNumeric, doAppMemory, doAppData, found, called, assigned] at run
                      rcases run with ⟨rfl, rfl⟩
                      refine ⟨{ target with refs := refs', ffi := ffi }, .val unitValue,
                        basicRelConvNil vr simple none, ?_, ?_⟩
                      · exact simpleState.2.2.2.2.2 _ _ ffi ffi ⟨refsRel, rfl⟩
                      · simp [doApp, doAppNumeric, doAppMemory, doAppData, found', ← ffiEq, called, assigned']
                | refv _ | varray _ | thunk _ _ =>
                  simp [doApp, doAppNumeric, doAppMemory, doAppData, found] at run
            | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
          | intLit _ | word8 _ | word64 _ | char _ | float64 _ =>
            simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
        | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [doApp, doAppNumeric, doAppMemory, doAppData] at run

private def simpleDestThunkRel (vr : Value → Value → Prop) : DestThunkResult → DestThunkResult → Prop
  | .badRef, .badRef | .notThunk, .notThunk => True
  | .isThunk mode value, .isThunk mode' value' => mode = mode' ∧ vr value value'
  | _, _ => False

private theorem simpleDestThunk (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    {left right : List Value} {store store' : SemanticPrimitivesHOL.Store Value}
    (values : List.Forall₂ vr left right)
    (stores : List.Forall₂ (storeValueRel vr) store store') :
    simpleDestThunkRel vr (destThunk left store) (destThunk right store') := by
  cases values with
  | nil => simp [destThunk, simpleDestThunkRel]
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [destThunk, simpleDestThunkRel]
    | nil =>
      cases value with
      | loc flag index =>
        have eq := simpleRelLoc vr simple flag index value' head
        subst value'
        cases found : SemanticPrimitivesHOL.storeLookup index store with
        | none =>
          have absent := storeValueRel_lookup_none stores index found
          simp [destThunk, found, absent, simpleDestThunkRel]
        | some entry =>
          obtain ⟨entry', found', rel⟩ := storeValueRel_lookup stores index entry found
          cases flag <;> cases entry <;> cases entry' <;> simp_all [storeValueRel, destThunk, simpleDestThunkRel]
      | litv lit =>
        have eq := simpleRelLit vr simple lit value' head
        subst value'
        simp [destThunk, simpleDestThunkRel]
      | conv stamp fields =>
        obtain ⟨fields', rfl, _⟩ := simpleRelConv vr simple stamp fields value' head
        simp [destThunk, simpleDestThunkRel]
      | vectorv fields =>
        obtain ⟨fields', rfl, _⟩ := simpleRelVector vr simple fields value' head
        simp [destThunk, simpleDestThunkRel]
      | closure env name body =>
        have shape := (simple.1 _ _ head).mp (by simp [isClosure])
        rcases shape with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> simp [destThunk, simpleDestThunkRel]
      | recclosure env funs name =>
        have shape := (simple.1 _ _ head).mp (by simp [isClosure])
        rcases shape with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> simp [destThunk, simpleDestThunkRel]

private theorem simpleBadThunkUpdate (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (mode : ThunkMode) (value value' : Value) (store store' : SemanticPrimitivesHOL.Store Value)
    (values : vr value value') (stores : List.Forall₂ (storeValueRel vr) store store') :
    badThunkUpdate mode value store = badThunkUpdate mode value' store' := by
  cases mode with
  | notEvaluated => rfl
  | evaluated =>
    have related := simpleDestThunk vr simple (.cons values .nil) stores
    cases left : destThunk [value] store <;>
      cases right : destThunk [value'] store' <;>
      simp_all [simpleDestThunkRel, badThunkUpdate]

private theorem simpleThunkAlloc {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (mode : ThunkMode) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (.thunkOp (.allocThunk mode))) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (.thunkOp (.allocThunk mode))) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons value value' tail tail' values rest =>
    cases rest with
    | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | nil =>
      have refs := simpleState.1 source target states
      have badEq := simpleBadThunkUpdate vr simple mode value value' source.refs target.refs values refs
      cases bad : badThunkUpdate mode value source.refs with
      | true => simp [doApp, doAppNumeric, doAppMemory, doAppData, bad] at run
      | false =>
        have bad' : badThunkUpdate mode value' target.refs = false := by rw [← badEq, bad]
        simp [doApp, doAppNumeric, doAppMemory, doAppData, SemanticPrimitivesHOL.storeAlloc, bad] at run
        rcases run with ⟨rfl, rfl⟩
        have lengths : target.refs.length = source.refs.length := (List.Forall₂.length_eq refs).symm
        exact ⟨{ target with refs := target.refs ++ [.thunk mode value'] }, .val (.loc false source.refs.length),
          basicRelLoc vr simple false source.refs.length,
          simpleState.2.1 source target _ _ ⟨states, List.rel_append refs (.cons ⟨rfl, values⟩ .nil)⟩,
          by simp [doApp, doAppNumeric, doAppMemory, doAppData, SemanticPrimitivesHOL.storeAlloc, bad', lengths]⟩

private theorem simpleThunkUpdate {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (mode : ThunkMode) (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src (.thunkOp (.updateThunk mode))) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src (.thunkOp (.updateThunk mode))) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | @cons value value' tail tail' valueRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
      | nil =>
        cases loc with
        | loc flag address =>
          have eq := simpleRelLoc vr simple flag address loc' locRel
          subst loc'
          cases flag with
          | true => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
          | false =>
            have badEq := simpleBadThunkUpdate vr simple mode value value' source.refs target.refs valueRel (simpleState.1 source target states)
            cases bad : badThunkUpdate mode value source.refs with
            | true => simp [doApp, doAppNumeric, doAppMemory, doAppData, bad] at run
            | false =>
              have bad' : badThunkUpdate mode value' target.refs = false := by rw [← badEq, bad]
              cases assigned : SemanticPrimitivesHOL.storeAssign address (.thunk mode value) source.refs with
              | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, bad, assigned] at run
              | some refs =>
                obtain ⟨refs', assigned', finalStates⟩ := simpleStateRel_storeAssign vr sr address
                  (.thunk mode value) source refs target (.thunk mode value') ⟨simpleState, assigned, states, ⟨rfl, valueRel⟩⟩
                simp [doApp, doAppNumeric, doAppMemory, doAppData, bad, assigned] at run
                rcases run with ⟨rfl, rfl⟩
                exact ⟨{ target with refs := refs' }, .val unitValue, basicRelConvNil vr simple none, finalStates,
                  by simp [doApp, doAppNumeric, doAppMemory, doAppData, bad', assigned']⟩
        | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [doApp, doAppNumeric, doAppMemory, doAppData] at run

private theorem simpleReadIndexedLiterals {C D F A : Type} (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (items : List A) (index : Int) (literal : A → Lit)
    (result : Result Value Value) (run : readIndexed source false items index (.litv ∘ literal) = some (source, result)) :
    readIndexed target false items index (.litv ∘ literal) = some (target, result) ∧ resultRel vr vr result result := by
  by_cases negative : index < 0
  · simp [readIndexed, boundsFailure, negative] at run
    subst result
    exact ⟨by simp [readIndexed, boundsFailure, negative], basicRelConvNil vr simple _⟩
  · cases found : items[index.toNat]? with
    | none =>
      simp [readIndexed, boundsFailure, negative, found] at run
      subst result
      exact ⟨by simp [readIndexed, boundsFailure, negative, found], basicRelConvNil vr simple _⟩
    | some item =>
      simp [readIndexed, negative, found] at run
      subst result
      exact ⟨by simp [readIndexed, negative, found], basicRelLit vr simple _⟩

private theorem simpleStrsub {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .strsub) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .strsub) values' = some (targetFinal, result') := by
  cases related with
  | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | @cons value value' tail tail' valueRel rest =>
    cases rest with
    | nil => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
    | @cons idx idx' tail tail' idxRel rest =>
      cases rest with
      | cons _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
      | nil =>
        cases value with
        | litv literal =>
          have eq := simpleRelLit vr simple literal value' valueRel
          subst value'
          cases literal with
          | strLit string =>
            cases idx with
            | litv literal =>
              have eq := simpleRelLit vr simple literal idx' idxRel
              subst idx'
              cases literal with
              | intLit index =>
                have read : readIndexed source false string.explode index (.litv ∘ Lit.char) = some (sourceFinal, result) := by
                  simpa [doApp, doAppNumeric, doAppMemory, doAppData] using run
                have eq := readIndexedState source sourceFinal false string.explode index (.litv ∘ Lit.char) result read
                subst sourceFinal
                obtain ⟨targetRead, resultRel⟩ := simpleReadIndexedLiterals vr simple source target string.explode index Lit.char result read
                exact ⟨target, result, resultRel, states,
                  by simpa [doApp, doAppNumeric, doAppMemory, doAppData] using targetRead⟩
              | word8 _ | word64 _ | char _ | strLit _ | float64 _ =>
                simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
            | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
              simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
          | intLit _ | word8 _ | word64 _ | char _ | float64 _ =>
            simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
        | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [doApp, doAppNumeric, doAppMemory, doAppData] at run

private theorem simpleScalarList (vr : Value → Value → Prop) (simple : simpleValueRel vr)
    {values values' : List Value} (related : List.Forall₂ vr values values')
    (scalar : ∀ value ∈ values, (∃ literal, value = .litv literal) ∨ (∃ flag index, value = .loc flag index)) :
    values' = values := by
  induction related with
  | nil => rfl
  | @cons value value' tail tail' valueRel tailRel ih =>
    have headEq : value' = value := by
      rcases scalar value (by simp) with ⟨literal, rfl⟩ | ⟨flag, index, rfl⟩
      · exact simpleRelLit vr simple literal value' valueRel
      · exact simpleRelLoc vr simple flag index value' valueRel
    have tailEq := ih (by intro value member; exact scalar value (List.mem_cons_of_mem _ member))
    simp [headEq, tailEq]

private theorem simpleCopyStrStrOperands {C F : Type} (state next : State C F) (values : List Value)
    (result : Result Value Value) (run : doApp state (.src .copyStrStr) values = some (next, result)) :
    ∃ string offset length, values = [.litv (.strLit string), .litv (.intLit offset), .litv (.intLit length)] := by
  simp only [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy] at run
  repeat' split at run <;> simp_all [boundsFailure]

private theorem simpleCopyStrStr {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .copyStrStr) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .copyStrStr) values' = some (targetFinal, result') := by
  obtain ⟨string, offset, length, rfl⟩ := simpleCopyStrStrOperands source sourceFinal values result run
  have equal : values' = [.litv (.strLit string), .litv (.intLit offset), .litv (.intLit length)] := by
    apply simpleScalarList vr simple related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact Or.inl ⟨_, rfl⟩
  subst values'
  cases copied : SemanticPrimitivesHOL.copyArray (string.explode, offset) length none with
  | none =>
    simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, copied] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, .err (.raise subscriptExnV), basicRelConvNil vr simple _, states,
      by simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, copied]⟩
  | some chars =>
    simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, copied] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, .val (.litv (.strLit (.implode chars))), basicRelLit vr simple _, states,
      by simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, copied]⟩

private theorem simpleCopyAw8StrOperands {C F : Type} (state next : State C F) (values : List Value)
    (result : Result Value Value) (run : doApp state (.src .copyAw8Str) values = some (next, result)) :
    ∃ flag address offset length, values = [.loc flag address, .litv (.intLit offset), .litv (.intLit length)] := by
  simp only [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy] at run
  repeat' split at run <;> simp_all [boundsFailure]

private theorem simpleCopyAw8Str {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .copyAw8Str) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .copyAw8Str) values' = some (targetFinal, result') := by
  obtain ⟨flag, address, offset, length, rfl⟩ := simpleCopyAw8StrOperands source sourceFinal values result run
  have equal : values' = [.loc flag address, .litv (.intLit offset), .litv (.intLit length)] := by
    apply simpleScalarList vr simple related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  subst values'
  cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
  | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found] at run
  | some entry =>
    cases entry with
    | w8array bytes =>
      have found' := simpleLookupBytes vr sr simpleState source target states address bytes found
      cases copied : SemanticPrimitivesHOL.copyArray (bytes, offset) length none with
      | none =>
        simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, found, copied] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .err (.raise subscriptExnV), basicRelConvNil vr simple _, states,
          by simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, found', copied]⟩
      | some chars =>
        simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found, copied] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .val (.litv (.strLit (.implode chars))), basicRelLit vr simple _, states,
          by simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found', copied]⟩
    | refv _ | varray _ | thunk _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found] at run

private theorem simpleCopyStrAw8Operands {C F : Type} (state next : State C F) (values : List Value)
    (result : Result Value Value) (run : doApp state (.src .copyStrAw8) values = some (next, result)) :
    ∃ string offset length flag address destinationOffset,
      values = [.litv (.strLit string), .litv (.intLit offset), .litv (.intLit length),
        .loc flag address, .litv (.intLit destinationOffset)] := by
  simp only [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy] at run
  repeat' split at run <;> simp_all [boundsFailure]

private theorem simpleCopyStrAw8 {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .copyStrAw8) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .copyStrAw8) values' = some (targetFinal, result') := by
  obtain ⟨string, offset, length, flag, address, dstOffset, rfl⟩ := simpleCopyStrAw8Operands source sourceFinal values result run
  have equal : values' = [.litv (.strLit string), .litv (.intLit offset), .litv (.intLit length), .loc flag address, .litv (.intLit dstOffset)] := by
    apply simpleScalarList vr simple related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  subst values'
  cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
  | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found] at run
  | some entry =>
    cases entry with
    | w8array bytes =>
      have found' := simpleLookupBytes vr sr simpleState source target states address bytes found
      cases copied : SemanticPrimitivesHOL.copyArray (string.explode, offset) length (some (bytes, dstOffset)) with
      | none =>
        simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, found, copied] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, .err (.raise subscriptExnV), basicRelConvNil vr simple _, states,
          by simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, found', copied]⟩
      | some output =>
        cases assigned : SemanticPrimitivesHOL.storeAssign address (.w8array output) source.refs with
        | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found, copied, assigned] at run
        | some refs =>
          obtain ⟨refs', assigned', finalStates⟩ := simpleStateRel_storeAssign vr sr address
            (.w8array output) source refs target (.w8array output) ⟨simpleState, assigned, states, rfl⟩
          simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found, copied, assigned] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨{ target with refs := refs' }, .val unitValue, basicRelConvNil vr simple none, finalStates,
            by simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found', copied, assigned']⟩
    | refv _ | varray _ | thunk _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found] at run

private theorem simpleXorOperands {C F : Type} (state next : State C F) (values : List Value)
    (result : Result Value Value) (run : doApp state (.src .xorAw8StrUnsafe) values = some (next, result)) :
    ∃ flag address string, values = [.loc flag address, .litv (.strLit string)] := by
  simp only [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy] at run
  repeat' split at run <;> simp_all

private theorem simpleXor {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .xorAw8StrUnsafe) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .xorAw8StrUnsafe) values' = some (targetFinal, result') := by
  obtain ⟨flag, address, string, rfl⟩ := simpleXorOperands source sourceFinal values result run
  have equal : values' = [.loc flag address, .litv (.strLit string)] := by
    apply simpleScalarList vr simple related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  subst values'
  cases found : SemanticPrimitivesHOL.storeLookup address source.refs with
  | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found] at run
  | some entry =>
    cases entry with
    | w8array bytes =>
      have found' := simpleLookupBytes vr sr simpleState source target states address bytes found
      cases xored : SemanticPrimitivesHOL.xorBytes string.explode bytes with
      | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found, xored] at run
      | some output =>
        cases assigned : SemanticPrimitivesHOL.storeAssign address (.w8array output) source.refs with
        | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found, xored, assigned] at run
        | some refs =>
          obtain ⟨refs', assigned', finalStates⟩ := simpleStateRel_storeAssign vr sr address
            (.w8array output) source refs target (.w8array output) ⟨simpleState, assigned, states, rfl⟩
          simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found, xored, assigned] at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨{ target with refs := refs' }, .val unitValue, basicRelConvNil vr simple none, finalStates,
            by simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found', xored, assigned']⟩
    | refv _ | varray _ | thunk _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, found] at run

private theorem simpleCopyAw8Aw8Operands {C F : Type} (state next : State C F) (values : List Value)
    (result : Result Value Value) (run : doApp state (.src .copyAw8Aw8) values = some (next, result)) :
    ∃ srcFlag src offset length dstFlag dst dstOffset,
      values = [.loc srcFlag src, .litv (.intLit offset), .litv (.intLit length),
        .loc dstFlag dst, .litv (.intLit dstOffset)] := by
  simp only [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy] at run
  repeat' split at run <;> simp_all [boundsFailure]

private theorem simpleCopyAw8Aw8 {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (simple : simpleValueRel vr) (simpleState : simpleStateRel vr sr)
    (source : State C F) (target : State D F) (sourceFinal : State C F)
    (values values' : List Value) (result : Result Value Value)
    (states : sr source target) (related : List.Forall₂ vr values values')
    (run : doApp source (.src .copyAw8Aw8) values = some (sourceFinal, result)) :
    ∃ targetFinal result', resultRel vr vr result result' ∧ sr sourceFinal targetFinal ∧
      doApp target (.src .copyAw8Aw8) values' = some (targetFinal, result') := by
  obtain ⟨srcFlag, src, offset, length, dstFlag, dst, dstOffset, rfl⟩ := simpleCopyAw8Aw8Operands source sourceFinal values result run
  have equal : values' = [.loc srcFlag src, .litv (.intLit offset), .litv (.intLit length), .loc dstFlag dst, .litv (.intLit dstOffset)] := by
    apply simpleScalarList vr simple related
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  subst values'
  cases sourceFound : SemanticPrimitivesHOL.storeLookup src source.refs with
  | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, sourceFound] at run
  | some sourceEntry =>
    cases sourceEntry with
    | w8array bytes =>
      have sourceFound' := simpleLookupBytes vr sr simpleState source target states src bytes sourceFound
      cases destFound : SemanticPrimitivesHOL.storeLookup dst source.refs with
      | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, sourceFound, destFound] at run
      | some destEntry =>
        cases destEntry with
        | w8array dstBytes =>
          have destFound' := simpleLookupBytes vr sr simpleState source target states dst dstBytes destFound
          cases copied : SemanticPrimitivesHOL.copyArray (bytes, offset) length (some (dstBytes, dstOffset)) with
          | none =>
            simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, sourceFound, destFound, copied] at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨target, .err (.raise subscriptExnV), basicRelConvNil vr simple _, states,
              by simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, sourceFound', destFound', copied]⟩
          | some output =>
            cases assigned : SemanticPrimitivesHOL.storeAssign dst (.w8array output) source.refs with
            | none => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, sourceFound, destFound, copied, assigned] at run
            | some refs =>
              obtain ⟨refs', assigned', finalStates⟩ := simpleStateRel_storeAssign vr sr dst
                (.w8array output) source refs target (.w8array output) ⟨simpleState, assigned, states, rfl⟩
              simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, sourceFound, destFound, copied, assigned] at run
              rcases run with ⟨rfl, rfl⟩
              exact ⟨{ target with refs := refs' }, .val unitValue, basicRelConvNil vr simple none, finalStates,
                by simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, sourceFound', destFound', copied, assigned']⟩
        | refv _ | varray _ | thunk _ _ =>
          simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, sourceFound, destFound] at run
    | refv _ | varray _ | thunk _ _ => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, sourceFound] at run

/-- Any simple value and state relations simulate successful flat primitive application. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_do_app_thm"]
theorem simpleDoApp {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (op : FlatLang.Op)
    (premises : simpleValueRel vr ∧ simpleStateRel vr sr) :
    ∀ (s1 : State C F) (vs1 : List Value) (t1 : State C F) (r1 : Result Value Value)
      (s2 : State D F) (vs2 : List Value),
      doApp s1 op vs1 = some (t1, r1) → sr s1 s2 ∧ List.Forall₂ vr vs1 vs2 →
      ∃ (t2 : State D F) (r2 : Result Value Value),
        resultRel vr vr r1 r2 ∧ sr t1 t2 ∧ doApp s2 op vs2 = some (t2, r2) := by
  obtain ⟨simple, simpleState⟩ := premises
  intro source values sourceFinal result target values' run ⟨states, related⟩
  cases op with
  | src sourceOp =>
    cases sourceOp with
    | arith action typ => exact simpleArith vr sr simple simpleState source target sourceFinal action typ values values' result states related run
    | fromTo sourceTyp targetTyp => exact simpleFromTo vr sr simple simpleState source target sourceFinal sourceTyp targetTyp values values' result states related run
    | shift width shift amount => exact simpleShift vr sr simple simpleState source target sourceFinal width shift amount values values' result states related run
    | test test typ => exact simpleTest vr sr simple source target sourceFinal test typ values values' result states related run
    | equality => exact simpleEquality vr sr simple source target sourceFinal values values' result states related run
    | opref => exact simpleOpref vr sr simple simpleState source target sourceFinal values values' result states related run
    | opassign => exact simpleOpassign vr sr simple simpleState source target sourceFinal values values' result states related run
    | opderef => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy] at run
    | aallocEmpty => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy] at run
    | envId => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy] at run
    | aallocFixed => exact simpleAallocFixed vr sr simple simpleState source target sourceFinal values values' result states related run
    | aalloc => exact simpleArrayAlloc vr sr simple simpleState source target sourceFinal values values' result states related run
    | aw8alloc => exact simpleByteArrayAlloc vr sr simple simpleState source target sourceFinal values values' result states related run
    | alength => exact simpleArrayLength vr sr simple simpleState source target sourceFinal values values' result states related run
    | aw8length => exact simpleByteArrayLength vr sr simple simpleState source target sourceFinal values values' result states related run
    | aupdate => exact simpleArrayUpdate vr sr simple simpleState source target sourceFinal false values values' result states related run
    | aupdateUnsafe => exact simpleArrayUpdate vr sr simple simpleState source target sourceFinal true values values' result states related run
    | asub => exact simpleArrayRead vr sr simple simpleState source target sourceFinal false values values' result states related run
    | asubUnsafe => exact simpleArrayRead vr sr simple simpleState source target sourceFinal true values values' result states related run
    | aw8sub => exact simpleByteArrayRead vr sr simple simpleState source target sourceFinal false values values' result states related run
    | aw8subUnsafe => exact simpleByteArrayRead vr sr simple simpleState source target sourceFinal true values values' result states related run
    | aw8update => exact simpleByteArrayUpdate vr sr simple simpleState source target sourceFinal false values values' result states related run
    | aw8updateUnsafe => exact simpleByteArrayUpdate vr sr simple simpleState source target sourceFinal true values values' result states related run
    | vfromList => exact simpleVectorFromList vr sr simple source target sourceFinal values values' result states related run
    | vlength => exact simpleVectorLength vr sr simple source target sourceFinal values values' result states related run
    | listAppend => exact simpleListAppend vr sr simple source target sourceFinal values values' result states related run
    | strlen => exact simpleStrlen vr sr simple source target sourceFinal values values' result states related run
    | explode => exact simpleExplode vr sr simple source target sourceFinal values values' result states related run
    | implode => exact simpleImplode vr sr simple source target sourceFinal values values' result states related run
    | strsub => exact simpleStrsub vr sr simple source target sourceFinal values values' result states related run
    | strcat => exact simpleStrcat vr sr simple source target sourceFinal values values' result states related run
    | configGC => exact simpleConfigGC vr sr simple source target sourceFinal values values' result states related run
    | copyStrStr => exact simpleCopyStrStr vr sr simple source target sourceFinal values values' result states related run
    | copyAw8Str => exact simpleCopyAw8Str vr sr simple simpleState source target sourceFinal values values' result states related run
    | copyStrAw8 => exact simpleCopyStrAw8 vr sr simple simpleState source target sourceFinal values values' result states related run
    | copyAw8Aw8 => exact simpleCopyAw8Aw8 vr sr simple simpleState source target sourceFinal values values' result states related run
    | xorAw8StrUnsafe => exact simpleXor vr sr simple simpleState source target sourceFinal values values' result states related run
    | vsub => exact simpleVectorRead vr sr simple source target sourceFinal false values values' result states related run
    | vsubUnsafe => exact simpleVectorRead vr sr simple source target sourceFinal true values values' result states related run
    | ffi name => exact simpleFFI vr sr simple simpleState source target sourceFinal name values values' result states related run
    | opapp | eval => simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy] at run
    | thunkOp thunk =>
      cases thunk with
      | allocThunk mode => exact simpleThunkAlloc vr sr simple simpleState source target sourceFinal mode values values' result states related run
      | updateThunk mode => exact simpleThunkUpdate vr sr simple simpleState source target sourceFinal mode values values' result states related run
      | forceThunk => simp [doApp, doAppNumeric, doAppMemory, doAppData] at run
  | globalVarAlloc count => exact simpleGlobalAlloc vr sr simple simpleState source target sourceFinal count values values' result states related run
  | globalVarInit index => exact simpleGlobalInit vr sr simple simpleState source target sourceFinal index values values' result states related run
  | globalVarLookup index => exact simpleGlobalLookup vr sr simpleState source target sourceFinal index values values' result states related run
  | id => exact simpleId vr sr source target sourceFinal values values' result states related run
  | lenEq length => exact simpleLenEq vr sr simple source target sourceFinal length values values' result states related run
  | tagLenEq tag length => exact simpleTagLenEq vr sr simple source target sourceFinal tag length values values' result states related run
  | el index => exact simpleEl vr sr simple simpleState source target sourceFinal index values values' result states related run
end Flapjack.Compiler.Backend.FlatProps
