module

public import Flapjack.Compiler.Backend.FlatProps.SimpleRelations
public import Flapjack.Compiler.Backend.Semantics.FlatSem.Eval

@[expose] public section

/-! List conversion properties for simple flat value relations. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem

set_option maxRecDepth 4096 in
/-- Character-list decoding is preserved by any simple value relation. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_v_to_char_list_v_rel"]
theorem simpleValueToCharList (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (left right : Value)
    (chars : List Flapjack.Basis.Pure.MlString.HolChar)
    (related : relation left right) (decoded : valueToCharList left = some chars) :
    valueToCharList right = some chars := by
  cases left with
  | litv _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
    simp [valueToCharList] at decoded
  | conv stamp fields =>
    have info := (simple.2 _ _ (by simp [isClosure])).1 related
    obtain ⟨targetFields, rfl⟩ := info.1
    have fieldsRel : List.Forall₂ relation fields targetFields := by
      simpa [valueContainerXs] using info.2
    cases fields with
    | nil =>
      cases fieldsRel
      exact decoded
    | cons head rest =>
      cases rest with
      | nil => simp [valueToCharList] at decoded
      | cons tail more =>
        cases more with
        | cons _ _ => simp [valueToCharList] at decoded
        | nil =>
          cases fieldsRel with
          | cons headRel tailRel =>
            cases tailRel with
            | cons tailRel remaining =>
              cases remaining
              cases head with
              | litv literal =>
                have headInfo := (simple.2 _ _ (by simp [isClosure])).1 headRel
                have headEq := headInfo.1
                simp only [simpleBasicValRel] at headEq
                subst_vars
                cases literal with
                | char char =>
                  cases stamp with
                  | none => simp [valueToCharList] at decoded
                  | some stamp =>
                    obtain ⟨tag, typeId⟩ := stamp
                    by_cases valid : tag = BackendCommon.consTag ∧ typeId = some listId
                    · cases tailDecoded : valueToCharList tail with
                      | none => simp [valueToCharList, valid, tailDecoded] at decoded
                      | some tailChars =>
                        have targetTail := simpleValueToCharList relation simple tail _ tailChars tailRel tailDecoded
                        simpa [valueToCharList, valid, tailDecoded, targetTail] using decoded
                    · simp [valueToCharList, valid] at decoded
                | intLit _ | word8 _ | word64 _ | strLit _ | float64 _ =>
                  simp [valueToCharList] at decoded
              | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
                simp [valueToCharList] at decoded
termination_by sizeOf left

set_option maxRecDepth 4096 in
/-- Decoding related flat lists produces pointwise related elements. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_v_to_list_v_rel"]
theorem simpleValueToList (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (left right : Value) (values : List Value)
    (related : relation left right) (decoded : valueToList left = some values) :
    ∃ values', valueToList right = some values' ∧ List.Forall₂ relation values values' := by
  cases left with
  | litv _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
    simp [valueToList] at decoded
  | conv stamp fields =>
    have info := (simple.2 _ _ (by simp [isClosure])).1 related
    obtain ⟨targetFields, rfl⟩ := info.1
    have fieldsRel : List.Forall₂ relation fields targetFields := by
      simpa [valueContainerXs] using info.2
    cases fields with
    | nil =>
      cases fieldsRel
      cases stamp with
      | none => simp [valueToList] at decoded
      | some stamp =>
        obtain ⟨tag, typeId⟩ := stamp
        by_cases valid : tag = BackendCommon.nilTag ∧ typeId = some listId
        · simp [valueToList, valid] at decoded
          subst values
          exact ⟨[], by simp [valueToList, valid], .nil⟩
        · simp [valueToList, valid] at decoded
    | cons head rest =>
      cases rest with
      | nil => simp [valueToList] at decoded
      | cons tail more =>
        cases more with
        | cons _ _ => simp [valueToList] at decoded
        | nil =>
          cases fieldsRel with
          | cons headRel tailRel =>
            cases tailRel with
            | cons tailRel remaining =>
              cases remaining
              cases stamp with
              | none => simp [valueToList] at decoded
              | some stamp =>
                obtain ⟨tag, typeId⟩ := stamp
                by_cases valid : tag = BackendCommon.consTag ∧ typeId = some listId
                · cases tailDecoded : valueToList tail with
                  | none => simp [valueToList, valid, tailDecoded] at decoded
                  | some tailValues =>
                    simp [valueToList, valid, tailDecoded] at decoded
                    subst values
                    obtain ⟨targetValues, targetDecoded, targetRel⟩ :=
                      simpleValueToList relation simple tail _ tailValues tailRel tailDecoded
                    refine ⟨_ :: targetValues, ?_, .cons headRel targetRel⟩
                    simp [valueToList, valid, targetDecoded]
                · simp [valueToList, valid] at decoded
termination_by sizeOf left

/-- Encoding pointwise related lists produces related flat values. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_v_rel_list_to_v"]
theorem simpleListToValue (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (left right : List Value)
    (related : List.Forall₂ relation left right) :
    relation (listToValue left) (listToValue right) := by
  induction related with
  | nil =>
    apply (simple.2 _ _ (by simp [listToValue, isClosure])).2
    simp [listToValue, simpleBasicValRel, valueContainerXs]
  | cons head tail ih =>
    apply (simple.2 _ _ (by simp [listToValue, isClosure])).2
    constructor
    · simp [listToValue, simpleBasicValRel]
    · simpa [listToValue, valueContainerXs] using List.Forall₂.cons head (List.Forall₂.cons ih List.Forall₂.nil)


/-- Concatenating pointwise related string literals preserves the result. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_vs_to_string_v_rel"]
theorem simpleValuesToString (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (values values' : List Value)
    (result : Flapjack.Basis.Pure.MlString.MlString)
    (related : List.Forall₂ relation values values')
    (run : valuesToString values = some result) :
    valuesToString values' = some result := by
  induction related generalizing result with
  | nil => simpa [valuesToString] using run
  | @cons value value' tail tail' valueRel tailRel ih =>
    cases value with
    | litv literal =>
      have shape := ((simple.2 _ _ (by simp [isClosure])).1 valueRel).1
      have eq : value' = .litv literal := by simpa [simpleBasicValRel] using shape
      subst value'
      cases literal with
      | strLit string =>
        cases tailRun : valuesToString tail with
        | none => simp [valuesToString, tailRun] at run
        | some rest =>
          have targetTail := ih rest tailRun
          simpa [valuesToString, tailRun, targetTail] using run
      | intLit _ | word8 _ | word64 _ | char _ | float64 _ => simp [valuesToString] at run
    | conv _ _ | loc _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ => simp [valuesToString] at run


/-- Simple relations preserve lists made solely from literal values.
This factors the inline HOL list-relation reasoning for byte and word decoders. -/
private theorem simpleLiteralMap_eq {α : Type} (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (literal : α → Flapjack.AstHOL.Lit)
    (items : List α) (target : List Value)
    (related : List.Forall₂ relation (items.map (Value.litv ∘ literal)) target) :
    target = items.map (Value.litv ∘ literal) := by
  induction items generalizing target with
  | nil => cases related; rfl
  | cons item rest ih =>
    simp only [List.map_cons, Function.comp_apply] at related ⊢
    cases related with
    | cons head tail =>
      have shape := ((simple.2 _ _ (by simp [isClosure])).1 head).1
      have eq := ih _ tail
      simp [simpleBasicValRel] at shape
      simp [shape, eq]

/-- Simple relations preserve successful byte-list decoding. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_val_rel_v_to_bytes"]
theorem simpleValueToBytes (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (left right : Value) (bytes : List (BitVec 8))
    (related : relation left right) (decoded : valueToBytes left = some bytes) :
    valueToBytes right = some bytes := by
  have source := (valueToBytes_eq_some left bytes).1 decoded
  obtain ⟨target, targetDecoded, targetRel⟩ :=
    simpleValueToList relation simple left right _ related source
  have equal := simpleLiteralMap_eq relation simple Flapjack.AstHOL.Lit.word8 bytes target targetRel
  apply (valueToBytes_eq_some right bytes).2
  simpa [equal] using targetDecoded

/-- Simple relations preserve successful 64-bit word-list decoding. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "simple_val_rel_v_to_words"]
theorem simpleValueToWords (relation : Value → Value → Prop)
    (simple : simpleValueRel relation) (left right : Value) (words : List (BitVec 64))
    (related : relation left right) (decoded : valueToWords left = some words) :
    valueToWords right = some words := by
  have source := (valueToWords_eq_some left words).1 decoded
  obtain ⟨target, targetDecoded, targetRel⟩ :=
    simpleValueToList relation simple left right _ related source
  have equal := simpleLiteralMap_eq relation simple Flapjack.AstHOL.Lit.word64 words target targetRel
  apply (valueToWords_eq_some right words).2
  simpa [equal] using targetDecoded

end Flapjack.Compiler.Backend.FlatProps
