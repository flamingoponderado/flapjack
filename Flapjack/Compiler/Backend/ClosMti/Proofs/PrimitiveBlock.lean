import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluatePrimitive

/-! Block inspection and Boolean operations for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Block tag and length tests preserve related values and errors. -/
theorem primitiveSimulation_block_tagLenEq {C F : Type} (tag length : Nat) :
    @PrimitiveSimulation C F (.blockOp (.tagLenEq tag length)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have lengths := fieldsRel.length_eq
        have boolRel := boolValue_related source.maxApp (actual == tag && fields.length == length)
        simp [doApp, applyBlock, ← lengths, boolRel, states]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyBlock, excRel]
    | cons head tail => simp [doApp, applyBlock, excRel]

/-- Block tag tests agree on related values. -/
theorem primitiveSimulation_block_tagEq {C F : Type} (tag : Nat) :
    @PrimitiveSimulation C F (.blockOp (.tagEq tag)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have boolRel := boolValue_related source.maxApp (actual == tag)
        simp [doApp, applyBlock, boolRel, states]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyBlock, excRel]
    | cons head tail => simp [doApp, applyBlock, excRel]

/-- Related blocks agree on length tests. -/
theorem primitiveSimulation_block_lenEq {C F : Type} (length : Nat) :
    @PrimitiveSimulation C F (.blockOp (.lenEq length)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have lengths := fieldsRel.length_eq
        have boolRel := boolValue_related source.maxApp (fields.length == length)
        simp [doApp, applyBlock, ← lengths, boolRel, states]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyBlock, excRel]
    | cons head tail => simp [doApp, applyBlock, excRel]

/-- Block length returns the same number for related blocks. -/
theorem primitiveSimulation_block_length {C F : Type} :
    @PrimitiveSimulation C F (.blockOp .lengthBlock) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have lengths := fieldsRel.length_eq
        have valueRel : ValueRel source.maxApp (.number fields.length) (.number fields.length) := .number _
        simp [doApp, applyBlock, ← lengths, valueRel, states]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyBlock, excRel]
    | cons head tail => simp [doApp, applyBlock, excRel]

/-- Block field lookup returns related values or fails on both sides. -/
theorem primitiveSimulation_block_elemAt {C F : Type} (index : Nat) :
    @PrimitiveSimulation C F (.blockOp (.elemAt index)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have lookupRel := forall₂_getElemRel fieldsRel index
        cases l : fields[index]? <;> cases r : nextFields[index]? <;>
          simp_all [optionRel, doApp, applyBlock, excRel]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
        simp [doApp, applyBlock, excRel]
    | cons head tail => simp [doApp, applyBlock, excRel]

/-- Boolean negation preserves the decoded Boolean or its type error. -/
theorem primitiveSimulation_block_boolNot {C F : Type} :
    @PrimitiveSimulation C F (.blockOp .boolNot) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have same := valueRel_asBool head
      cases observation : asBool value with
      | none =>
        have targetObservation : asBool nextValue = none := by rw [← same, observation]
        simp [doApp, applyBlock, observation, targetObservation, excRel]
      | some boolean =>
        have targetObservation : asBool nextValue = some boolean := by rw [← same, observation]
        have relatedBool := boolValue_related source.maxApp (!boolean)
        simp [doApp, applyBlock, observation, targetObservation, relatedBool, states]
    | cons head tail => simp [doApp, applyBlock, excRel]

/-- Boolean tests preserve both decoded inputs and their error cases. -/
theorem primitiveSimulation_block_boolTest {C F : Type} (test : AstHOL.Test) :
    @PrimitiveSimulation C F (.blockOp (.boolTest test)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyBlock, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        rename_i firstValue nextFirst secondValue nextSecond
        have sameFirst := valueRel_asBool first
        have sameSecond := valueRel_asBool second
        cases firstObs : asBool firstValue with
        | none => simp [doApp, applyBlock, ← sameFirst, firstObs, excRel]
        | some x =>
          cases secondObs : asBool secondValue with
          | none => simp [doApp, applyBlock, ← sameFirst, ← sameSecond, firstObs, secondObs, excRel]
          | some y =>
            have boolRel := boolValue_related source.maxApp (x == y)
            simp [doApp, applyBlock, ← sameFirst, ← sameSecond, firstObs, secondObs, boolRel, states]
      | cons head tail => simp [doApp, applyBlock, excRel]

/-- Block bounds checks agree on related blocks and numeric indices. -/
theorem primitiveSimulation_block_bounds {C F : Type} :
    @PrimitiveSimulation C F (.blockOp .boundsCheckBlock) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyBlock, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | block tag fields nextFields fieldsRel =>
          cases second with
          | number index =>
            have lengths := fieldsRel.length_eq
            simp [doApp, applyBlock, ← lengths, boolValue_related, states]
          | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
            simp [doApp, applyBlock, excRel]
        | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
          cases second <;> simp [doApp, applyBlock, excRel]
      | cons head tail => simp [doApp, applyBlock, excRel]

/-- Encoding related lists yields related closure-list values. -/
theorem listToValue_related (maxApp : Nat) {left right : List Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) :
    ValueRel maxApp (listToValue left) (listToValue right) := by
  apply (ClosProps.valueRel_listToValue (ValueRel maxApp) right (listToValue left)
    (simpleValRel maxApp)).mpr
  exact ⟨left, rfl, related⟩

/-- Closure constants produce values related to themselves. -/
theorem makeConst_related (maxApp : Nat) (constant : ClosLang.Const) :
    ValueRel maxApp (makeConst constant) (makeConst constant) := by
  cases constant with
  | constInt value => simpa [makeConst] using ValueRel.number (maxApp := maxApp) value
  | constWord64 value => simpa [makeConst] using ValueRel.word64 (maxApp := maxApp) value
  | constStr value => simpa [makeConst] using ValueRel.byteVector (maxApp := maxApp) value.explode
  | constCons tag constants =>
    simp only [makeConst]
    apply ValueRel.block
    have worker : ∀ xs : List ClosLang.Const, (∀ x ∈ xs, x ∈ constants) →
        List.Forall₂ (ValueRel maxApp) (xs.map makeConst) (xs.map makeConst) := by
      intro xs member
      induction xs with
      | nil => exact .nil
      | cons first rest ih =>
        apply List.Forall₂.cons
        · have contained : first ∈ constants := member first (by simp)
          exact makeConst_related maxApp first
        · apply ih
          intro x hx
          exact member x (by simp [hx])
    exact worker constants (by intro x hx; exact hx)
termination_by sizeOf constant
decreasing_by
  simp_wf
  have bound := List.sizeOf_lt_of_mem contained
  omega

/-- Decoding a closure list into a block preserves related fields. -/
theorem primitiveSimulation_block_fromList {C F : Type} (tag : Nat) :
    @PrimitiveSimulation C F (.blockOp (.fromList tag)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have decoded := ClosProps.valueToList_related (ValueRel source.maxApp)
        (simpleValRel source.maxApp) value nextValue head
      cases l : valueToList value <;> cases r : valueToList nextValue <;>
        simp_all [doApp, applyBlock, excRel]
      exact .block _ _ _ decoded
    | cons head tail => simp [doApp, applyBlock, excRel]

/-- Appending closure lists preserves their element relation. -/
theorem primitiveSimulation_block_listAppend {C F : Type} :
    @PrimitiveSimulation C F (.blockOp .listAppend) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyBlock, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        rename_i firstValue nextFirst secondValue nextSecond
        have firstRel := ClosProps.valueToList_related (ValueRel source.maxApp)
          (simpleValRel source.maxApp) firstValue nextFirst first
        have secondRel := ClosProps.valueToList_related (ValueRel source.maxApp)
          (simpleValRel source.maxApp) secondValue nextSecond second
        cases leftRun : valueToList firstValue <;> cases nextLeftRun : valueToList nextFirst <;>
          cases rightRun : valueToList secondValue <;> cases nextRightRun : valueToList nextSecond <;>
          simp_all [doApp, applyBlock, excRel]
        exact listToValue_related source.maxApp (List.rel_append firstRel secondRel)
      | cons head tail => simp [doApp, applyBlock, excRel]

/-- Structural equality agrees on related values, including closures. -/
theorem primitiveSimulation_block_equal {C F : Type} :
    @PrimitiveSimulation C F (.blockOp .equal) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyBlock, excRel]
    | cons second tail =>
      cases tail with
      | nil =>
        rename_i firstValue nextFirst secondValue nextSecond
        have same := (ClosProps.simpleValRel_doEq (ValueRel source.maxApp)
          (simpleValRel source.maxApp)).1 nextFirst nextSecond firstValue secondValue ⟨first, second⟩
        cases result : doEq firstValue secondValue with
        | typeError => simp [doApp, applyBlock, ← same, result, excRel]
        | val boolean =>
          have boolRel := boolValue_related source.maxApp boolean
          simp [doApp, applyBlock, ← same, result, boolRel, states]
      | cons head tail => simp [doApp, applyBlock, excRel]

/-- Constants preserve nested constructor values. -/
theorem primitiveSimulation_block_constant {C F : Type} (constant : ClosLang.Const) :
    @PrimitiveSimulation C F (.blockOp (.constant constant)) := by
  intro source target left right states values
  cases values with
  | nil =>
    have valueRel := makeConst_related source.maxApp constant
    simp [doApp, applyBlock, valueRel, states]
  | cons head tail => simp [doApp, applyBlock, excRel]

/-- Constant comparisons agree for related scalar operands. -/
theorem primitiveSimulation_block_equalConst {C F : Type} (constant : ClosLang.ConstPart) :
    @PrimitiveSimulation C F (.blockOp (.equalConst constant)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons head tail =>
    cases tail with
    | nil => cases constant <;> cases head <;> simp [doApp, applyBlock, excRel, boolValue_related, states]
    | cons head tail => simp [doApp, applyBlock, excRel]

/-- The closure dispatcher rejects build on both sides, as in the universal
source fallback replayed by the closure semantics probe. -/
theorem primitiveSimulation_block_build {C F : Type} (constants : List ClosLang.ConstPart) :
    @PrimitiveSimulation C F (.blockOp (.build constants)) := by
  intro source target left right states values
  simp [doApp_build_fallback, excRel]

/-- Block extension preserves the initial fields and selected related slice,
and rejects the same invalid sizes and bounds. -/
theorem primitiveSimulation_block_consExtend {C F : Type} (tag : Nat) :
    @PrimitiveSimulation C F (.blockOp (.consExtend tag)) := by
  intro source target left right states values
  cases values with
  | nil => simp [doApp, applyBlock, excRel]
  | cons first rest =>
    cases first with
    | block original fields nextFields fieldsRel =>
      cases rest with
      | nil => simp [doApp, applyBlock, excRel]
      | cons lowerRel rest =>
        cases lowerRel with
        | number lower =>
          cases rest with
          | nil => simp [doApp, applyBlock, excRel]
          | cons lenRel rest =>
            cases lenRel with
            | number len =>
              cases rest with
              | nil => simp [doApp, applyBlock, excRel]
              | cons totalRel initialRel =>
                cases totalRel with
                | number total =>
                  rename_i initial nextInitial
                  have fieldsLength := fieldsRel.length_eq
                  have initialLength := initialRel.length_eq
                  have sliceRel := List.forall₂_take len.toNat (List.forall₂_drop lower.toNat fieldsRel)
                  have resultRel := ValueRel.block tag _ _ (List.rel_append initialRel sliceRel)
                  by_cases invalid : lower < 0 ∨ len < 0 ∨ Int.ofNat fields.length < lower + len ∨
                      total = 0 ∨ total ≠ Int.ofNat initial.length + len
                  · simp only [doApp, applyBlock, ← fieldsLength, ← initialLength]
                    rw [ite_eq_left invalid, ite_eq_left invalid]
                    exact ⟨_, rfl, rfl⟩
                  · simp only [doApp, applyBlock, ← fieldsLength, ← initialLength]
                    rw [ite_eq_right invalid, ite_eq_right invalid]
                    exact ⟨_, _, resultRel, states, rfl⟩
                | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
                  simp [doApp, applyBlock, excRel]
            | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
              cases rest <;> simp [doApp, applyBlock, excRel]
        | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
          cases rest <;> simp [doApp, applyBlock, excRel]
    | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure | partialRecclosure =>
      cases rest <;> simp [doApp, applyBlock, excRel]

/-- Every case of the proof-side block dispatcher preserves the relation.
The dispatcher and evaluator remain subject to source correspondence review. -/
theorem primitiveSimulation_block {C F : Type} (op : ClosLang.BlockOp) :
    @PrimitiveSimulation C F (.blockOp op) := by
  cases op with
  | cons tag => exact primitiveSimulation_block_cons tag
  | elemAt index => exact primitiveSimulation_block_elemAt index
  | tagLenEq tag length => exact primitiveSimulation_block_tagLenEq tag length
  | lenEq length => exact primitiveSimulation_block_lenEq length
  | tagEq tag => exact primitiveSimulation_block_tagEq tag
  | lengthBlock => exact primitiveSimulation_block_length
  | boolTest test => exact primitiveSimulation_block_boolTest test
  | boolNot => exact primitiveSimulation_block_boolNot
  | boundsCheckBlock => exact primitiveSimulation_block_bounds
  | consExtend tag => exact primitiveSimulation_block_consExtend tag
  | fromList tag => exact primitiveSimulation_block_fromList tag
  | listAppend => exact primitiveSimulation_block_listAppend
  | constant constant => exact primitiveSimulation_block_constant constant
  | equal => exact primitiveSimulation_block_equal
  | equalConst constant => exact primitiveSimulation_block_equalConst constant
  | build constants => exact primitiveSimulation_block_build constants

end Flapjack.Compiler.Backend.ClosMti
