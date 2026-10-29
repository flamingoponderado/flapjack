import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveMemory
import Flapjack.Compiler.Backend.FlatPattern.Proofs.MatchBranch

/-! Array primitive simulations for the proof-side flat pattern relations.
The evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result StoreValue storeLookup storeAssign)
open Flapjack.SemanticPrimitivesProps (storeValueRel)

/-- The single-value counterpart of the proof-side expression result relation. -/
inductive PrimitiveResultRel : Result FlatSem.Value FlatSem.Value → Result FlatSem.Value FlatSem.Value → Prop where
  | value {left right} : ValueRel left right → PrimitiveResultRel (.val left) (.val right)
  | error {left right} : FlatErrorRel left right → PrimitiveResultRel (.err left) (.err right)

/-- A missing position is missing from both related lists. -/
theorem forall₂_getElem_none {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) (index : Nat) (absent : xs[index]? = none) : ys[index]? = none := by
  induction related generalizing index with
  | nil => simp
  | cons _ _ ih =>
    cases index with
    | zero => simp at absent
    | succ index =>
      simp only [List.getElem?_cons_succ] at absent ⊢
      exact ih index absent

/-- Replacing related elements at the same position preserves the list relation. -/
theorem forall₂_set {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) (index : Nat) {x : A} {y : B} (values : R x y) :
    List.Forall₂ R (xs.set index x) (ys.set index y) := by
  induction related generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simpa using List.Forall₂.cons values tail
    | succ index => simpa using List.Forall₂.cons head (ih index)

/-- Repeating related values yields related lists. -/
theorem forall₂_replicate {A B : Type} {R : A → B → Prop} (count : Nat) {x : A} {y : B}
    (related : R x y) : List.Forall₂ R (List.replicate count x) (List.replicate count y) := by
  induction count with
  | zero => exact .nil
  | succ _ ih => exact .cons related ih

/-- The bounds exception is related to itself. -/
theorem subscriptExn_related : ValueRel FlatSem.subscriptExnV FlatSem.subscriptExnV := by
  exact (valueRel_conv _ [] _).2 ⟨[], rfl, .nil⟩

/-- Indexed reads preserve returned values and bounds exceptions for related
lists; unsafe out-of-bounds reads remain absent on both sides. -/
theorem readIndexed_related {C F : Type} (source target : FlatSem.State C F) (unsafeOp : Bool)
    (items items' : List FlatSem.Value) (index : Int)
    (related : List.Forall₂ ValueRel items items') (result : Result FlatSem.Value FlatSem.Value)
    (run : FlatSem.readIndexed source unsafeOp items index id = some (source, result)) :
    ∃ result', FlatSem.readIndexed target unsafeOp items' index id = some (target, result') ∧
      PrimitiveResultRel result result' := by
  by_cases negative : index < 0
  · cases unsafeOp with
    | true => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at run
    | false =>
      simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative] at run
      subst result
      exact ⟨_, by simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative], .error (.raise subscriptExn_related)⟩
  · cases found : items[index.toNat]? with
    | none =>
      have absent := forall₂_getElem_none related index.toNat found
      cases unsafeOp with
      | true => simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, found] at run
      | false =>
        simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, found] at run
        subst result
        exact ⟨_, by simp [FlatSem.readIndexed, FlatSem.boundsFailure, negative, absent], .error (.raise subscriptExn_related)⟩
    | some value =>
      obtain ⟨value', found', valueRel⟩ := forall₂_getElem_some related index.toNat value found
      simp [FlatSem.readIndexed, negative, found] at run
      subst result
      exact ⟨_, by simp [FlatSem.readIndexed, negative, found'], .value valueRel⟩

/-- The array entry found in a related store contains a pointwise related array. -/
theorem stateRel_lookup_array {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (states : StateRel cfg source target) (address : Nat) (items : List FlatSem.Value)
    (found : storeLookup address source.refs = some (.varray items)) :
    ∃ items', storeLookup address target.refs = some (.varray items') ∧ List.Forall₂ ValueRel items items' := by
  obtain ⟨entry, lookup, relation⟩ := storeValueRel_lookup states.2.1 address (.varray items) found
  cases entry <;> simp [storeValueRel] at relation
  case varray items' => exact ⟨items', lookup, relation⟩

/-- Array length is unchanged by pointwise value relatedness. -/
theorem doApp_arrayLength_related {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (flag : Bool) (address : Nat) (items : List FlatSem.Value)
    (states : StateRel cfg source target) (found : storeLookup address source.refs = some (.varray items)) :
    ∃ result, FlatSem.doApp source (.src .alength) [.loc flag address] = some (source, .val result) ∧
      FlatSem.doApp target (.src .alength) [.loc flag address] = some (target, .val result) ∧ ValueRel result result := by
  obtain ⟨items', found', related⟩ := stateRel_lookup_array cfg source target states address items found
  have lengths := forall₂_length related
  refine ⟨.litv (.intLit items.length), ?_, ?_, (valueRel_lit _ _).2 rfl⟩
  · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found]
  · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found', ← lengths]

/-- Allocating an array with related fill values preserves both the allocated
address and the negative-size bounds exception. -/
theorem doApp_arrayAlloc_related {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (size : Int) (value value' : FlatSem.Value) (states : StateRel cfg source target)
    (values : ValueRel value value') :
    ∃ sourceFinal targetFinal result result',
      FlatSem.doApp source (.src .aalloc) [.litv (.intLit size), value] = some (sourceFinal, result) ∧
      FlatSem.doApp target (.src .aalloc) [.litv (.intLit size), value'] = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  by_cases negative : size < 0
  · refine ⟨source, target, .err (.raise FlatSem.subscriptExnV), .err (.raise FlatSem.subscriptExnV), ?_, ?_,
      states, .error (.raise subscriptExn_related)⟩
    · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.boundsFailure, negative]
    · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, FlatSem.boundsFailure, negative]
  · have lengths : target.refs.length = source.refs.length := (forall₂_length states.2.1).symm
    refine ⟨{ source with refs := source.refs ++ [.varray (List.replicate size.toNat value)] },
      { target with refs := target.refs ++ [.varray (List.replicate size.toNat value')] },
      .val (.loc true source.refs.length), .val (.loc true source.refs.length), ?_, ?_, ?_, .value ?_⟩
    · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, Flapjack.SemanticPrimitivesHOL.storeAlloc, negative]
    · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, Flapjack.SemanticPrimitivesHOL.storeAlloc, negative, lengths]
    · exact ⟨states.1, forall₂_append_one states.2.1 (forall₂_replicate size.toNat values), states.2.2⟩
    · exact (valueRel_loc true source.refs.length _).2 rfl

/-- Array reads preserve both ordinary results and bounds exceptions. -/
theorem doApp_arrayRead_related {C F : Type} (cfg : Config) (source target : FlatSem.State C F)
    (unsafeOp : Bool) (flag : Bool) (address : Nat) (index : Int) (items : List FlatSem.Value)
    (result : Result FlatSem.Value FlatSem.Value) (states : StateRel cfg source target)
    (found : storeLookup address source.refs = some (.varray items))
    (run : FlatSem.doApp source (.src (if unsafeOp then .asubUnsafe else .asub))
      [.loc flag address, .litv (.intLit index)] = some (source, result)) :
    ∃ result', FlatSem.doApp target (.src (if unsafeOp then .asubUnsafe else .asub))
      [.loc flag address, .litv (.intLit index)] = some (target, result') ∧ PrimitiveResultRel result result' := by
  obtain ⟨items', found', related⟩ := stateRel_lookup_array cfg source target states address items found
  have unequal : (Op.asub == Op.asubUnsafe) = false := by decide
  have read : FlatSem.readIndexed source unsafeOp items index id = some (source, result) := by
    cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found, unequal] using run
  obtain ⟨result', read', results⟩ := readIndexed_related source target unsafeOp items items' index related result read
  refine ⟨result', ?_, results⟩
  cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found', unequal] using read'

/-- Indexed updates preserve stores, values and bounds exceptions. -/
theorem updateIndexed_array_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (unsafeOp : Bool) (address : Nat) (items items' : List FlatSem.Value) (index : Int)
    (value value' : FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (itemsRel : List.Forall₂ ValueRel items items')
    (values : ValueRel value value')
    (run : FlatSem.updateIndexed source unsafeOp address items index value .varray = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.updateIndexed target unsafeOp address items' index value' .varray =
      some (targetFinal, result') ∧ StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  have lengths : items'.length = items.length := (forall₂_length itemsRel).symm
  by_cases bounds : index < 0 ∨ items.length ≤ index.toNat
  · have bounds' : index < 0 ∨ items'.length ≤ index.toNat := by simpa [lengths] using bounds
    cases unsafeOp with
    | true => simp [FlatSem.updateIndexed, FlatSem.boundsFailure, bounds] at run
    | false =>
      simp [FlatSem.updateIndexed, FlatSem.boundsFailure, bounds] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨target, .err (.raise FlatSem.subscriptExnV), ?_, states, .error (.raise subscriptExn_related)⟩
      simp [FlatSem.updateIndexed, FlatSem.boundsFailure, bounds']
  · have bounds' : ¬ (index < 0 ∨ items'.length ≤ index.toNat) := by simpa [lengths] using bounds
    cases assigned : storeAssign address (.varray (items.set index.toNat value)) source.refs with
    | none => simp [FlatSem.updateIndexed, bounds, assigned] at run
    | some refs =>
      have entries : storeValueRel ValueRel (.varray (items.set index.toNat value))
          (.varray (items'.set index.toNat value')) := forall₂_set itemsRel index.toNat values
      obtain ⟨refs', assigned', refsRel⟩ := storeAssign_related states.2.1 address entries assigned
      simp [FlatSem.updateIndexed, bounds, assigned] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ target with refs := refs' }, .val FlatSem.unitValue, ?_, ?_, .value ?_⟩
      · simp [FlatSem.updateIndexed, bounds', assigned']
      · exact ⟨states.1, refsRel, states.2.2⟩
      · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩

/-- Array updates preserve their result and state through the primitive
dispatcher, for both checked and unsafe operations. -/
theorem doApp_arrayUpdate_related {C F : Type} (cfg : Config) (source target sourceFinal : FlatSem.State C F)
    (unsafeOp : Bool) (flag : Bool) (address : Nat) (index : Int) (items : List FlatSem.Value)
    (value value' : FlatSem.Value) (result : Result FlatSem.Value FlatSem.Value)
    (states : StateRel cfg source target) (values : ValueRel value value')
    (found : storeLookup address source.refs = some (.varray items))
    (run : FlatSem.doApp source (.src (if unsafeOp then .aupdateUnsafe else .aupdate))
      [.loc flag address, .litv (.intLit index), value] = some (sourceFinal, result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src (if unsafeOp then .aupdateUnsafe else .aupdate))
      [.loc flag address, .litv (.intLit index), value'] = some (targetFinal, result') ∧
      StateRel cfg sourceFinal targetFinal ∧ PrimitiveResultRel result result' := by
  obtain ⟨items', found', related⟩ := stateRel_lookup_array cfg source target states address items found
  have unequal : (Op.aupdate == Op.aupdateUnsafe) = false := by decide
  have update : FlatSem.updateIndexed source unsafeOp address items index value .varray = some (sourceFinal, result) := by
    cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found, unequal] using run
  obtain ⟨targetFinal, result', update', finalStates, results⟩ :=
    updateIndexed_array_related cfg source target sourceFinal unsafeOp address items items' index value value' result
      states related values update
  refine ⟨targetFinal, result', ?_, finalStates, results⟩
  cases unsafeOp <;> simpa [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, found', unequal] using update'

end Flapjack.Compiler.Backend.FlatPattern
