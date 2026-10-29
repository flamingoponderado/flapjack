import Flapjack.Compiler.Backend.FlatPattern.Proofs.ThunkRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

/-! Reference operations for the flat pattern compiler. These results use
the proof-side evaluator and relations, which remain pending HOL review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result storeAlloc storeAssign)
open Flapjack.SemanticPrimitivesProps (storeValueRel)

/-- Pointwise related lists have equal lengths. -/
theorem forall₂_length {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Appending a pair of related entries preserves a pointwise relation. -/
theorem forall₂_append_one {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) {x : A} {y : B} (head : R x y) :
    List.Forall₂ R (xs ++ [x]) (ys ++ [y]) := by
  induction related with
  | nil => exact .cons head .nil
  | cons first _ ih => exact .cons first ih

/-- Indexing a related list at a valid position finds a related element. -/
theorem forall₂_getElem_some {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) (index : Nat) (x : A) (found : xs[index]? = some x) :
    ∃ y, ys[index]? = some y ∧ R x y := by
  induction related generalizing index with
  | nil => simp at found
  | @cons first second xs ys head tail ih =>
    cases index with
    | zero =>
      simp at found
      subst x
      exact ⟨second, rfl, head⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found ⊢
      exact ih index found

/-- Allocating a reference to related values produces related stores and the
same location. -/
theorem doApp_refAlloc_related {C F : Type} (cfg : Config)
    (source target : FlatSem.State C F) (values values' : List FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (sourceFinal : FlatSem.State C F) (result : FlatSem.Value)
    (run : FlatSem.doApp source (.src .opref) values = some (sourceFinal, .val result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .opref) values' = some (targetFinal, .val result') ∧
      StateRel cfg sourceFinal targetFinal ∧ ValueRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons value value' tail tail' head rest =>
    cases rest with
    | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | nil =>
      simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc] at run
      rcases run with ⟨rfl, rfl⟩
      have lengths : target.refs.length = source.refs.length := (forall₂_length states.2.1).symm
      refine ⟨{ target with refs := target.refs ++ [.refv value'] }, .loc true target.refs.length, ?_, ?_, ?_⟩
      · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc]
      · exact ⟨states.1, forall₂_append_one states.2.1 head, states.2.2⟩
      · exact (valueRel_loc true source.refs.length _).2 (by simp [lengths])

/-- A successful reference assignment preserves related stores and returns
related unit values. -/
theorem doApp_refAssign_related {C F : Type} (cfg : Config)
    (source target : FlatSem.State C F) (values values' : List FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values')
    (sourceFinal : FlatSem.State C F) (result : FlatSem.Value)
    (run : FlatSem.doApp source (.src .opassign) values = some (sourceFinal, .val result)) :
    ∃ targetFinal result', FlatSem.doApp target (.src .opassign) values' = some (targetFinal, .val result') ∧
      StateRel cfg sourceFinal targetFinal ∧ ValueRel result result' := by
  cases related with
  | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
  | @cons loc loc' tail tail' locRel rest =>
    cases rest with
    | nil => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
    | @cons value value' tail tail' valueRel rest =>
      cases rest with
      | cons _ _ => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run
      | nil =>
        cases loc with
        | loc flag index =>
          have eq := (valueRel_loc flag index loc').1 locRel
          subst loc'
          cases assigned : storeAssign index (.refv value) source.refs with
          | none => simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, assigned] at run
          | some refs =>
            have assigned' := storeAssign_related states.2.1 index (show storeValueRel ValueRel (.refv value) (.refv value') from valueRel) assigned
            obtain ⟨refs', assignTarget, refsRel⟩ := assigned'
            simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, assigned] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ target with refs := refs' }, FlatSem.unitValue, ?_, ?_, ?_⟩
            · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, assignTarget]
            · exact ⟨states.1, refsRel, states.2.2⟩
            · exact (valueRel_conv none [] _).2 ⟨[], rfl, .nil⟩
        | litv _ | conv _ _ | vectorv _ | closure _ _ _ | recclosure _ _ _ =>
          simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory] at run

/-- Fixed-size array allocation stores the related argument lists and returns
the same newly allocated location. -/
theorem doApp_arrayFixed_related {C F : Type} (cfg : Config)
    (source target : FlatSem.State C F) (values values' : List FlatSem.Value)
    (states : StateRel cfg source target) (related : List.Forall₂ ValueRel values values') :
    ∃ sourceFinal targetFinal result,
      FlatSem.doApp source (.src .aallocFixed) values = some (sourceFinal, .val result) ∧
      FlatSem.doApp target (.src .aallocFixed) values' = some (targetFinal, .val result) ∧
      StateRel cfg sourceFinal targetFinal ∧ ValueRel result result := by
  have lengths : target.refs.length = source.refs.length := (forall₂_length states.2.1).symm
  refine ⟨{ source with refs := source.refs ++ [.varray values] },
    { target with refs := target.refs ++ [.varray values'] }, .loc true source.refs.length, ?_, ?_, ?_, ?_⟩
  · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc]
  · simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory, storeAlloc, lengths]
  · exact ⟨states.1, forall₂_append_one states.2.1 related, states.2.2⟩
  · exact (valueRel_loc true source.refs.length _).2 rfl

/-- Reading a reference through flat's zero-index projection preserves its
contained value when the source read succeeds. -/
theorem doApp_refRead_related {C F : Type} (cfg : Config)
    (source target : FlatSem.State C F) (flag : Bool) (index : Nat) (value : FlatSem.Value)
    (states : StateRel cfg source target)
    (run : FlatSem.doApp source (.el 0) [.loc flag index] = some (source, .val value)) :
    ∃ value', FlatSem.doApp target (.el 0) [.loc flag index] = some (target, .val value') ∧ ValueRel value value' := by
  cases found : Flapjack.SemanticPrimitivesHOL.storeLookup index source.refs with
  | none => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
  | some entry =>
    cases entry with
    | refv stored =>
      simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
      subst value
      obtain ⟨value', found', related⟩ := stateRel_lookup_ref cfg source target states index stored found
      exact ⟨value', by simp [FlatSem.doApp, FlatSem.doAppFlat, found'], related⟩
    | w8array _ | varray _ | thunk _ _ => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run

/-- Projection from related constructor values returns related fields. -/
theorem doApp_constructorRead_related {C F : Type} (state target : FlatSem.State C F)
    (index : Nat) (tag : Option (FlatLang.CtorId × FlatLang.TypeId))
    (fields fields' : List FlatSem.Value) (value : FlatSem.Value)
    (related : List.Forall₂ ValueRel fields fields')
    (run : FlatSem.doApp state (.el index) [.conv tag fields] = some (state, .val value)) :
    ∃ value', FlatSem.doApp target (.el index) [.conv tag fields'] = some (target, .val value') ∧ ValueRel value value' := by
  cases found : fields[index]? with
  | none => simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
  | some field =>
    simp [FlatSem.doApp, FlatSem.doAppFlat, found] at run
    subst value
    obtain ⟨field', found', fieldRel⟩ := forall₂_getElem_some related index field found
    exact ⟨field', by simp [FlatSem.doApp, FlatSem.doAppFlat, found'], fieldRel⟩

end Flapjack.Compiler.Backend.FlatPattern
