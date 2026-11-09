module

public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
public import Flapjack.Misc.Sptree.Map

@[expose] public section

/-! Global pointer primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Reading the global pointer preserves the related states. This factored
case is untagged pending review of the complete primitive theorem. -/
theorem doApp_globalsPtr {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.globOp .globalsPtr) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.globOp .globalsPtr) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    cases ptr : source.global with
    | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, ptr] at run
    | some n =>
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, ptr] at run
      rcases run with ⟨rfl, rfl⟩
      have targetPtr : target.global = some n := by rw [← related.2.2.2.2.2.2]; exact ptr
      refine ⟨target, .refPtr true n, ?_, ?_, related⟩
      · simp [DataSem.doAppAux, DataSem.applyNonFfi, targetPtr]
      · simp [dataToBviValue]

/-- Updating the global pointer preserves the related states. This factored
case is untagged pending review of the complete primitive theorem. -/
theorem doApp_setGlobalsPtr {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.globOp .setGlobalsPtr) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.globOp .setGlobalsPtr) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | nil =>
      cases arg with
      | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | codePtr n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
      | refPtr bit ptr =>
        cases bit with
        | false => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
        | true =>
          simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ target with global := some ptr }, DataSem.unitValue, ?_, ?_, ?_⟩
          · simp [DataSem.doAppAux, DataSem.applyNonFfi]
          · exact dataToBviValue_unit.symm
          · rcases related with ⟨clock, code, oracle, compiler, refs, ffi, _⟩
            exact ⟨clock, code, oracle, compiler, refs, ffi, rfl⟩

/-- A global read returns the projection of the same data value, including
reference and index failure cases. This factored simulation remains untagged
pending review of the complete primitive theorem. -/
theorem doApp_global {C F : Type} (index : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.globOp (.global index)) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.globOp (.global index)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    cases global : target.global with
    | none =>
      have sourceGlobal : source.global = none := related.2.2.2.2.2.2.trans global
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal] at run
    | some ptr =>
      have sourceGlobal : source.global = some ptr := related.2.2.2.2.2.2.trans global
      have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
        rw [← sptLookup_sptMap]
        exact related.2.2.2.2.1 ptr
      cases found : sptLookup ptr target.refs with
      | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found] at run
      | some entry =>
        cases entry with
        | byteArray flag bytes =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found, dataToBviRef] at run
        | thunk mode value =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found, dataToBviRef] at run
        | mutBlock tag finalised left child right =>
          simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found, dataToBviRef] at run
        | valueArray values =>
          cases slot : values[index]? with
          | none =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found,
              dataToBviRef, List.getElem?_map, slot] at run
          | some value =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found,
              dataToBviRef, List.getElem?_map, slot] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨target, value, ?_, rfl, related⟩
            simp [DataSem.doAppAux, DataSem.applyNonFfi, global, found, slot]

/-- Updating a global array element preserves the projection of every
reference-store lookup. This factored case is untagged pending review of the
complete primitive theorem. -/
theorem doApp_setGlobal {C F : Type} (index : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.globOp (.setGlobal index)) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.globOp (.setGlobal index)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | cons arg rest =>
    cases rest with
    | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | nil =>
      cases global : target.global with
      | none =>
        have sourceGlobal : source.global = none := related.2.2.2.2.2.2.trans global
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal] at run
      | some ptr =>
        have sourceGlobal : source.global = some ptr := related.2.2.2.2.2.2.trans global
        have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
          rw [← sptLookup_sptMap]
          exact related.2.2.2.2.1 ptr
        cases found : sptLookup ptr target.refs with
        | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found] at run
        | some entry =>
          cases entry with
          | byteArray flag bytes =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found, dataToBviRef] at run
          | thunk mode value =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found, dataToBviRef] at run
          | mutBlock tag finalised left child right =>
            simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found, dataToBviRef] at run
          | valueArray values =>
            by_cases bound : index < values.length
            · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found,
                dataToBviRef, bound] at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨{ target with refs := sptInsert ptr (.valueArray (values.set index arg)) target.refs },
                DataSem.unitValue, ?_, dataToBviValue_unit.symm, ?_⟩
              · simp [DataSem.doAppAux, DataSem.applyNonFfi, global, found, bound]
              · rcases related with ⟨clock, code, oracle, compiler, oldRefs, ffi, _⟩
                refine ⟨clock, code, oracle, compiler, ?_, ffi, global.symm⟩
                intro key
                rw [HolFiniteMapExact.lookup_updateEq, sptLookup_sptMap]
                by_cases same : key = ptr
                · subst key
                  simp [FUPDATE_HOL, sptLookup_sptInsert_same, dataToBviRef, List.map_set]
                · rw [sptLookup_sptInsert_ne ptr key _ _ same]
                  simp [FUPDATE_HOL, same, ← sptLookup_sptMap, oldRefs]
            · simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, sourceGlobal, refs, found,
                dataToBviRef, bound] at run

end
end Flapjack.Compiler.Backend.BviToData
