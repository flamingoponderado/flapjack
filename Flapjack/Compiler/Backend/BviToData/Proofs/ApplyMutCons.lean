module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Build
public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
public import Flapjack.Misc.Sptree.Map

@[expose] public section

/-! Mutable-constructor primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Mutable constructor allocation uses the same fresh address and retains
the projected prefix, selected child, and suffix. This factored case is
untagged pending review of the complete primitive theorem. -/
theorem doApp_mutCons {C F : Type} (tag index : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp (.mutCons tag index)) (args.map dataToBviValue) source =
      .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp (.mutCons tag index)) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  have refs : ∀ n, source.refs.lookup n = (sptLookup n target.refs).map dataToBviRef := by
    intro n
    rw [← sptLookup_sptMap]
    exact related.2.2.2.2.1 n
  have fresh := leastUnusedRef_projection target.refs source.refs refs
  cases slot : args[index]? with
  | none =>
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, List.getElem?_map, slot] at run
  | some child =>
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, List.getElem?_map, slot, fresh] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨{ target with refs := sptInsert (DataSem.leastUnusedRef target.refs) (.mutBlock tag false (args.take index) child (args.drop (index + 1))) target.refs },
      .refPtr false (DataSem.leastUnusedRef target.refs), ?_, ?_, ?_⟩
    · simp [DataSem.doAppAux, DataSem.applyNonFfi, slot]
    · simp [dataToBviValue]
    · simpa [dataToBviRef, List.map_take, List.map_drop] using
        stateRel_insertRef source target related (DataSem.leastUnusedRef target.refs)
          (.mutBlock tag false (args.take index) child (args.drop (index + 1)))

/-- Updating the open slot of a mutable constructor preserves its reference
projection and leaves all other store entries related. This factored case is
untagged pending review of the complete primitive theorem. -/
theorem doApp_updateCons {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.memOp .updateCons) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.memOp .updateCons) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
    | cons b rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
      | cons value rest =>
        cases rest with
        | cons c rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
        | nil =>
          cases a with
          | number n => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
          | refPtr bit ptr =>
            cases b with
            | word64 w => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
            | codePtr p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
            | refPtr bit p => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
            | block ts tag vs => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
            | number index =>
              have refs : source.refs.lookup ptr = (sptLookup ptr target.refs).map dataToBviRef := by
                rw [← sptLookup_sptMap]
                exact related.2.2.2.2.1 ptr
              cases found : sptLookup ptr target.refs with
              | none => simp [dataToBviValue, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, refs, found] at run
              | some entry =>
                cases entry with
                | byteArray flag bytes => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, refs, found] at run
                | valueArray values => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, refs, found] at run
                | thunk mode body => simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, refs, found] at run
                | mutBlock tag finalised left old right =>
                  cases finalised with
                  | true =>
                    simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, refs, found] at run
                  | false =>
                    by_cases indexEq : index = Int.ofNat left.length
                    · subst index
                      simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, refs, found] at run
                      rcases run with ⟨rfl, rfl⟩
                      refine ⟨{ target with refs := sptInsert ptr (.mutBlock tag false left value right) target.refs },
                        DataSem.unitValue, ?_, dataToBviValue_unit.symm, ?_⟩
                      · simp [DataSem.doAppAux, DataSem.applyNonFfi, found]
                      · simpa [dataToBviRef] using stateRel_insertRef source target related ptr (.mutBlock tag false left value right)
                    · have indexNe : index ≠ (↑left.length : Int) := by exact indexEq
                      simp [dataToBviValue, dataToBviRef, BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, refs, found, indexNe] at run

end
end Flapjack.Compiler.Backend.BviToData
