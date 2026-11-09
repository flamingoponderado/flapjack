module

public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

@[expose] public section

/-! Code label primitive simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- A BVI code label can be read from the compiled data code tree. This
factored case is untagged pending review of the complete primitive theorem. -/
theorem doApp_label {C F : Type} (label : Nat) (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp (.label label) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.doAppAux (.label label) args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases args with
  | cons a rest => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | nil =>
    cases lookup : sptLookup label source.code with
    | none => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, lookup] at run
    | some entry =>
      obtain ⟨argc, exp⟩ := entry
      have targetLookup : sptLookup label target.code = some (argc, compileExp argc exp) :=
        related.2.1.2.2.2 label exp argc lookup
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, lookup] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨target, .codePtr label, ?_, ?_, related⟩
      · simp [DataSem.doAppAux, DataSem.applyNonFfi, targetLookup]
      · simp [dataToBviValue]

end
end Flapjack.Compiler.Backend.BviToData
