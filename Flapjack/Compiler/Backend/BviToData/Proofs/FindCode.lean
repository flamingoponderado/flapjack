module

public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Call
public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Code lookup simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack
open Classical
noncomputable section

/-- A successful direct BVI code lookup finds the compiled data body with the
same projected arguments. This is the direct case of the local source lemma. -/
theorem findCode_direct {C F : Type} (source : BviSem.BviState C F) (target : DataSem.State C F)
    (label : Nat) (values : List DataSem.Value) (args : List BvlSem.Value) (body : Bvi.Exp)
    (related : stateRel source target)
    (found : BvlSem.findCode (some label) (values.map dataToBviValue) source.code = some (args, body)) :
    ∃ dataArgs size, args = dataArgs.map dataToBviValue ∧
      DataSem.findCode (some label) values target.code target.stackFrameSizes =
        some (dataArgs, compileExp dataArgs.length body, size) := by
  cases lookup : sptLookup label source.code with
  | none => simp [BvlSem.findCode, lookup] at found
  | some pair =>
    obtain ⟨arity, expression⟩ := pair
    by_cases length : values.length = arity
    · simp [BvlSem.findCode, lookup, length] at found
      rcases found with ⟨rfl, rfl⟩
      have targetLookup := related.2.1.2.2.2 label expression arity lookup
      refine ⟨values, sptLookup label target.stackFrameSizes, rfl, ?_⟩
      simp [DataSem.findCode, targetLookup, length]
    · simp [BvlSem.findCode, lookup, length] at found

private theorem project_holLast (head : DataSem.Value) (tail : List DataSem.Value) :
    holLast ((head :: tail).map dataToBviValue) = dataToBviValue (holLast (head :: tail)) := by
  induction tail generalizing head with
  | nil => simp [holLast]
  | cons next rest ih => simpa [holLast] using ih next

/-- A successful indirect code lookup removes the same final code pointer and
finds its compiled body. This is the indirect case of the local source lemma. -/
theorem findCode_indirect {C F : Type} (source : BviSem.BviState C F) (target : DataSem.State C F)
    (values : List DataSem.Value) (args : List BvlSem.Value) (body : Bvi.Exp)
    (related : stateRel source target)
    (found : BvlSem.findCode none (values.map dataToBviValue) source.code = some (args, body)) :
    ∃ dataArgs size, args = dataArgs.map dataToBviValue ∧
      DataSem.findCode none values target.code target.stackFrameSizes =
        some (dataArgs, compileExp dataArgs.length body, size) := by
  cases values with
  | nil => simp [BvlSem.findCode] at found
  | cons head tail =>
    have lastProjection : holLast (dataToBviValue head :: tail.map dataToBviValue) =
        dataToBviValue (holLast (head :: tail)) := by
      simpa only [List.map_cons] using project_holLast head tail
    cases last : holLast (head :: tail) with
    | number n => simp [BvlSem.findCode, lastProjection, last, dataToBviValue] at found
    | word64 w => simp [BvlSem.findCode, lastProjection, last, dataToBviValue] at found
    | refPtr bit ptr => simp [BvlSem.findCode, lastProjection, last, dataToBviValue] at found
    | block ts tag fields => simp [BvlSem.findCode, lastProjection, last, dataToBviValue] at found
    | codePtr label =>
      cases lookup : sptLookup label source.code with
      | none => simp [BvlSem.findCode, lastProjection, last, dataToBviValue, lookup] at found
      | some pair =>
        obtain ⟨arity, expression⟩ := pair
        by_cases length : tail.length = arity
        · simp [BvlSem.findCode, lastProjection, last, dataToBviValue, lookup, length] at found
          rcases found with ⟨rfl, rfl⟩
          have targetLookup := related.2.1.2.2.2 label expression arity lookup
          have argsLength : (head :: tail).dropLast.length = arity := by
            simp [List.length_dropLast, length]
          refine ⟨(head :: tail).dropLast, sptLookup label target.stackFrameSizes, ?_, ?_⟩
          · simp [List.map_dropLast]
          · simp [DataSem.findCode, last, targetLookup, length, argsLength]
        · simp [BvlSem.findCode, lastProjection, last, dataToBviValue, lookup, length] at found

/-- Successful BVI code lookup, direct or indirect, has the corresponding data
lookup and compiled body. This remains untagged pending review of the complete
source statement and state carriers. -/
theorem findCode_projection {C F : Type} (dest : Option Nat) (values : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F) (args : List BvlSem.Value) (body : Bvi.Exp)
    (related : stateRel source target)
    (found : BvlSem.findCode dest (values.map dataToBviValue) source.code = some (args, body)) :
    ∃ dataArgs size, args = dataArgs.map dataToBviValue ∧
      DataSem.findCode dest values target.code target.stackFrameSizes =
        some (dataArgs, compileExp dataArgs.length body, size) := by
  cases dest with
  | none => exact findCode_indirect source target values args body related found
  | some label => exact findCode_direct source target label values args body related found

end
end Flapjack.Compiler.Backend.BviToData
