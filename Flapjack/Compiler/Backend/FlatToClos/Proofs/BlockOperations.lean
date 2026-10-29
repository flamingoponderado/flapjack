import Flapjack.Compiler.Backend.FlatToClos.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyFlat
import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic

/-! Block primitive cases for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos

/-- The two semantic Boolean representations are related. -/
theorem boolValue_related (value : Bool) : ValueRel (FlatSem.boolValue value) (ClosSem.boolValue value) := by
  cases value <;> exact .con .nil

private theorem related_lengths {source : List FlatSem.Value} {target : List ClosSem.Value}
    (related : List.Forall₂ ValueRel source target) : source.length = target.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Constructor tag-and-length checks produce related Boolean results. -/
theorem tagLenEq_related {C F : Type} (sourceState : FlatSem.State C F) (targetState : ClosSem.State C F)
    (expected length actual : Nat) (typeId : FlatLang.TypeId)
    (source : List FlatSem.Value) (target : List ClosSem.Value) (related : List.Forall₂ ValueRel source target) :
    ∃ flatResult closResult,
      FlatSem.doAppFlat sourceState (.tagLenEq expected length) [.conv (some (actual, typeId)) source] =
        some (some (sourceState, .val flatResult)) ∧
      ClosSem.applyBlock (.tagLenEq expected length) [.block actual target] targetState =
        some (closResult, targetState) ∧ ValueRel flatResult closResult := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  rw [← related_lengths related]
  exact boolValue_related _

/-- Length checks preserve their Boolean result for both tuple and tagged
constructors. -/
theorem lenEq_related {C F : Type} (sourceState : FlatSem.State C F) (targetState : ClosSem.State C F)
    (expected tag : Nat) (stamp : Option (FlatLang.CtorId × FlatLang.TypeId))
    (source : List FlatSem.Value) (target : List ClosSem.Value) (related : List.Forall₂ ValueRel source target) :
    ∃ flatResult closResult,
      FlatSem.doAppFlat sourceState (.lenEq expected) [.conv stamp source] =
        some (some (sourceState, .val flatResult)) ∧
      ClosSem.applyBlock (.lenEq expected) [.block tag target] targetState =
        some (closResult, targetState) ∧ ValueRel flatResult closResult := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  rw [← related_lengths related]
  exact boolValue_related _

end Flapjack.Compiler.Backend.FlatToClos
