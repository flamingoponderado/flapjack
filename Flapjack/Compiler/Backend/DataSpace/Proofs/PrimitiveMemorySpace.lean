import Flapjack.Compiler.Backend.DataSpace.Proofs.PrimitiveSpace

/-! Independence of memory primitive results from reserved space. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Reference allocation does not inspect reserved space. -/
theorem doAppAux_ref_with_space {C F : Type} (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.memOp .ref) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp .ref) values state) := by
  simp [doAppAux, applyNonFfi, replaceResultSpace]

/-- Mutable-constructor allocation does not inspect reserved space. -/
theorem doAppAux_mutCons_with_space {C F : Type} (tag index : Nat)
    (values : List DataSem.Value) (state : State C F) (space : Nat) :
    doAppAux (.memOp (.mutCons tag index)) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp (.mutCons tag index)) values state) := by
  cases found : values[index]? <;> simp [doAppAux, applyNonFfi, replaceResultSpace, found]

/-- Finalising a constructor does not inspect reserved space. -/
theorem doAppAux_finaliseCons_with_space {C F : Type} (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.memOp .finaliseCons) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp .finaliseCons) values state) := by
  cases values with
  | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | nil =>
      cases found : finaliseCons first state.refs state.tstamps with
      | none => simp [doAppAux, applyNonFfi, replaceResultSpace, found]
      | some result =>
        obtain ⟨value, refs, stamps⟩ := result
        simp [doAppAux, applyNonFfi, replaceResultSpace, found]

/-- Value-array updates do not inspect reserved space. -/
theorem doAppAux_update_with_space {C F : Type} (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.memOp .update) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp .update) values state) := by
  cases values with
  | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | cons third tail =>
        cases tail with
        | cons fourth tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
        | nil =>
          cases first <;> cases second <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
          case refPtr.number flag ptr index =>
            cases found : sptLookup ptr state.refs with
            | none => simp
            | some entry =>
              cases entry <;> simp
              case valueArray values =>
                by_cases invalid : index < 0 ∨ index.toNat ≥ values.length <;> simp [invalid]

end Flapjack.Compiler.Backend.DataSpace
