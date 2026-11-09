module

public import Flapjack.Compiler.Backend.DataSpace.Proofs.PrimitiveSpace

@[expose] public section

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

/-- Byte-array updates do not inspect reserved space. -/
theorem doAppAux_updateByte_with_space {C F : Type} (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.memOp .updateByte) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp .updateByte) values state) := by
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
          cases first <;> cases second <;> cases third <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
          case refPtr.number.number flag ptr index byte =>
            cases found : sptLookup ptr state.refs with
            | none => simp
            | some entry =>
              cases entry <;> simp
              case byteArray mutability bytes =>
                by_cases invalid : index < 0 ∨ index.toNat ≥ bytes.length
                · simp [invalid]
                · cases converted : ClosSem.intToByte byte <;> simp [invalid]

/-- Mutable-constructor updates do not inspect reserved space. -/
theorem doAppAux_updateCons_with_space {C F : Type} (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.memOp .updateCons) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp .updateCons) values state) := by
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
              case mutBlock tag done left child right =>
                cases done with
                | true => simp
                | false =>
                  by_cases mismatch : index ≠ (left.length : Int) <;> simp [mismatch]

/-- Array and byte-array length reads do not inspect reserved space. -/
theorem doAppAux_length_with_space {C F : Type} (op : ClosLang.MemOp)
    (values : List DataSem.Value) (state : State C F) (space : Nat)
    (lengthOp : op = .length ∨ op = .lengthByte) :
    doAppAux (.memOp op) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp op) values state) := by
  rcases lengthOp with rfl | rfl
  all_goals
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
        case refPtr flag ptr =>
          cases found : sptLookup ptr state.refs with
          | none => simp
          | some entry => cases entry <;> simp

/-- Array and byte-array bounds checks do not inspect reserved space. -/
theorem doAppAux_bounds_with_space {C F : Type} (op : ClosLang.MemOp)
    (values : List DataSem.Value) (state : State C F) (space : Nat)
    (boundsOp : op = .boundsCheckArray ∨ ∃ loose, op = .boundsCheckByte loose) :
    doAppAux (.memOp op) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp op) values state) := by
  rcases boundsOp with rfl | ⟨loose, rfl⟩
  all_goals
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
        | nil =>
          cases first <;> cases second <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
          case refPtr.number flag ptr index =>
            cases found : sptLookup ptr state.refs with
            | none => simp
            | some entry => cases entry <;> simp

/-- Indexed value reads do not inspect reserved space. -/
theorem doAppAux_el_with_space {C F : Type} (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.memOp .el) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp .el) values state) := by
  cases values with
  | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
        case block.number timestamp tag values index =>
          by_cases negative : index < 0
          · simp [negative]
          · cases slot : values[index.toNat]? <;> simp [negative]
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr state.refs with
          | none => simp
          | some entry =>
            cases entry <;> simp
            case valueArray values =>
              by_cases negative : index < 0
              · simp [negative]
              · cases slot : values[index.toNat]? <;> simp [negative]

/-- Indexed byte reads do not inspect reserved space. -/
theorem doAppAux_derefByte_with_space {C F : Type} (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.memOp .derefByte) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp .derefByte) values state) := by
  cases values with
  | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr state.refs with
          | none => simp
          | some entry =>
            cases entry <;> simp
            case byteArray mutability bytes =>
              by_cases negative : index < 0
              · simp [negative]
              · cases slot : bytes[index.toNat]? <;> simp [negative]

/-- Every memory operation permitted in an unannotated assignment has an
auxiliary result independent of the amount of reserved space. -/
theorem doAppAux_memory_noNames_with_space {C F : Type} (op : ClosLang.MemOp)
    (values : List DataSem.Value) (state : State C F) (space : Nat)
    (valid : DataLang.opRequiresNames (.memOp op) = false) :
    doAppAux (.memOp op) values { state with space := space } =
      replaceResultSpace space (doAppAux (.memOp op) values state) := by
  cases op <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at valid
  case ref => exact doAppAux_ref_with_space values state space
  case update => exact doAppAux_update_with_space values state space
  case el => exact doAppAux_el_with_space values state space
  case length => exact doAppAux_length_with_space _ values state space (Or.inl rfl)
  case lengthByte => exact doAppAux_length_with_space _ values state space (Or.inr rfl)
  case derefByte => exact doAppAux_derefByte_with_space values state space
  case updateByte => exact doAppAux_updateByte_with_space values state space
  case concatByteVec => cases values <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
  case fromListByte => cases values <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
  case toListByte => cases values <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
  case lengthByteVec => cases values <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
  case derefByteVec => cases values <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
  case boundsCheckArray => exact doAppAux_bounds_with_space _ values state space (Or.inl rfl)
  case boundsCheckByte loose => exact doAppAux_bounds_with_space _ values state space (Or.inr ⟨loose, rfl⟩)
  case mutCons tag index => exact doAppAux_mutCons_with_space tag index values state space
  case updateCons => exact doAppAux_updateCons_with_space values state space
  case finaliseCons => exact doAppAux_finaliseCons_with_space values state space

end Flapjack.Compiler.Backend.DataSpace
