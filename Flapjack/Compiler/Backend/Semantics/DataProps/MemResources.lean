import Flapjack.Compiler.Backend.Semantics.DataProps.PrimitiveResources

/-! Resource observations of source memory operations. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- The auxiliary memory cases preserve the source resource observations. -/
theorem doAppAux_ref_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .ref) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  simp [doAppAux, applyNonFfi] at run
  obtain ⟨rfl, rfl⟩ := run
  simp [BackendProps.optionLe_refl]


theorem doAppAux_refArray_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .refArray) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi] at run
        case number count =>
          by_cases negative : count < 0
          · simp [negative] at run
          · simp [negative] at run
            obtain ⟨rfl, rfl⟩ := run
            simp [BackendProps.optionLe_refl]


theorem doAppAux_configGC_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .configGC) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        obtain ⟨rfl, rfl⟩ := run
        simp [BackendProps.optionLe_refl]


theorem doAppAux_boundsCheckArray_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .boundsCheckArray) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            case valueArray values =>
              obtain ⟨rfl, rfl⟩ := run
              simp [BackendProps.optionLe_refl]


theorem doAppAux_boundsCheckByte_resource_frame {C F : Type} (loose : Bool) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.boundsCheckByte loose)) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            case byteArray mutability bytes =>
              obtain ⟨rfl, rfl⟩ := run
              simp [BackendProps.optionLe_refl]


theorem doAppAux_length_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .length) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases first <;> simp [doAppAux, applyNonFfi] at run
      case refPtr flag ptr =>
        cases found : sptLookup ptr state.refs with
        | none => simp [found] at run
        | some entry =>
          cases entry <;> simp [found] at run
          case valueArray values =>
            obtain ⟨rfl, rfl⟩ := run
            simp [BackendProps.optionLe_refl]


theorem doAppAux_lengthByte_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .lengthByte) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases first <;> simp [doAppAux, applyNonFfi] at run
      case refPtr flag ptr =>
        cases found : sptLookup ptr state.refs with
        | none => simp [found] at run
        | some entry =>
          cases entry <;> simp [found] at run
          case byteArray mutability bytes =>
            obtain ⟨rfl, rfl⟩ := run
            simp [BackendProps.optionLe_refl]


theorem doAppAux_derefByte_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .derefByte) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            case byteArray mutability bytes =>
              by_cases negative : index < 0
              · simp [negative] at run
              · cases slot : bytes[index.toNat]? with
                | none => simp [negative, slot] at run
                | some byte =>
                  simp [negative, slot] at run
                  obtain ⟨rfl, rfl⟩ := run
                  simp [BackendProps.optionLe_refl]


theorem doAppAux_el_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .el) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        case block.number timestamp tag values index =>
          by_cases negative : index < 0
          · simp [negative] at run
          · cases slot : values[index.toNat]? with
            | none => simp [negative, slot] at run
            | some item =>
              simp [negative, slot] at run
              obtain ⟨rfl, rfl⟩ := run
              simp [BackendProps.optionLe_refl]
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            case valueArray values =>
              by_cases negative : index < 0
              · simp [negative] at run
              · cases slot : values[index.toNat]? with
                | none => simp [negative, slot] at run
                | some item =>
                  simp [negative, slot] at run
                  obtain ⟨rfl, rfl⟩ := run
                  simp [BackendProps.optionLe_refl]


theorem doAppAux_update_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .update) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons third tail =>
        cases tail with
        | cons fourth tail => simp [doAppAux, applyNonFfi] at run
        | nil =>
          cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
          case refPtr.number flag ptr index =>
            cases found : sptLookup ptr state.refs with
            | none => simp [found] at run
            | some entry =>
              cases entry <;> simp [found] at run
              case valueArray values =>
                by_cases invalid : index < 0 ∨ index.toNat ≥ values.length
                · simp [invalid] at run
                · simp [invalid] at run
                  obtain ⟨rfl, rfl⟩ := run
                  simp [BackendProps.optionLe_refl]


theorem doAppAux_updateByte_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .updateByte) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons third tail =>
        cases tail with
        | cons fourth tail => simp [doAppAux, applyNonFfi] at run
        | nil =>
          cases first <;> cases second <;> cases third <;> simp [doAppAux, applyNonFfi] at run
          case refPtr.number.number flag ptr index byte =>
            cases found : sptLookup ptr state.refs with
            | none => simp [found] at run
            | some entry =>
              cases entry <;> simp [found] at run
              case byteArray mutability bytes =>
                by_cases invalid : index < 0 ∨ index.toNat ≥ bytes.length
                · simp [invalid] at run
                · cases converted : ClosSem.intToByte byte with
                  | none => simp [invalid, converted] at run
                  | some b =>
                    simp [invalid, converted] at run
                    obtain ⟨rfl, rfl⟩ := run
                    simp [BackendProps.optionLe_refl]


theorem doAppAux_refByte_resource_frame {C F : Type} (flag : Bool) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.refByte flag)) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        case number.number count byte =>
          by_cases negative : count < 0
          · simp [negative] at run
          · cases converted : ClosSem.intToByte byte with
            | none => simp [negative, converted] at run
            | some b =>
              simp [negative, converted] at run
              obtain ⟨rfl, rfl⟩ := run
              simp [BackendProps.optionLe_refl]


theorem doAppAux_mutCons_resource_frame {C F : Type} (tag index : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.mutCons tag index)) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases slot : args[index]? with
  | none => simp [doAppAux, applyNonFfi, slot] at run
  | some child =>
    simp [doAppAux, applyNonFfi, slot] at run
    obtain ⟨rfl, rfl⟩ := run
    simp [BackendProps.optionLe_refl]


theorem doAppAux_finaliseCons_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .finaliseCons) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases result : finaliseCons first state.refs state.tstamps with
      | none => simp [doAppAux, applyNonFfi, result] at run
      | some triple =>
        obtain ⟨built, refs, stamps⟩ := triple
        simp [doAppAux, applyNonFfi, result] at run
        obtain ⟨rfl, rfl⟩ := run
        simp [BackendProps.optionLe_refl]


theorem doAppAux_updateCons_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .updateCons) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons third tail =>
        cases tail with
        | cons fourth tail => simp [doAppAux, applyNonFfi] at run
        | nil =>
          cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
          case refPtr.number flag ptr index =>
            cases found : sptLookup ptr state.refs with
            | none => simp [found] at run
            | some entry =>
              cases entry <;> simp [found] at run
              case mutBlock tag done left child right =>
                cases done with
                | true => simp at run
                | false =>
                  by_cases mismatch : index ≠ (left.length : Int)
                  · simp [mismatch] at run
                  · simp [mismatch] at run
                    obtain ⟨rfl, rfl⟩ := run
                    simp [BackendProps.optionLe_refl]


theorem doAppAux_stringCmp_resource_frame {C F : Type} (fast : Bool) (cmp : Opb) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.stringCmp fast cmp)) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        case refPtr.refPtr bitA ptrA bitB ptrB =>
          cases foundA : sptLookup ptrA state.refs with
          | none => simp [foundA] at run
          | some entryA =>
            cases entryA <;> simp [foundA] at run
            case byteArray flagA bytesA =>
              cases foundB : sptLookup ptrB state.refs with
              | none => simp [foundB] at run
              | some entryB =>
                cases entryB <;> simp [foundB] at run
                case byteArray flagB bytesB =>
                  obtain ⟨rfl, rfl⟩ := run
                  simp [BackendProps.optionLe_refl]


theorem doAppAux_xorByte_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .xorByte) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        case refPtr.refPtr bitA ptrA bitB ptrB =>
          cases foundB : sptLookup ptrB state.refs with
          | none => simp [foundB] at run
          | some entryB =>
            cases entryB <;> simp [foundB] at run
            case byteArray flagB bytesB =>
              cases foundA : sptLookup ptrA state.refs with
              | none => simp [foundA] at run
              | some entryA =>
                cases entryA <;> simp [foundA] at run
                case byteArray flagA bytesA =>
                  cases result : xorBytes bytesB bytesA with
                  | none => simp [result] at run
                  | some updated =>
                    simp [result] at run
                    obtain ⟨rfl, rfl⟩ := run
                    simp [BackendProps.optionLe_refl]


theorem doAppAux_concatByteVec_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .concatByteVec) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args <;> simp [doAppAux, applyNonFfi] at run


theorem doAppAux_fromListByte_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .fromListByte) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args <;> simp [doAppAux, applyNonFfi] at run


theorem doAppAux_toListByte_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .toListByte) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args <;> simp [doAppAux, applyNonFfi] at run


theorem doAppAux_lengthByteVec_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .lengthByteVec) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args <;> simp [doAppAux, applyNonFfi] at run


theorem doAppAux_derefByteVec_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .derefByteVec) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args <;> simp [doAppAux, applyNonFfi] at run


theorem doAppAux_copyByte_false_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.copyByte false)) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons a rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons b rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons c rest =>
        cases rest with
        | nil => simp [doAppAux, applyNonFfi] at run
        | cons d rest =>
          cases rest with
          | nil => simp [doAppAux, applyNonFfi] at run
          | cons e rest =>
            cases rest with
            | cons f rest => simp [doAppAux, applyNonFfi] at run
            | nil =>
              cases a <;> try (simp [doAppAux, applyNonFfi] at run)
              case refPtr srcBit src =>
                cases b <;> try (simp at run)
                case number offset =>
                  cases c <;> try (simp at run)
                  case number length =>
                    cases d <;> try (simp at run)
                    case refPtr dstBit dst =>
                      cases e <;> try (simp at run)
                      case number dstOffset =>
                        cases srcFound : sptLookup src state.refs with
                        | none => simp [srcFound] at run
                        | some srcEntry =>
                          cases srcEntry <;> simp [srcFound] at run
                          case byteArray srcFlag srcBytes =>
                            cases dstFound : sptLookup dst state.refs with
                            | none => simp [dstFound] at run
                            | some dstEntry =>
                              cases dstEntry <;> simp [dstFound] at run
                              case byteArray dstFlag dstBytes =>
                                cases copied : copyArray (srcBytes, offset) length (some (dstBytes, dstOffset)) with
                                | none => simp [copied] at run
                                | some updated =>
                                  simp [copied] at run
                                  obtain ⟨rfl, rfl⟩ := run
                                  simp [BackendProps.optionLe_refl]


theorem doAppAux_copyByte_true_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.copyByte true)) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args <;> simp [doAppAux, applyNonFfi] at run


theorem doAppAux_mem_resource_frame {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp op) args state = .val (value, next)) : state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases op with
  | ref => exact doAppAux_ref_resource_frame args state next value run
  | update => exact doAppAux_update_resource_frame args state next value run
  | el => exact doAppAux_el_resource_frame args state next value run
  | length => exact doAppAux_length_resource_frame args state next value run
  | lengthByte => exact doAppAux_lengthByte_resource_frame args state next value run
  | refByte flag => exact doAppAux_refByte_resource_frame flag args state next value run
  | refArray => exact doAppAux_refArray_resource_frame args state next value run
  | derefByte => exact doAppAux_derefByte_resource_frame args state next value run
  | updateByte => exact doAppAux_updateByte_resource_frame args state next value run
  | concatByteVec => exact doAppAux_concatByteVec_resource_frame args state next value run
  | copyByte flag =>
    cases flag with
    | false => exact doAppAux_copyByte_false_resource_frame args state next value run
    | true => exact doAppAux_copyByte_true_resource_frame args state next value run
  | fromListByte => exact doAppAux_fromListByte_resource_frame args state next value run
  | toListByte => exact doAppAux_toListByte_resource_frame args state next value run
  | lengthByteVec => exact doAppAux_lengthByteVec_resource_frame args state next value run
  | derefByteVec => exact doAppAux_derefByteVec_resource_frame args state next value run
  | stringCmp fast cmp => exact doAppAux_stringCmp_resource_frame fast cmp args state next value run
  | xorByte => exact doAppAux_xorByte_resource_frame args state next value run
  | boundsCheckArray => exact doAppAux_boundsCheckArray_resource_frame args state next value run
  | boundsCheckByte loose => exact doAppAux_boundsCheckByte_resource_frame loose args state next value run
  | mutCons tag index => exact doAppAux_mutCons_resource_frame tag index args state next value run
  | updateCons => exact doAppAux_updateCons_resource_frame args state next value run
  | finaliseCons => exact doAppAux_finaliseCons_resource_frame args state next value run
  | configGC => exact doAppAux_configGC_resource_frame args state next value run



/-- Memory operations satisfy resource monotonicity through the production dispatcher. -/
theorem doApp_mem_resource_frame {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.memOp op) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  simp only [doApp] at run
  cases space : doSpace (.memOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    exact accounted_resource_frame _ args state accounted next value space run
      (fun before after v h => doAppAux_mem_resource_frame op args before after v h)

end Flapjack.Compiler.Backend.DataSem
