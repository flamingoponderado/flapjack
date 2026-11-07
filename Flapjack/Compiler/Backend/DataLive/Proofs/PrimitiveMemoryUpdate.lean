import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveMemoryRead

/-! Mutating memory primitive simulation for the liveness pass. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Related states perform the same value-array update. This theorem is
untagged pending source evaluator and state-carrier review. -/
theorem stateRel_doAppAux_update {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .update) args source) (doAppAux (.memOp .update) args target) := by
  have refs := related.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, appRel]
      | cons third tail =>
        cases tail with
        | cons fourth tail => simp [doAppAux, applyNonFfi, appRel]
        | nil =>
          cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
          case refPtr.number flag ptr index =>
            cases found : sptLookup ptr source.refs with
            | none => simp [found, ← refs]
            | some entry =>
              cases entry <;> simp [found, ← refs]
              case valueArray values =>
                by_cases invalid : index < 0 ∨ index.toNat ≥ values.length
                · simp [invalid]
                · simpa [invalid, ← refs, appRel] using stateRel_setRefs source target live
                    (sptInsert ptr (.valueArray (values.set index.toNat third)) source.refs) related

/-- Related states perform the same byte-array update. -/
theorem stateRel_doAppAux_updateByte {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .updateByte) args source) (doAppAux (.memOp .updateByte) args target) := by
  have refs := related.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, appRel]
      | cons third tail =>
        cases tail with
        | cons fourth tail => simp [doAppAux, applyNonFfi, appRel]
        | nil =>
          cases first <;> cases second <;> cases third <;> simp [doAppAux, applyNonFfi, appRel]
          case refPtr.number.number flag ptr index byte =>
            cases found : sptLookup ptr source.refs with
            | none => simp [found, ← refs]
            | some entry =>
              cases entry <;> simp [found, ← refs]
              case byteArray mutability bytes =>
                by_cases invalid : index < 0 ∨ index.toNat ≥ bytes.length
                · simp [invalid]
                · cases converted : ClosSem.intToByte byte with
                  | none => simp [invalid]
                  | some b =>
                    simpa [invalid, converted, ← refs, appRel] using stateRel_setRefs source target live
                      (sptInsert ptr (.byteArray mutability (bytes.set index.toNat b)) source.refs) related

/-- Related states update the same mutable-constructor entry. -/
theorem stateRel_doAppAux_updateCons {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .updateCons) args source) (doAppAux (.memOp .updateCons) args target) := by
  have refs := related.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, appRel]
      | cons third tail =>
        cases tail with
        | cons fourth tail => simp [doAppAux, applyNonFfi, appRel]
        | nil =>
          cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
          case refPtr.number flag ptr index =>
            cases found : sptLookup ptr source.refs with
            | none => simp [found, ← refs]
            | some entry =>
              cases entry <;> simp [found, ← refs]
              case mutBlock tag done left child right =>
                cases done with
                | true => simp
                | false =>
                  by_cases mismatch : index ≠ (left.length : Int)
                  · simp [mismatch]
                  · simpa [mismatch, ← refs, appRel] using stateRel_setRefs source target live
                      (sptInsert ptr (.mutBlock tag false left third right) source.refs) related

/-- Related states XOR the same byte arrays and write identical results. -/
theorem stateRel_doAppAux_xorByte {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .xorByte) args source) (doAppAux (.memOp .xorByte) args target) := by
  have refs := related.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
        case refPtr.refPtr bitA ptrA bitB ptrB =>
          cases foundB : sptLookup ptrB source.refs with
          | none => simp [foundB, ← refs]
          | some entryB =>
            cases entryB <;> simp [foundB, ← refs]
            case byteArray flagB bytesB =>
              cases foundA : sptLookup ptrA source.refs with
              | none => simp
              | some entryA =>
                cases entryA <;> simp
                case byteArray flagA bytesA =>
                  cases result : xorBytes bytesB bytesA with
                  | none => simp
                  | some updated =>
                    simpa [result, ← refs, appRel] using stateRel_setRefs source target live
                      (sptInsert ptrA (.byteArray flagA updated) source.refs) related

/-- The disabled byte-vector conversion and true-mode byte-copy branches
produce matching type errors. -/
theorem stateRel_doAppAux_fromListByte {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) :
    appRel live (doAppAux (.memOp .fromListByte) args source) (doAppAux (.memOp .fromListByte) args target) := by
  cases args <;> simp [doAppAux, applyNonFfi, appRel]

theorem stateRel_doAppAux_copyByte_true {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) :
    appRel live (doAppAux (.memOp (.copyByte true)) args source) (doAppAux (.memOp (.copyByte true)) args target) := by
  cases args <;> simp [doAppAux, applyNonFfi, appRel]

/-- GC configuration has matching auxiliary outcomes and does not change
the related state. -/
theorem stateRel_doAppAux_configGC {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .configGC) args source) (doAppAux (.memOp .configGC) args target) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
        exact related

/-- Related states copy the same byte range and write the same result. -/
theorem stateRel_doAppAux_copyByte_false {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp (.copyByte false)) args source)
      (doAppAux (.memOp (.copyByte false)) args target) := by
  have refs := related.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons a rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons b rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, appRel]
      | cons c rest =>
        cases rest with
        | nil => simp [doAppAux, applyNonFfi, appRel]
        | cons d rest =>
          cases rest with
          | nil => simp [doAppAux, applyNonFfi, appRel]
          | cons e rest =>
            cases rest with
            | cons f rest => simp [doAppAux, applyNonFfi, appRel]
            | nil =>
              cases a <;> try (simp [doAppAux, applyNonFfi, appRel])
              case refPtr srcBit src =>
                cases b <;> try simp
                case number offset =>
                  cases c <;> try simp
                  case number length =>
                    cases d <;> try simp
                    case refPtr dstBit dst =>
                      cases e <;> try simp
                      case number dstOffset =>
                        cases srcFound : sptLookup src source.refs with
                        | none => simp [srcFound, ← refs]
                        | some srcEntry =>
                          cases srcEntry <;> simp [srcFound, ← refs]
                          case byteArray srcFlag srcBytes =>
                            cases dstFound : sptLookup dst source.refs with
                            | none => simp
                            | some dstEntry =>
                              cases dstEntry <;> simp
                              case byteArray dstFlag dstBytes =>
                                cases copied : copyArray (srcBytes, offset) length (some (dstBytes, dstOffset)) with
                                | none => simp
                                | some updated =>
                                  simpa [copied, ← refs, appRel] using stateRel_setRefs source target live
                                    (sptInsert dst (.byteArray dstFlag updated) source.refs) related

/-- Every memory primitive produces matching outcomes on related states.
This result remains untagged pending source evaluator and carrier review. -/
theorem stateRel_doAppAux_memory {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.MemOp) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp op) args source) (doAppAux (.memOp op) args target) := by
  by_cases pure : isPure (.memOp op) = true
  · exact stateRel_doAppAux_pureMemory source target live op args pure related
  · cases op <;> simp [isPure] at pure
    case ref => exact stateRel_doAppAux_ref source target live args related
    case update => exact stateRel_doAppAux_update source target live args related
    case refByte flag => exact stateRel_doAppAux_refByte source target live flag args related
    case refArray => exact stateRel_doAppAux_refArray source target live args related
    case updateByte => exact stateRel_doAppAux_updateByte source target live args related
    case copyByte flag =>
      cases flag with
      | false => exact stateRel_doAppAux_copyByte_false source target live args related
      | true => exact stateRel_doAppAux_copyByte_true source target live args
    case fromListByte => exact stateRel_doAppAux_fromListByte source target live args
    case xorByte => exact stateRel_doAppAux_xorByte source target live args related
    case mutCons tag index => exact stateRel_doAppAux_mutCons source target live tag index args related
    case updateCons => exact stateRel_doAppAux_updateCons source target live args related
    case finaliseCons => exact stateRel_doAppAux_finaliseCons source target live args related
    case configGC => exact stateRel_doAppAux_configGC source target live args related

/-- Every memory assignment satisfies the liveness simulation. -/
theorem simulationFor_assign_memory_all {C F : Type} (dest : Nat) (op : ClosLang.MemOp)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.memOp op) args names) live := by
  apply simulationFor_assign_memory_of_aux dest op args names live
  intro source target values related
  exact stateRel_doAppAux_memory source target _ op values related

/-- Every assignment satisfies the liveness simulation. This is the full
assignment case for the current Lean evaluator, untagged pending source
evaluator and state-carrier review. -/
theorem simulationFor_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest op args names) live := by
  cases op with
  | label label => exact simulationFor_assign_label_all dest label args names live
  | ffi name => exact simulationFor_assign_ffi_all dest name args names live
  | intOp op => exact simulationFor_assign_int_all dest op args names live
  | wordOp op => exact simulationFor_assign_word_all dest op args names live
  | blockOp op => exact simulationFor_assign_block_all dest op args names live
  | globOp op => exact simulationFor_assign_global_all dest op args names live
  | memOp op => exact simulationFor_assign_memory_all dest op args names live
  | install => exact simulationFor_assign_install_all dest args names live
  | thunkOp op => exact simulationFor_assign_thunk_all dest op args names live

end Flapjack.Compiler.Backend.DataLive
