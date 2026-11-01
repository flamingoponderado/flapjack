import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame

/-! Local and control frames for memory primitive application. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Allocating a reference changes the reference store but preserves the
local and control fields used by the pass simulation. -/
theorem doAppAux_ref_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .ref) args state = .val (value, next)) : SameLocalControl state next := by
  simp [doAppAux, applyNonFfi] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful array allocation preserves locals and control fields. -/
theorem doAppAux_refArray_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .refArray) args state = .val (value, next)) : SameLocalControl state next := by
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
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful GC-configuration primitive preserves locals and control. -/
theorem doAppAux_configGC_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .configGC) args state = .val (value, next)) : SameLocalControl state next := by
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
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Array bounds checks preserve locals and control fields. -/
theorem doAppAux_boundsCheckArray_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .boundsCheckArray) args state = .val (value, next)) : SameLocalControl state next := by
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
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Byte-array bounds checks preserve locals and control fields in both
strict and inclusive modes. -/
theorem doAppAux_boundsCheckByte_frame {C F : Type} (loose : Bool) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.boundsCheckByte loose)) args state = .val (value, next)) : SameLocalControl state next := by
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
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reading an array length preserves locals and control fields. -/
theorem doAppAux_length_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .length) args state = .val (value, next)) : SameLocalControl state next := by
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
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reading a byte-array length preserves locals and control fields. -/
theorem doAppAux_lengthByte_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .lengthByte) args state = .val (value, next)) : SameLocalControl state next := by
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
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A byte-array read preserves locals and control fields. -/
theorem doAppAux_derefByte_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .derefByte) args state = .val (value, next)) : SameLocalControl state next := by
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
                  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An indexed read preserves locals and control fields, for both direct
blocks and reference-backed arrays. -/
theorem doAppAux_el_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .el) args state = .val (value, next)) : SameLocalControl state next := by
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
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
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
                  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A value-array update changes the reference store while preserving locals
and control fields. -/
theorem doAppAux_update_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .update) args state = .val (value, next)) : SameLocalControl state next := by
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
                  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A byte-array update changes the reference store while preserving locals
and control fields. -/
theorem doAppAux_updateByte_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .updateByte) args state = .val (value, next)) : SameLocalControl state next := by
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
                    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Allocating a byte array preserves locals and control fields. -/
theorem doAppAux_refByte_frame {C F : Type} (flag : Bool) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.refByte flag)) args state = .val (value, next)) : SameLocalControl state next := by
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
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Allocating a mutable constructor preserves locals and control fields. -/
theorem doAppAux_mutCons_frame {C F : Type} (tag index : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.mutCons tag index)) args state = .val (value, next)) : SameLocalControl state next := by
  cases slot : args[index]? with
  | none => simp [doAppAux, applyNonFfi, slot] at run
  | some child =>
    simp [doAppAux, applyNonFfi, slot] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Finalising a constructor changes references and timestamps, while
preserving locals and control fields. -/
theorem doAppAux_finaliseCons_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .finaliseCons) args state = .val (value, next)) : SameLocalControl state next := by
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
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Updating a mutable constructor changes its reference-store entry but
preserves locals and control fields. -/
theorem doAppAux_updateCons_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .updateCons) args state = .val (value, next)) : SameLocalControl state next := by
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
                    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- String comparison preserves locals and control fields. -/
theorem doAppAux_stringCmp_frame {C F : Type} (fast : Bool) (cmp : Opb) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.stringCmp fast cmp)) args state = .val (value, next)) : SameLocalControl state next := by
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
                  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Byte-array XOR preserves locals and control fields. -/
theorem doAppAux_xorByte_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .xorByte) args state = .val (value, next)) : SameLocalControl state next := by
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
                    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The data dispatcher has no successful `concatByteVec` auxiliary clause. -/
theorem doAppAux_concatByteVec_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .concatByteVec) args state = .val (value, next)) : SameLocalControl state next := by
  cases args <;> simp [doAppAux, applyNonFfi] at run

/-- The data dispatcher has no successful `fromListByte` auxiliary clause. -/
theorem doAppAux_fromListByte_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .fromListByte) args state = .val (value, next)) : SameLocalControl state next := by
  cases args <;> simp [doAppAux, applyNonFfi] at run

/-- The data dispatcher has no successful `toListByte` auxiliary clause. -/
theorem doAppAux_toListByte_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .toListByte) args state = .val (value, next)) : SameLocalControl state next := by
  cases args <;> simp [doAppAux, applyNonFfi] at run

/-- The data dispatcher has no successful `lengthByteVec` auxiliary clause. -/
theorem doAppAux_lengthByteVec_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .lengthByteVec) args state = .val (value, next)) : SameLocalControl state next := by
  cases args <;> simp [doAppAux, applyNonFfi] at run

/-- The data dispatcher has no successful `derefByteVec` auxiliary clause. -/
theorem doAppAux_derefByteVec_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .derefByteVec) args state = .val (value, next)) : SameLocalControl state next := by
  cases args <;> simp [doAppAux, applyNonFfi] at run

/-- Copying into a byte array changes the reference store but preserves
locals and control fields. -/
theorem doAppAux_copyByte_false_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.copyByte false)) args state = .val (value, next)) : SameLocalControl state next := by
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
                                  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The data auxiliary dispatcher has no successful true-mode byte-copy
clause. -/
theorem doAppAux_copyByte_true_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp (.copyByte true)) args state = .val (value, next)) : SameLocalControl state next := by
  cases args <;> simp [doAppAux, applyNonFfi] at run

/-- Every successful memory auxiliary operation preserves local and control
fields. This is Flapjack infrastructure for evaluator and pass proofs. -/
theorem doAppAux_mem_frame {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp op) args state = .val (value, next)) : SameLocalControl state next := by
  cases op with
  | ref => exact doAppAux_ref_frame args state next value run
  | update => exact doAppAux_update_frame args state next value run
  | el => exact doAppAux_el_frame args state next value run
  | length => exact doAppAux_length_frame args state next value run
  | lengthByte => exact doAppAux_lengthByte_frame args state next value run
  | refByte flag => exact doAppAux_refByte_frame flag args state next value run
  | refArray => exact doAppAux_refArray_frame args state next value run
  | derefByte => exact doAppAux_derefByte_frame args state next value run
  | updateByte => exact doAppAux_updateByte_frame args state next value run
  | concatByteVec => exact doAppAux_concatByteVec_frame args state next value run
  | copyByte flag =>
    cases flag with
    | false => exact doAppAux_copyByte_false_frame args state next value run
    | true => exact doAppAux_copyByte_true_frame args state next value run
  | fromListByte => exact doAppAux_fromListByte_frame args state next value run
  | toListByte => exact doAppAux_toListByte_frame args state next value run
  | lengthByteVec => exact doAppAux_lengthByteVec_frame args state next value run
  | derefByteVec => exact doAppAux_derefByteVec_frame args state next value run
  | stringCmp fast cmp => exact doAppAux_stringCmp_frame fast cmp args state next value run
  | xorByte => exact doAppAux_xorByte_frame args state next value run
  | boundsCheckArray => exact doAppAux_boundsCheckArray_frame args state next value run
  | boundsCheckByte loose => exact doAppAux_boundsCheckByte_frame loose args state next value run
  | mutCons tag index => exact doAppAux_mutCons_frame tag index args state next value run
  | updateCons => exact doAppAux_updateCons_frame args state next value run
  | finaliseCons => exact doAppAux_finaliseCons_frame args state next value run
  | configGC => exact doAppAux_configGC_frame args state next value run

/-- Lift a memory auxiliary frame through resource bookkeeping. -/
theorem doApp_mem_frame_of_aux {C F : Type} (op : ClosLang.MemOp)
    (auxFrame : ∀ (args : List Value) (before after : State C F) (value : Value),
      doAppAux (.memOp op) args before = .val (value, after) → SameLocalControl before after)
    (args : List Value) (state next : State C F) (value : Value)
    (run : doApp (.memOp op) args state = .val (value, next)) : SameLocalControl state next := by
  simp only [doApp] at run
  cases space : doSpace (.memOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := doSpace_frame (.memOp op) args state accounted space
    have second := auxFrame args _ next value run
    have second' : SameLocalControl accounted next := by
      simpa [SameLocalControl, doStack, doLimSafe] using second
    exact first.trans second'

/-- Successful memory operations preserve local and control fields through
the full dispatcher. -/
theorem doApp_mem_frame {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.memOp op) args state = .val (value, next)) : SameLocalControl state next :=
  doApp_mem_frame_of_aux op (doAppAux_mem_frame op) args state next value run

end Flapjack.Compiler.Backend.DataSem
