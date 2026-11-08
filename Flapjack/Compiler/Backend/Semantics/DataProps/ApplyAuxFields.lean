import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux
import Flapjack.SemanticPrimitivesProps.ResultMap

/-! Field-independence lemmas for the auxiliary primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

private def applyNonFfiFields {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value) : Prop :=
  ∀ (state : State C F) (stack : List Stack) (localsSize mx : Option Nat)
    (peak : Nat) (locals : Spt DataSem.Value) (space : Nat)
    (handler clock : Nat) (frameSizes : Spt Nat) (compiler : Compiler C),
    applyNonFfi op values { state with stack := stack, localsSize := localsSize, stackMax := mx, peakHeapLength := peak, locals := locals, space := space, handler := handler, clock := clock, stackFrameSizes := frameSizes, compile := compiler } =
      (applyNonFfi op values state).map (fun (value, next) =>
        (value, { next with stack := stack, localsSize := localsSize, stackMax := mx, peakHeapLength := peak, locals := locals, space := space, handler := handler, clock := clock, stackFrameSizes := frameSizes, compile := compiler }))

private theorem applyNonFfiFields_int {C F : Type} (op : ClosLang.IntOp) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.intOp op) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases result : doIntApp op values <;> simp [applyNonFfi, result]

private theorem applyNonFfiFields_word {C F : Type} (op : ClosLang.WordOp) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.wordOp op) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases result : doWordApp op values <;> simp [applyNonFfi, result]

private theorem applyNonFfiFields_label {C F : Type} (label : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.label label) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => cases found : (sptLookup label state.code).isSome <;> simp [applyNonFfi, found]
  | cons value rest => simp [applyNonFfi]

private theorem applyNonFfiFields_install {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) .install values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  simp [applyNonFfi]

private theorem applyNonFfiFields_ffi {C F : Type} (name : Basis.Pure.MlString.MlString)
    (values : List DataSem.Value) : applyNonFfiFields (C := C) (F := F) (.ffi name) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  simp [applyNonFfi]

private theorem applyNonFfiFields_thunk {C F : Type} (op : AstHOL.ThunkOp) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.thunkOp op) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases op <;> cases values <;> simp only [applyNonFfi] <;>
    repeat' (split <;> simp_all)
  all_goals try simp_all
  all_goals simp only [apply_ite]
  all_goals split <;> try simp_all
  all_goals split <;> simp_all

private theorem applyNonFfiFields_globalsPtr {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.globOp .globalsPtr) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => cases ptr : state.global <;> simp [applyNonFfi, ptr]
  | cons value rest => simp [applyNonFfi]

private theorem applyNonFfiFields_global {C F : Type} (index : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.globOp (.global index)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil =>
    cases globalEq : state.global with
    | none => simp [applyNonFfi, globalEq]
    | some pointer =>
      cases lookup : sptLookup pointer state.refs with
      | none => simp [applyNonFfi, globalEq, lookup]
      | some entry =>
        cases entry with
        | valueArray contents =>
          cases element : contents[index]? <;> simp [applyNonFfi, globalEq, lookup, element]
        | byteArray _ _ | thunk _ _ | mutBlock _ _ _ _ _ =>
          simp [applyNonFfi, globalEq, lookup]
  | cons value rest => simp [applyNonFfi]

private theorem applyNonFfiFields_setGlobal {C F : Type} (index : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.globOp (.setGlobal index)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest =>
    cases rest with
    | cons value' rest => simp [applyNonFfi]
    | nil =>
      cases globalEq : state.global with
      | none => simp [applyNonFfi, globalEq]
      | some pointer =>
        cases lookup : sptLookup pointer state.refs with
        | none => simp [applyNonFfi, globalEq, lookup]
        | some entry =>
          cases entry with
          | valueArray contents =>
            by_cases bound : index < contents.length <;> simp [applyNonFfi, globalEq, lookup, bound]
          | byteArray _ _ | thunk _ _ | mutBlock _ _ _ _ _ =>
            simp [applyNonFfi, globalEq, lookup]

private theorem applyNonFfiFields_allocGlobal {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.globOp .allocGlobal) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values <;> simp [applyNonFfi]

private theorem applyNonFfiFields_setGlobalsPtr {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.globOp .setGlobalsPtr) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest =>
    cases rest with
    | cons value' rest => simp [applyNonFfi]
    | nil =>
      cases value <;> simp [applyNonFfi]
      all_goals split <;> simp_all

private theorem applyNonFfiFields_globalOp {C F : Type} (op : ClosLang.GlobOp) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.globOp op) values := by
  cases op with
  | global index => exact applyNonFfiFields_global index values
  | setGlobal index => exact applyNonFfiFields_setGlobal index values
  | allocGlobal => exact applyNonFfiFields_allocGlobal values
  | globalsPtr => exact applyNonFfiFields_globalsPtr values
  | setGlobalsPtr => exact applyNonFfiFields_setGlobalsPtr values

private theorem applyNonFfiFields_constant {C F : Type} (constant : ClosLang.Const) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.constant constant)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values <;> simp [applyNonFfi]

private theorem applyNonFfiFields_tagEq {C F : Type} (tag : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.tagEq tag)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest => cases rest <;> cases value <;> simp [applyNonFfi]

private theorem applyNonFfiFields_lenEq {C F : Type} (length : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.lenEq length)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest => cases rest <;> cases value <;> simp [applyNonFfi]

private theorem applyNonFfiFields_tagLenEq {C F : Type} (tag length : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.tagLenEq tag length)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest => cases rest <;> cases value <;> simp [applyNonFfi]

private theorem applyNonFfiFields_lengthBlock {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp .lengthBlock) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest => cases rest <;> cases value <;> simp [applyNonFfi]

private theorem applyNonFfiFields_build {C F : Type} (parts : List ClosLang.ConstPart) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.build parts)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil =>
    cases built : doBuildConst parts state.refs state.tstamps with
    | mk value rest =>
      cases rest with
      | mk refs stamps => simp [applyNonFfi, built]
  | cons value rest => simp [applyNonFfi]

private theorem applyNonFfiFields_boolNot {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp .boolNot) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest =>
    cases rest with
    | cons value' rest => simp [applyNonFfi]
    | nil => cases result : destBool value <;> simp [applyNonFfi, result]

private theorem applyNonFfiFields_boolTest {C F : Type} (test : AstHOL.Test) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.boolTest test)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil =>
        cases a : destBool first <;> cases b : destBool second <;> simp [applyNonFfi, a, b]

private theorem applyNonFfiFields_equal {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp .equal) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil => cases result : doEq state.refs first second <;> simp [applyNonFfi, result]

private theorem applyNonFfiFields_boundsCheckBlock {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp .boundsCheckBlock) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil => cases first <;> cases second <;> simp [applyNonFfi]

private theorem applyNonFfiFields_cons {C F : Type} (tag : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.cons tag)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest =>
    cases stamps : state.tstamps <;> simp [applyNonFfi, withFreshTimestamp, checkLim, stamps]

private theorem applyNonFfiFields_fromList {C F : Type} (tag : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.fromList tag)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil =>
        cases first with
        | number length =>
          cases converted : valueToList second with
          | none => simp [applyNonFfi, converted]
          | some items =>
            by_cases lengthEq : length = (items.length : Int)
            · cases items with
              | nil => simp [applyNonFfi, converted, lengthEq]
              | cons item items =>
                cases stamps : state.tstamps <;>
                  simp [applyNonFfi, converted, lengthEq, withFreshTimestamp, checkLim, stamps]
            · simp [applyNonFfi, converted, lengthEq]
        | word64 _ | block _ _ _ | refPtr _ _ | codePtr _ => simp [applyNonFfi]

private theorem applyNonFfiFields_listAppend {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp .listAppend) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil =>
        cases a : valueToList first <;> cases b : valueToList second <;>
          cases stamps : state.tstamps <;>
            simp [applyNonFfi, a, b, withFreshTimestamp, checkLim, stamps]

private theorem applyNonFfiFields_elemAt {C F : Type} (index : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.elemAt index)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest =>
    cases rest with
    | cons extra rest => simp [applyNonFfi]
    | nil =>
      cases value with
      | block stamp tag contents =>
        cases item : contents[index]? <;> simp [applyNonFfi, item]
      | refPtr bit pointer =>
        cases lookup : sptLookup pointer state.refs with
        | none => simp [applyNonFfi, lookup]
        | some entry =>
          cases entry with
          | valueArray contents => cases item : contents[index]? <;> simp [applyNonFfi, lookup, item]
          | byteArray _ _ | thunk _ _ | mutBlock _ _ _ _ _ => simp [applyNonFfi, lookup]
      | number _ | word64 _ | codePtr _ => simp [applyNonFfi]

private theorem applyNonFfiFields_equalConst {C F : Type} (constant : ClosLang.ConstPart) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.equalConst constant)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => cases constant <;> simp [applyNonFfi]
  | cons value rest =>
    cases rest with
    | cons extra rest => cases constant <;> simp [applyNonFfi]
    | nil =>
      cases constant with
      | con tag fields => cases value <;> simp [applyNonFfi]
      | int number => cases value <;> simp [applyNonFfi]
      | w64 word => cases value <;> simp [applyNonFfi]
      | str text =>
        cases value with
        | refPtr bit pointer =>
          cases lookup : sptLookup pointer state.refs with
          | none => simp [applyNonFfi, lookup]
          | some entry =>
            cases entry <;> simp [applyNonFfi, lookup]
            all_goals split <;> simp_all
        | number _ | word64 _ | block _ _ _ | codePtr _ => simp [applyNonFfi]

private theorem applyNonFfiFields_consExtend {C F : Type} (tag : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp (.consExtend tag)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩ <;>
    try simp [applyNonFfi]
  cases first <;> try simp
  case block timestamp previousTag previous =>
    cases second <;> try simp
    case number lower =>
      cases third <;> try simp
      case number length =>
        cases fourth <;> try simp
        case number total =>
          cases stamps : state.tstamps <;>
            simp [withFreshTimestamp, checkLim, stamps, apply_ite] <;> split <;> omega

private theorem applyNonFfiFields_block {C F : Type} (op : ClosLang.BlockOp) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.blockOp op) values := by
  cases op with
  | cons tag => exact applyNonFfiFields_cons tag values
  | elemAt index => exact applyNonFfiFields_elemAt index values
  | tagLenEq tag length => exact applyNonFfiFields_tagLenEq tag length values
  | lenEq length => exact applyNonFfiFields_lenEq length values
  | tagEq tag => exact applyNonFfiFields_tagEq tag values
  | lengthBlock => exact applyNonFfiFields_lengthBlock values
  | boolTest test => exact applyNonFfiFields_boolTest test values
  | boolNot => exact applyNonFfiFields_boolNot values
  | boundsCheckBlock => exact applyNonFfiFields_boundsCheckBlock values
  | consExtend tag => exact applyNonFfiFields_consExtend tag values
  | fromList tag => exact applyNonFfiFields_fromList tag values
  | listAppend => exact applyNonFfiFields_listAppend values
  | constant value => exact applyNonFfiFields_constant value values
  | equal => exact applyNonFfiFields_equal values
  | equalConst value => exact applyNonFfiFields_equalConst value values
  | build parts => exact applyNonFfiFields_build parts values

private theorem applyNonFfiFields_ref {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .ref) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  simp [applyNonFfi]

private theorem applyNonFfiFields_refArray {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .refArray) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;> try simp [applyNonFfi]
  cases first <;> simp [apply_ite]

private theorem applyNonFfiFields_refByte {C F : Type} (flag : Bool) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp (.refByte flag)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;> try simp [applyNonFfi]
  cases first <;> try simp
  case number count =>
    cases second <;> try simp
    case number byte =>
      cases result : ClosSem.intToByte byte <;> simp [apply_ite]

private theorem applyNonFfiFields_concatByteVec {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .concatByteVec) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values <;> simp [applyNonFfi]

private theorem applyNonFfiFields_fromListByte {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .fromListByte) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values <;> simp [applyNonFfi]

private theorem applyNonFfiFields_toListByte {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .toListByte) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values <;> simp [applyNonFfi]

private theorem applyNonFfiFields_lengthByteVec {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .lengthByteVec) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values <;> simp [applyNonFfi]

private theorem applyNonFfiFields_derefByteVec {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .derefByteVec) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values <;> simp [applyNonFfi]

private theorem applyNonFfiFields_copyByteTrue {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp (.copyByte true)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values <;> simp [applyNonFfi]

private theorem applyNonFfiFields_configGC {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .configGC) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;> try simp [applyNonFfi]
  cases first <;> cases second <;> simp

private theorem applyNonFfiFields_mutCons {C F : Type} (tag index : Nat) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp (.mutCons tag index)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases child : values[index]? <;> simp [applyNonFfi, child]

private theorem applyNonFfiFields_finaliseCons {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .finaliseCons) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest =>
    cases rest with
    | cons extra rest => simp [applyNonFfi]
    | nil =>
      cases result : finaliseCons value state.refs state.tstamps with
      | none => simp [applyNonFfi, result]
      | some entry =>
        obtain ⟨value', refs, stamps⟩ := entry
        simp [applyNonFfi, result]

private theorem applyNonFfiFields_length {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .length) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest =>
    cases rest with
    | cons extra rest => simp [applyNonFfi]
    | nil =>
      cases value with
      | refPtr bit pointer =>
        cases lookup : sptLookup pointer state.refs with
        | none => simp [applyNonFfi, lookup]
        | some entry => cases entry <;> simp [applyNonFfi, lookup]
      | number _ | word64 _ | block _ _ _ | codePtr _ => simp [applyNonFfi]

private theorem applyNonFfiFields_lengthByte {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .lengthByte) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons value rest =>
    cases rest with
    | cons extra rest => simp [applyNonFfi]
    | nil =>
      cases value with
      | refPtr bit pointer =>
        cases lookup : sptLookup pointer state.refs with
        | none => simp [applyNonFfi, lookup]
        | some entry => cases entry <;> simp [applyNonFfi, lookup]
      | number _ | word64 _ | block _ _ _ | codePtr _ => simp [applyNonFfi]

private theorem applyNonFfiFields_boundsCheckByte {C F : Type} (loose : Bool) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp (.boundsCheckByte loose)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil =>
        cases first with
        | refPtr bit pointer =>
          cases second with
          | number index =>
            cases lookup : sptLookup pointer state.refs with
            | none => simp [applyNonFfi, lookup]
            | some entry => cases entry <;> simp [applyNonFfi, lookup]
          | word64 _ | block _ _ _ | refPtr _ _ | codePtr _ => simp [applyNonFfi]
        | number _ | word64 _ | block _ _ _ | codePtr _ => simp [applyNonFfi]

private theorem applyNonFfiFields_boundsCheckArray {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .boundsCheckArray) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil =>
        cases first with
        | refPtr bit pointer =>
          cases second with
          | number index =>
            cases lookup : sptLookup pointer state.refs with
            | none => simp [applyNonFfi, lookup]
            | some entry => cases entry <;> simp [applyNonFfi, lookup]
          | word64 _ | block _ _ _ | refPtr _ _ | codePtr _ => simp [applyNonFfi]
        | number _ | word64 _ | block _ _ _ | codePtr _ => simp [applyNonFfi]

private theorem applyNonFfiFields_el {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .el) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil =>
        cases second with
        | number index =>
          cases first with
          | block stamp tag contents =>
            by_cases neg : index < 0
            · simp [applyNonFfi, neg]
            · cases item : contents[index.toNat]? <;> simp [applyNonFfi, neg, item]
          | refPtr bit pointer =>
            cases lookup : sptLookup pointer state.refs with
            | none => simp [applyNonFfi, lookup]
            | some entry =>
              cases entry with
              | valueArray contents =>
                by_cases neg : index < 0
                · simp [applyNonFfi, lookup, neg]
                · cases item : contents[index.toNat]? <;> simp [applyNonFfi, lookup, neg, item]
              | byteArray _ _ | thunk _ _ | mutBlock _ _ _ _ _ => simp [applyNonFfi, lookup]
          | number _ | word64 _ | codePtr _ => simp [applyNonFfi]
        | word64 _ | block _ _ _ | refPtr _ _ | codePtr _ => cases first <;> simp [applyNonFfi]

private theorem applyNonFfiFields_derefByte {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .derefByte) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil =>
        cases first with
        | refPtr bit pointer =>
          cases second with
          | number index =>
            cases lookup : sptLookup pointer state.refs with
            | none => simp [applyNonFfi, lookup]
            | some entry =>
              cases entry with
              | byteArray flag bytes =>
                by_cases neg : index < 0
                · simp [applyNonFfi, lookup, neg]
                · cases item : bytes[index.toNat]? <;> simp [applyNonFfi, lookup, neg, item]
              | valueArray _ | thunk _ _ | mutBlock _ _ _ _ _ => simp [applyNonFfi, lookup]
          | word64 _ | block _ _ _ | refPtr _ _ | codePtr _ => simp [applyNonFfi]
        | number _ | word64 _ | block _ _ _ | codePtr _ => simp [applyNonFfi]

private theorem applyNonFfiFields_stringCmp {C F : Type} (fast : Bool) (cmp : Opb)
    (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp (.stringCmp fast cmp)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases values with
  | nil => simp [applyNonFfi]
  | cons first rest =>
    cases rest with
    | nil => simp [applyNonFfi]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [applyNonFfi]
      | nil =>
        cases first with
        | refPtr bit1 ptr1 =>
          cases second with
          | refPtr bit2 ptr2 =>
            cases left : sptLookup ptr1 state.refs with
            | none => simp [applyNonFfi, left]
            | some entry1 =>
              cases entry1 with
              | byteArray flag1 bytes1 =>
                cases right : sptLookup ptr2 state.refs with
                | none => simp [applyNonFfi, left, right]
                | some entry2 => cases entry2 <;> simp [applyNonFfi, left, right]
              | valueArray _ | thunk _ _ | mutBlock _ _ _ _ _ => simp [applyNonFfi, left]
          | number _ | word64 _ | block _ _ _ | codePtr _ => simp [applyNonFfi]
        | number _ | word64 _ | block _ _ _ | codePtr _ => cases second <;> simp [applyNonFfi]

private theorem applyNonFfiFields_update {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .update) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩ <;>
    try simp [applyNonFfi]
  cases first <;> try simp
  case refPtr bit pointer =>
    cases second <;> try simp
    case number index =>
      cases lookup : sptLookup pointer state.refs with
      | none => simp
      | some entry =>
        cases entry with
        | valueArray contents =>
          by_cases invalid : index < 0 ∨ index.toNat ≥ contents.length <;> simp [invalid]
        | byteArray _ _ | thunk _ _ | mutBlock _ _ _ _ _ => simp

private theorem applyNonFfiFields_updateByte {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .updateByte) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩ <;>
    try simp [applyNonFfi]
  cases first <;> try simp
  case refPtr bit pointer =>
    cases second <;> try simp
    case number index =>
      cases third <;> try simp
      case number byte =>
        cases lookup : sptLookup pointer state.refs with
        | none => simp
        | some entry =>
          cases entry with
          | byteArray flag bytes =>
            by_cases invalid : index < 0 ∨ index.toNat ≥ bytes.length
            · simp [invalid]
            · cases converted : ClosSem.intToByte byte <;> simp [invalid]
          | valueArray _ | thunk _ _ | mutBlock _ _ _ _ _ => simp

private theorem applyNonFfiFields_updateCons {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .updateCons) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩ <;>
    try simp [applyNonFfi]
  cases first <;> try simp
  case refPtr bit pointer =>
    cases second <;> try simp
    case number index =>
      cases lookup : sptLookup pointer state.refs with
      | none => simp
      | some entry =>
        cases entry with
        | mutBlock tag finalised left child right =>
          cases finalised <;> simp [apply_ite]
        | valueArray _ | byteArray _ _ | thunk _ _ => simp

private theorem applyNonFfiFields_xorByte {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp .xorByte) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;> try simp [applyNonFfi]
  cases first <;> try simp
  case refPtr bit1 dst =>
    cases second <;> try simp
    case refPtr bit2 src =>
      cases sourceLookup : sptLookup src state.refs with
      | none => simp
      | some sourceEntry =>
        cases sourceEntry with
        | byteArray sourceFlag source =>
          cases destLookup : sptLookup dst state.refs with
          | none => simp
          | some destEntry =>
            cases destEntry with
            | byteArray destFlag bytes =>
              cases result : xorBytes source bytes <;> simp [result]
            | valueArray _ | thunk _ _ | mutBlock _ _ _ _ _ => simp
        | valueArray _ | thunk _ _ | mutBlock _ _ _ _ _ => simp

private theorem applyNonFfiFields_copyByteFalse {C F : Type} (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp (.copyByte false)) values := by
  intro state stack localsSize mx peak locals space handler clock frameSizes compiler
  rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _ | ⟨fifth, _ | ⟨sixth, rest⟩⟩⟩⟩⟩⟩ <;>
    try simp [applyNonFfi]
  cases first <;> try simp
  case refPtr bit1 src =>
    cases second <;> try simp
    case number offset =>
      cases third <;> try simp
      case number length =>
        cases fourth <;> try simp
        case refPtr bit2 dst =>
          cases fifth <;> try simp
          case number dstOffset =>
            cases sourceLookup : sptLookup src state.refs with
            | none => simp
            | some sourceEntry =>
              cases sourceEntry with
              | byteArray sourceFlag source =>
                cases destLookup : sptLookup dst state.refs with
                | none => simp
                | some destEntry =>
                  cases destEntry with
                  | byteArray destFlag bytes =>
                    cases result : copyArray (source, offset) length (some (bytes, dstOffset)) <;> simp [result]
                  | valueArray _ | thunk _ _ | mutBlock _ _ _ _ _ => simp
              | valueArray _ | thunk _ _ | mutBlock _ _ _ _ _ => simp

private theorem applyNonFfiFields_mem {C F : Type} (op : ClosLang.MemOp) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) (.memOp op) values := by
  cases op with
  | ref => exact applyNonFfiFields_ref values
  | update => exact applyNonFfiFields_update values
  | el => exact applyNonFfiFields_el values
  | length => exact applyNonFfiFields_length values
  | lengthByte => exact applyNonFfiFields_lengthByte values
  | refByte flag => exact applyNonFfiFields_refByte flag values
  | refArray => exact applyNonFfiFields_refArray values
  | derefByte => exact applyNonFfiFields_derefByte values
  | updateByte => exact applyNonFfiFields_updateByte values
  | concatByteVec => exact applyNonFfiFields_concatByteVec values
  | copyByte flag => cases flag <;> first | exact applyNonFfiFields_copyByteTrue values | exact applyNonFfiFields_copyByteFalse values
  | fromListByte => exact applyNonFfiFields_fromListByte values
  | toListByte => exact applyNonFfiFields_toListByte values
  | lengthByteVec => exact applyNonFfiFields_lengthByteVec values
  | derefByteVec => exact applyNonFfiFields_derefByteVec values
  | stringCmp fast cmp => exact applyNonFfiFields_stringCmp fast cmp values
  | xorByte => exact applyNonFfiFields_xorByte values
  | boundsCheckArray => exact applyNonFfiFields_boundsCheckArray values
  | boundsCheckByte loose => exact applyNonFfiFields_boundsCheckByte loose values
  | mutCons tag index => exact applyNonFfiFields_mutCons tag index values
  | updateCons => exact applyNonFfiFields_updateCons values
  | finaliseCons => exact applyNonFfiFields_finaliseCons values
  | configGC => exact applyNonFfiFields_configGC values

private theorem applyNonFfiFields_all {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value) :
    applyNonFfiFields (C := C) (F := F) op values := by
  cases op with
  | intOp op => exact applyNonFfiFields_int op values
  | wordOp op => exact applyNonFfiFields_word op values
  | label label => exact applyNonFfiFields_label label values
  | install => exact applyNonFfiFields_install values
  | ffi name => exact applyNonFfiFields_ffi name values
  | thunkOp op => exact applyNonFfiFields_thunk op values
  | globOp op => exact applyNonFfiFields_globalOp op values
  | blockOp op => exact applyNonFfiFields_block op values
  | memOp op => exact applyNonFfiFields_mem op values

/-- Auxiliary application commutes with changes to fields it does not read.
This Flapjack-specific equation supports the HOL field-swap theorems. -/
theorem doAppAux_withFields {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (stack : List Stack) (localsSize mx : Option Nat)
    (peak : Nat) (locals : Spt DataSem.Value) (space : Nat)
    (handler clock : Nat) (frameSizes : Spt Nat) (compiler : Compiler C) :
    doAppAux op values { state with stack := stack, localsSize := localsSize, stackMax := mx, peakHeapLength := peak, locals := locals, space := space, handler := handler, clock := clock, stackFrameSizes := frameSizes, compile := compiler } =
      Flapjack.SemanticPrimitivesProps.mapResult
        (fun (value, next) => (value, { next with stack := stack, localsSize := localsSize, stackMax := mx, peakHeapLength := peak, locals := locals, space := space, handler := handler, clock := clock, stackFrameSizes := frameSizes, compile := compiler }))
        id (doAppAux op values state) := by
  have fields := applyNonFfiFields_all (C := C) (F := F) op values state stack localsSize mx peak locals space handler clock frameSizes compiler
  cases op with
  | ffi name =>
    rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;>
      try simp [doAppAux, Flapjack.SemanticPrimitivesProps.mapResult,
        Flapjack.SemanticPrimitivesProps.mapErrorResult]
    cases first <;> try simp
    case refPtr configBit configPtr =>
      cases second <;> try simp
      case refPtr dataBit dataPtr =>
        cases configLookup : sptLookup configPtr state.refs with
        | none => simp
        | some configEntry =>
          cases configEntry with
          | byteArray configFlag config =>
            cases configFlag with
            | false => simp
            | true =>
              cases dataLookup : sptLookup dataPtr state.refs with
              | none => simp
              | some dataEntry =>
                cases dataEntry with
                | byteArray dataFlag bytes =>
                  cases dataFlag with
                  | true => simp
                  | false =>
                    cases call : callFFIHOL state.ffi (.extCall name) config bytes <;>
                      simp [call]
                | valueArray _ | thunk _ _ | mutBlock _ _ _ _ _ => simp
          | valueArray _ | thunk _ _ | mutBlock _ _ _ _ _ => simp
  | intOp op =>
    cases app : applyNonFfi (.intOp op) values state <;> cases values <;>
      simp [doAppAux, fields, app, Flapjack.SemanticPrimitivesProps.mapResult,
        Flapjack.SemanticPrimitivesProps.mapErrorResult]
  | wordOp op =>
    cases app : applyNonFfi (.wordOp op) values state <;> cases values <;>
      simp [doAppAux, fields, app, Flapjack.SemanticPrimitivesProps.mapResult,
        Flapjack.SemanticPrimitivesProps.mapErrorResult]
  | label op =>
    cases app : applyNonFfi (.label op) values state <;> cases values <;>
      simp [doAppAux, fields, app, Flapjack.SemanticPrimitivesProps.mapResult,
        Flapjack.SemanticPrimitivesProps.mapErrorResult]
  | install =>
    cases app : applyNonFfi (.install) values state <;> cases values <;>
      simp [doAppAux, fields, app, Flapjack.SemanticPrimitivesProps.mapResult,
        Flapjack.SemanticPrimitivesProps.mapErrorResult]
  | thunkOp op =>
    cases app : applyNonFfi (.thunkOp op) values state <;> cases values <;>
      simp [doAppAux, fields, app, Flapjack.SemanticPrimitivesProps.mapResult,
        Flapjack.SemanticPrimitivesProps.mapErrorResult]
  | globOp op =>
    cases app : applyNonFfi (.globOp op) values state <;> cases values <;>
      simp [doAppAux, fields, app, Flapjack.SemanticPrimitivesProps.mapResult,
        Flapjack.SemanticPrimitivesProps.mapErrorResult]
  | blockOp op =>
    cases app : applyNonFfi (.blockOp op) values state <;> cases values <;>
      simp [doAppAux, fields, app, Flapjack.SemanticPrimitivesProps.mapResult,
        Flapjack.SemanticPrimitivesProps.mapErrorResult]
  | memOp op =>
    cases app : applyNonFfi (.memOp op) values state <;> cases values <;>
      simp [doAppAux, fields, app, Flapjack.SemanticPrimitivesProps.mapResult,
        Flapjack.SemanticPrimitivesProps.mapErrorResult]

/-- Successful auxiliary applications preserve the fields not read by their
dispatcher. This Flapjack-specific helper follows from the field commutation. -/
theorem doAppAux_fieldFrame {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux op values state = .val (value, next)) :
    next.stack = state.stack ∧ next.localsSize = state.localsSize ∧ next.stackMax = state.stackMax ∧
      next.peakHeapLength = state.peakHeapLength ∧ next.locals = state.locals ∧ next.space = state.space ∧
      next.handler = state.handler ∧ next.clock = state.clock ∧
      next.stackFrameSizes = state.stackFrameSizes ∧ next.compile = state.compile := by
  have self := doAppAux_withFields op values state state.stack state.localsSize state.stackMax
    state.peakHeapLength state.locals state.space state.handler state.clock state.stackFrameSizes state.compile
  have same : next = { next with stack := state.stack, localsSize := state.localsSize, stackMax := state.stackMax, peakHeapLength := state.peakHeapLength, locals := state.locals, space := state.space, handler := state.handler, clock := state.clock, stackFrameSizes := state.stackFrameSizes, compile := state.compile } := by
    simpa [run, Flapjack.SemanticPrimitivesProps.mapResult] using self
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only using congrArg (fun s : State C F => s.stack) same
  · simpa only using congrArg (fun s : State C F => s.localsSize) same
  · simpa only using congrArg (fun s : State C F => s.stackMax) same
  · simpa only using congrArg (fun s : State C F => s.peakHeapLength) same
  · simpa only using congrArg (fun s : State C F => s.locals) same
  · simpa only using congrArg (fun s : State C F => s.space) same
  · simpa only using congrArg (fun s : State C F => s.handler) same
  · simpa only using congrArg (fun s : State C F => s.clock) same
  · simpa only using congrArg (fun s : State C F => s.stackFrameSizes) same
  · simpa only using congrArg (fun s : State C F => s.compile) same

/-- Successful auxiliary application preserves the source control and compiler fields. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_const"]
theorem doAppAux_const {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F)
    (run : doAppAux op values state = .val (value, next)) :
    next.stack = state.stack ∧ next.handler = state.handler ∧ next.locals = state.locals ∧
      next.clock = state.clock ∧ next.compile = state.compile := by
  obtain ⟨stack, _, _, _, locals, _, handler, clock, _, compiler⟩ :=
    doAppAux_fieldFrame op values state next value run
  exact ⟨stack, handler, locals, clock, compiler⟩

/-- Auxiliary application commutes with replacing locals. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_with_locals"]
theorem doAppAux_withLocals {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (locals : Spt DataSem.Value) :
    doAppAux op values { state with locals := locals } =
      Flapjack.SemanticPrimitivesProps.mapResult
        (fun (value, next) => (value, { next with locals := locals })) id (doAppAux op values state) := by
  have changed := doAppAux_withFields op values state state.stack state.localsSize state.stackMax
    state.peakHeapLength locals state.space state.handler state.clock state.stackFrameSizes state.compile
  cases run : doAppAux op values state with
  | err error => simpa [run, Flapjack.SemanticPrimitivesProps.mapResult,
      Flapjack.SemanticPrimitivesProps.mapErrorResult] using changed
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have frame := doAppAux_fieldFrame op values state next value run
    simpa [run, Flapjack.SemanticPrimitivesProps.mapResult, frame.1, frame.2.1,
      frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.2.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1,
      frame.2.2.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.2.2] using changed

/-- Auxiliary application commutes with replacing reserved space. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_aux_with_space"]
theorem doAppAux_withSpace {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux op values { state with space := space } =
      Flapjack.SemanticPrimitivesProps.mapResult
        (fun (value, next) => (value, { next with space := space })) id (doAppAux op values state) := by
  have changed := doAppAux_withFields op values state state.stack state.localsSize state.stackMax
    state.peakHeapLength state.locals space state.handler state.clock state.stackFrameSizes state.compile
  cases run : doAppAux op values state with
  | err error => simpa [run, Flapjack.SemanticPrimitivesProps.mapResult,
      Flapjack.SemanticPrimitivesProps.mapErrorResult] using changed
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have frame := doAppAux_fieldFrame op values state next value run
    simpa [run, Flapjack.SemanticPrimitivesProps.mapResult, frame.1, frame.2.1,
      frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1, frame.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.1,
      frame.2.2.2.2.2.2.2.2.1, frame.2.2.2.2.2.2.2.2.2] using changed

end Flapjack.Compiler.Backend.DataProps
