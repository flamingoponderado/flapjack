module

public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyEquality
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyBuild
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyWord
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyInt
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyGlobals
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyLabel
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyFinalise
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyRef
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyMutCons
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyThunk
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyArrayUpdate
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyFfi
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyList
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyBlockExtend
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyElemAt
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyByteRead
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyBool
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyBlockObserve
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyEqualConst
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyConfigGC
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyBounds
public import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyByteOps

@[expose] public section

/-! Primitive application simulation for BVI-to-data correctness. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical
noncomputable section

/-- Flapjack simulation infrastructure for the full data dispatcher. This
also handles `CopyByte`, which the separate original HOL theorem excludes. -/
theorem doApp_projection {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (args : List DataSem.Value) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install)
    (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (related : stateRel source target)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doAppAux op args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  cases op with
  | install => exact False.elim (notInstall rfl)
  | label label => exact doApp_label label args source target related result next run
  | ffi name => exact doApp_ffi name args source target related result next run
  | intOp op => exact doApp_int op args source target related result next run
  | wordOp op =>
    apply doApp_word op args source target related result next
    · intro h; apply notWordGt; rw [h]
    · intro h; apply notWordGeq; rw [h]
    · exact run
  | blockOp op =>
    cases op with
    | cons tag => exact doApp_cons tag args source target related result next run
    | elemAt index => exact doApp_elemAt index args source target related result next run
    | tagLenEq tag length => exact doApp_tagLenEq tag length args source target related result next run
    | lenEq length => exact doApp_lenEq length args source target related result next run
    | tagEq tag => exact doApp_tagEq tag args source target related result next run
    | lengthBlock => exact doApp_lengthBlock args source target related result next run
    | boolTest test => exact doApp_boolTest test args source target related result next run
    | boolNot => exact doApp_boolNot args source target related result next run
    | boundsCheckBlock => exact doApp_boundsCheckBlock args source target related result next run
    | consExtend tag => exact doApp_consExtend tag args source target related result next run
    | fromList tag => exact doApp_fromList tag args source target related result next run
    | listAppend => exact doApp_listAppend args source target related result next run
    | equal => exact doApp_equal args source target related result next run
    | equalConst part => exact doApp_equalConst part args source target related result next run
    | build parts => exact doApp_build parts args source target related result next run
    | constant value =>
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock] at run
  | globOp op =>
    cases op with
    | global index => exact doApp_global index args source target related result next run
    | setGlobal index => exact doApp_setGlobal index args source target related result next run
    | globalsPtr => exact doApp_globalsPtr args source target related result next run
    | setGlobalsPtr => exact doApp_setGlobalsPtr args source target related result next run
    | allocGlobal => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
  | memOp op =>
    cases op with
    | ref => exact doApp_ref args source target related result next run
    | update => exact doApp_update args source target related result next run
    | el => exact doApp_el args source target related result next run
    | length => exact doApp_length args source target related result next run
    | lengthByte => exact doApp_lengthByte args source target related result next run
    | refByte flag => exact doApp_refByte flag args source target related result next run
    | refArray => exact doApp_refArray args source target related result next run
    | derefByte => exact doApp_derefByte args source target related result next run
    | updateByte => exact doApp_updateByte args source target related result next run
    | copyByte flag =>
      cases flag with
      | false => exact doApp_copyByte_false args source target related result next run
      | true => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | stringCmp fast cmp => exact doApp_stringCmp fast cmp args source target related result next run
    | xorByte => exact doApp_xorByte args source target related result next run
    | boundsCheckArray => exact doApp_boundsCheckArray args source target related result next run
    | boundsCheckByte loose => exact doApp_boundsCheckByte loose args source target related result next run
    | mutCons tag index => exact doApp_mutCons tag index args source target related result next run
    | updateCons => exact doApp_updateCons args source target related result next run
    | finaliseCons => exact doApp_finaliseCons args source target related result next run
    | configGC => exact doApp_configGC args source target related result next run
    | concatByteVec | fromListByte | toListByte =>
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux] at run
    | lengthByteVec | derefByteVec =>
      simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory] at run
  | thunkOp op =>
    cases op with
    | allocThunk mode => exact doApp_allocThunk mode args source target related result next run
    | updateThunk mode => exact doApp_updateThunk mode args source target related result next run
    | forceThunk => exact False.elim (notForce rfl)

end
end Flapjack.Compiler.Backend.BviToData
