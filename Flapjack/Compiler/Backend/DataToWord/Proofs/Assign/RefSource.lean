module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Apply

@[expose] public section

/-! Source reference allocation for the data-to-word assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.SemanticPrimitivesHOL

/-- The source reference allocation expands into space consumption followed
by allocation and the original safety and stack accounting. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "do_app_Ref"]
theorem doApp_ref {C F : Type} (values : List DataSem.Value) (source : DataSem.State C F) :
    DataSem.doApp (.memOp .ref) values source =
      match DataSem.consumeSpace (values.length + 1) source with
      | none => .err (.abort .typeError)
      | some s1 =>
        .val (.refPtr true (DataSem.leastUnusedRef s1.refs),
          { s1 with
            refs := sptInsert (DataSem.leastUnusedRef s1.refs) (.valueArray values) s1.refs
            safeForSpace := (DataSem.doStack (.memOp .ref) values
              (DataSem.doLimSafe s1 (.memOp .ref) values)).safeForSpace
            stackMax := (DataSem.doStack (.memOp .ref) values
              (DataSem.doLimSafe s1 (.memOp .ref) values)).stackMax }) := by
  cases h : DataSem.consumeSpace (values.length + 1) source with
  | none =>
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h]
  | some s1 =>
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h,
      DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
