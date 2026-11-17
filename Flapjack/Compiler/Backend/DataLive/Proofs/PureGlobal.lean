module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PureBlock

@[expose] public section

/-! Pure global reads and dead assignment elimination. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Pure global primitives leave reserved heap space unchanged. -/
theorem pure_global_doSpace {C F : Type} (op : ClosLang.GlobOp) (args : List DataSem.Value)
    (state : State C F) (pure : isPure (.globOp op) = true) : doSpace (.globOp op) args state = some state := by
  cases op <;> simp [isPure] at pure <;> simp [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]

/-- Successful pure global operations leave the auxiliary state unchanged.
This is an untagged part of the pure-operation simulation infrastructure. -/
theorem pure_global_aux_same {C F : Type} (op : ClosLang.GlobOp) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (pure : isPure (.globOp op) = true) (run : doAppAux (.globOp op) args state = .val (value, next)) :
    next = state := by
  cases op <;> simp [isPure] at pure
  case allocGlobal => simp [doAppAux, applyNonFfi] at run
  case globalsPtr =>
    cases args with
    | cons a rest => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases global : state.global with
      | none => simp [doAppAux, applyNonFfi, global] at run
      | some ptr =>
        simp [doAppAux, applyNonFfi, global] at run
        exact run.2.symm
  case global index =>
    cases args with
    | cons a rest => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases global : state.global with
      | none => simp [doAppAux, applyNonFfi, global] at run
      | some ptr =>
        cases found : sptLookup ptr state.refs with
        | none => simp [doAppAux, applyNonFfi, global, found] at run
        | some entry =>
          cases entry with
          | byteArray flag bytes => simp [doAppAux, applyNonFfi, global, found] at run
          | thunk mode v => simp [doAppAux, applyNonFfi, global, found] at run
          | mutBlock tag done left child right => simp [doAppAux, applyNonFfi, global, found] at run
          | valueArray values =>
            cases slot : values[index]? with
            | none => simp [doAppAux, applyNonFfi, global, found, slot] at run
            | some v =>
              simp [doAppAux, applyNonFfi, global, found, slot] at run
              exact run.2.symm

end Flapjack.Compiler.Backend.DataLive
