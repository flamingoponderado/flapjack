import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions
import Flapjack.Compiler.Backend.Semantics.BvlSem.Thunk

/-! BVL installation and primitive application. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

/-- Install code only when the decoded buffers and shifted compiler oracle
agree with the callback, preserving the original disjointness checks. The
source-shaped definition remains untagged because the finite-map reference
checker cannot yet distinguish the imported BVL `State` from other imported
structures with the same name and `refs` field. -/
noncomputable def doInstall {C F R : Type} (args : List Value) (s : State C F) :
    Result (Value × State C F) R := by
  classical
  let fail : Result (Value × State C F) R := .err (.abort .typeError)
  exact match args with
  | [v1, v2] =>
    match valueToBytes v1, valueToWords v2 with
    | some bytes, some data =>
      let (cfg, progs) := s.compileOracle 0
      let newOracle := fun n => s.compileOracle (n + 1)
      if (∀ entry ∈ progs, sptLookup entry.1 s.code = none) ∧
          (progs.map Prod.fst).Nodup then
        match s.compile cfg progs, progs with
        | some (bytes', data', cfg'), (key, _) :: _ =>
          if bytes = bytes' ∧ data = data' ∧ (newOracle 0).1 = cfg' then
            .val (.codePtr key, { s with
              code := sptUnion s.code (sptFromAList progs)
              compileOracle := newOracle })
          else fail
        | _, _ => fail
      else fail
    | _, _ => fail
  | _ => fail

/-- Source-shaped BVL primitive dispatcher. It remains untagged until all
branches have been reviewed against HOL. -/
noncomputable def doApp {C F : Type} (op : ClosLang.Op) (args : List Value) (s : State C F) :
    Result (Value × State C F) Value := by
  classical
  let fail : Result (Value × State C F) Value := .err (.abort .typeError)
  let convert (value : Option (Value × State C F)) := match value with
    | none => fail
    | some pair => Result.val pair
  exact match op with
  | .globOp operation => convert (applyGlobal operation args s)
  | .blockOp operation => convert (applyBlock operation args s)
  | .memOp operation => convert (applyMemory operation args s)
  | .intOp _ | .wordOp _ => convert (applyNumeric op args s)
  | .install => doInstall args s
  | .label index =>
    match args, sptLookup index s.code with
    | [], some _ => .val (.codePtr index, s)
    | _, _ => fail
  | .ffi name =>
    match args with
    | [.refPtr _ configPtr, .refPtr _ ptr] =>
      match s.refs.lookup configPtr, s.refs.lookup ptr with
      | some (.byteArray true config), some (.byteArray false bytes) =>
        match callFFIHOL s.ffi (.extCall name) config bytes with
        | .ret ffi updated =>
          .val (unitValue, { s with refs := s.refs.updateEq (ptr, .byteArray false updated), ffi := ffi })
        | .final outcome => .err (.abort (.ffiError outcome))
      | _, _ => fail
    | _ => fail
  | .thunkOp operation =>
    match operation, args with
    | .allocThunk mode, [value] =>
      if badThunkUpdate mode value s.refs then fail else
        let ptr := leastUnusedRef s.refs
        .val (.refPtr false ptr, { s with refs := s.refs.updateEq (ptr, .thunk mode value) })
    | .updateThunk mode, [.refPtr false ptr, value] =>
      if badThunkUpdate mode value s.refs then fail else
        match s.refs.lookup ptr with
        | some (.thunk .notEvaluated _) =>
          .val (unitValue, { s with refs := s.refs.updateEq (ptr, .thunk mode value) })
        | _ => fail
    | _, _ => fail
end Flapjack.Compiler.Backend.BvlSem
