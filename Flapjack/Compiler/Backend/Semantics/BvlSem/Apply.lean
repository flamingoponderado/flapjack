import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions
import Flapjack.Compiler.Backend.Semantics.BvlSem.Thunk
import Flapjack.HolRef

/-! BVL installation and primitive application. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

namespace InstallCarrier
/-- Canonical finite-map state representation roundtrip for installation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InstallCarrier

/-- Install code only when the decoded buffers and shifted compiler oracle
agree with the callback, preserving the original disjointness checks. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "do_install_def"
  (fmap_as_finite_support := [refs])]
noncomputable def doInstall {C F R : Type} (args : List Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) :
    Result (Value × Flapjack.Compiler.Backend.BvlSem.State C F) R := by
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

/-- BVL primitive application, including installation, FFI and thunk cases. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "do_app_def"
  (fmap_as_finite_support := [refs])]
noncomputable def doApp {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s : Flapjack.Compiler.Backend.BvlSem.State C F) :
    Result (Value × Flapjack.Compiler.Backend.BvlSem.State C F) Value := by
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
