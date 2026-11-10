module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

@[expose] public section

/-! Source-shaped list, string, vector, thunk and FFI primitive cases. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL
open Flapjack.Basis.Pure.MlString

/-- Implode accepts one valid list of character literals. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_implode_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .implode) vs = match vs with
      | [v] => (valueToCharList v).map fun chars => (s, .val (.litv (.strLit (.implode chars))))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all

/-- Explode encodes the characters of a single string as a flat list. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_explode_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .explode) vs = match vs with
      | [.litv (.strLit str)] => some (s, .val (listToValue (str.explode.map (.litv ∘ Lit.char))))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData] <;> rfl

/-- String indexing raises the source subscript exception on bad bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_strsub_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .strsub) vs = match vs with
      | [.litv (.strLit str), .litv (.intLit i)] =>
        if i < 0 then some (s, .err (.raise subscriptExnV)) else
        match str.explode[i.toNat]? with
        | none => some (s, .err (.raise subscriptExnV))
        | some c => some (s, .val (.litv (.char c)))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, readIndexed, boundsFailure]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- String length counts HOL characters. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_strlen_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .strlen) vs = match vs with
      | [.litv (.strLit str)] => some (s, .val (.litv (.intLit str.explode.length)))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData] <;> rfl

/-- Concatenation decodes a flat list and rejects non-string elements. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_strcat_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .strcat) vs = match vs with
      | [v] => do
        let parts ← valueToList v
        let str ← valuesToString parts
        some (s, .val (.litv (.strLit str)))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData] <;> rfl

/-- Vector creation decodes the original flat list representation. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_vfromList_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .vfromList) vs = match vs with
      | [v] => (valueToList v).map fun values => (s, .val (.vectorv values))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all

/-- Safe vector indexing raises the source subscript exception on bad bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_vsub_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .vsub) vs = match vs with
      | [.vectorv xs, .litv (.intLit i)] => if i < 0 then some (s, .err (.raise subscriptExnV)) else
        match xs[i.toNat]? with | none => some (s, .err (.raise subscriptExnV)) | some v => some (s, .val v)
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, readIndexed, boundsFailure]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Unsafe vector indexing fails on bad bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_vsubUnsafe_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .vsubUnsafe) vs = match vs with
      | [.vectorv xs, .litv (.intLit i)] => if i < 0 then none else
        match xs[i.toNat]? with | none => none | some v => some (s, .val v)
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, readIndexed, boundsFailure]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Vector length accepts precisely one vector. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_vlength_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .vlength) vs = match vs with
      | [.vectorv xs] => some (s, .val (.litv (.intLit xs.length)))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData] <;> rfl

/-- List append decodes both lists before constructing the result. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_listAppend_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .listAppend) vs = match vs with
      | [x, y] => do
        let left ← valueToList x
        let right ← valueToList y
        some (s, .val (listToValue (left ++ right)))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData] <;> rfl

/-- GC configuration accepts exactly two integer literals and returns unit. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_configGC_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .configGC) vs = match vs with
      | [.litv (.intLit _), .litv (.intLit _)] => some (s, .val unitValue)
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData] <;> rfl

/-- Thunk allocation and update preserve the original invalid-update checks. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_thunk_source {C F : Type} (s : State C F) (op : ThunkOp) (vs : List Value) :
    doApp s (.src (.thunkOp op)) vs = match op, vs with
      | .allocThunk mode, [v] =>
        if badThunkUpdate mode v s.refs then none else
        let (refs, n) := storeAlloc (.thunk mode v) s.refs
        some ({ s with refs := refs }, .val (.loc false n))
      | .updateThunk mode, [.loc false n, v] =>
        if badThunkUpdate mode v s.refs then none else
        (storeAssign n (.thunk mode v) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
      | _, _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- FFI calls update the byte store and FFI state on return, or propagate the
original final event without updating the state. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_ffi_source {C F : Type} (s : State C F) (name : MlString) (vs : List Value) :
    doApp s (.src (.ffi name)) vs = match vs with
      | [.litv (.strLit conf), .loc _ n] => match storeLookup n s.refs with
        | some (.w8array bytes) => match callFFIHOL s.ffi (.extCall name) conf.explode bytes with
          | .final event => some (s, .err (.abort (.ffiError event)))
          | .ret ffi output => (storeAssign n (.w8array output) s.refs).map fun refs =>
              ({ s with refs := refs, ffi := ffi }, .val unitValue)
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

end Flapjack.Compiler.Backend.FlatSem
