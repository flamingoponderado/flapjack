module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

@[expose] public section

/-! Source-shaped reference and array cases of flat primitive application. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- Reference allocation accepts one value. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_opref_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .opref) vs = match vs with
      | [v] => let (refs, n) := storeAlloc (.refv v) s.refs
               some ({ s with refs := refs }, .val (.loc true n))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory] <;> rfl

/-- Reference assignment preserves store type and rejects invalid arguments. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_opassign_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .opassign) vs = match vs with
      | [.loc _ n, v] => (storeAssign n (.refv v) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all <;> rfl

/-- Fixed-size allocation stores its entire argument list in order. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aallocFixed_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aallocFixed) vs =
      let (refs, n) := storeAlloc (.varray vs) s.refs
      some ({ s with refs := refs }, .val (.loc true n)) := by
  simp [doApp, doAppNumeric, doAppMemory] <;> rfl

/-- Value-array allocation rejects negative sizes with a subscript exception. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aalloc_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aalloc) vs = match vs with
      | [.litv (.intLit n), v] => if n < 0 then some (s, .err (.raise subscriptExnV)) else
        let (refs, address) := storeAlloc (.varray (List.replicate n.toNat v)) s.refs
        some ({ s with refs := refs }, .val (.loc true address))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, boundsFailure]
  split <;> simp_all

/-- Byte-array allocation rejects negative sizes with a subscript exception. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aw8alloc_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aw8alloc) vs = match vs with
      | [.litv (.intLit n), .litv (.word8 v)] => if n < 0 then some (s, .err (.raise subscriptExnV)) else
        let (refs, address) := storeAlloc (.w8array (List.replicate n.toNat v)) s.refs
        some ({ s with refs := refs }, .val (.loc true address))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, boundsFailure]
  split <;> simp_all

/-- Value-array length requires a location containing a value array. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_alength_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .alength) vs = match vs with
      | [.loc _ n] => match storeLookup n s.refs with
        | some (.varray xs) => some (s, .val (.litv (.intLit xs.length)))
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory]
  split <;> simp_all
  split <;> simp_all

/-- Byte-array length requires a location containing a byte array. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aw8length_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aw8length) vs = match vs with
      | [.loc _ n] => match storeLookup n s.refs with
        | some (.w8array xs) => some (s, .val (.litv (.intLit xs.length)))
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory]
  split <;> simp_all
  split <;> simp_all

/-- Safe value-array reads raise the source subscript exception on bad bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_asub_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .asub) vs = match vs with
      | [.loc _ n, .litv (.intLit i)] => match storeLookup n s.refs with
        | some (.varray xs) => if i < 0 then some (s, .err (.raise subscriptExnV)) else
          match xs[i.toNat]? with
          | none => some (s, .err (.raise subscriptExnV))
          | some v => some (s, .val v)
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, readIndexed, boundsFailure]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Safe value-array updates check bounds before assigning the updated store. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aupdate_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aupdate) vs = match vs with
      | [.loc _ n, .litv (.intLit i), v] => match storeLookup n s.refs with
        | some (.varray xs) => if i < 0 ∨ xs.length ≤ i.toNat then some (s, .err (.raise subscriptExnV)) else
          (storeAssign n (.varray (xs.set i.toNat v)) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, updateIndexed, boundsFailure, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Unsafe value-array reads fail on bad bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_asubUnsafe_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .asubUnsafe) vs = match vs with
      | [.loc _ n, .litv (.intLit i)] => match storeLookup n s.refs with
        | some (.varray xs) => if i < 0 then none else
          match xs[i.toNat]? with | none => none | some v => some (s, .val v)
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, readIndexed, boundsFailure]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Unsafe value-array updates fail on bad bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aupdateUnsafe_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aupdateUnsafe) vs = match vs with
      | [.loc _ n, .litv (.intLit i), v] => match storeLookup n s.refs with
        | some (.varray xs) => if i < 0 ∨ xs.length ≤ i.toNat then none else
          (storeAssign n (.varray (xs.set i.toNat v)) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, updateIndexed, boundsFailure, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Safe byte-array reads raise the source subscript exception on bad bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aw8sub_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aw8sub) vs = match vs with
      | [.loc _ n, .litv (.intLit i)] => match storeLookup n s.refs with
        | some (.w8array xs) => if i < 0 then some (s, .err (.raise subscriptExnV)) else
          match xs[i.toNat]? with
          | none => some (s, .err (.raise subscriptExnV))
          | some v => some (s, .val (.litv (.word8 v)))
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, readIndexed, boundsFailure]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Unsafe byte-array reads fail on bad bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aw8subUnsafe_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aw8subUnsafe) vs = match vs with
      | [.loc _ n, .litv (.intLit i)] => match storeLookup n s.refs with
        | some (.w8array xs) => if i < 0 then none else
          match xs[i.toNat]? with | none => none | some v => some (s, .val (.litv (.word8 v)))
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, readIndexed, boundsFailure]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Safe byte-array updates check bounds before assigning the updated store. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aw8update_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aw8update) vs = match vs with
      | [.loc _ n, .litv (.intLit i), .litv (.word8 v)] => match storeLookup n s.refs with
        | some (.w8array xs) => if i < 0 ∨ xs.length ≤ i.toNat then some (s, .err (.raise subscriptExnV)) else
          (storeAssign n (.w8array (xs.set i.toNat v)) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, updateIndexed, boundsFailure, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Unsafe byte-array updates fail on bad bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_aw8updateUnsafe_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .aw8updateUnsafe) vs = match vs with
      | [.loc _ n, .litv (.intLit i), .litv (.word8 v)] => match storeLookup n s.refs with
        | some (.w8array xs) => if i < 0 ∨ xs.length ≤ i.toNat then none else
          (storeAssign n (.w8array (xs.set i.toNat v)) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, updateIndexed, boundsFailure, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

end Flapjack.Compiler.Backend.FlatSem
