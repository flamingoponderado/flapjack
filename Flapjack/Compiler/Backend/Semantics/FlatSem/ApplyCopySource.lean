module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

@[expose] public section
/-! Source-shaped string and byte-copy cases of flat primitive application. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- String-to-string copying raises the subscript exception on invalid bounds. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_copyStrStr_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .copyStrStr) vs = match vs with
      | [.litv (.strLit str), .litv (.intLit offset), .litv (.intLit length)] =>
        match copyArray (str.explode, offset) length none with
        | none => some (s, .err (.raise subscriptExnV))
        | some chars => some (s, .val (.litv (.strLit (.implode chars))))
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure]
  split <;> simp_all
  split <;> simp_all

/-- String-to-byte-array copying updates the destination or raises a bounds exception. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_copyStrAw8_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .copyStrAw8) vs = match vs with
      | [.litv (.strLit str), .litv (.intLit off), .litv (.intLit len), .loc _ dst, .litv (.intLit dstOff)] =>
        match storeLookup dst s.refs with
        | some (.w8array bytes) => match copyArray (str.explode, off) len (some (bytes, dstOff)) with
          | none => some (s, .err (.raise subscriptExnV))
          | some copied => (storeAssign dst (.w8array copied) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Byte-array-to-string copying returns the selected bytes or raises a bounds exception. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_copyAw8Str_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .copyAw8Str) vs = match vs with
      | [.loc _ src, .litv (.intLit off), .litv (.intLit len)] =>
        match storeLookup src s.refs with
        | some (.w8array bytes) => match copyArray (bytes, off) len none with
          | none => some (s, .err (.raise subscriptExnV))
          | some copied => some (s, .val (.litv (.strLit (.implode copied))))
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Byte-array copying uses the original source and destination snapshots. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_copyAw8Aw8_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .copyAw8Aw8) vs = match vs with
      | [.loc _ src, .litv (.intLit off), .litv (.intLit len), .loc _ dst, .litv (.intLit dstOff)] =>
        match storeLookup src s.refs, storeLookup dst s.refs with
        | some (.w8array bytes), some (.w8array output) =>
          match copyArray (bytes, off) len (some (output, dstOff)) with
          | none => some (s, .err (.raise subscriptExnV))
          | some copied => (storeAssign dst (.w8array copied) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
        | _, _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, boundsFailure, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Unsafe string XOR fails when the destination is missing or too short. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_xorAw8StrUnsafe_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .xorAw8StrUnsafe) vs = match vs with
      | [.loc _ dst, .litv (.strLit str)] => match storeLookup dst s.refs with
        | some (.w8array bytes) => match xorBytes str.explode bytes with
          | none => none
          | some output => (storeAssign dst (.w8array output) s.refs).map fun refs => ({ s with refs := refs }, .val unitValue)
        | _ => none
      | _ => none := by
  simp [doApp, doAppNumeric, doAppMemory, doAppData, doAppCopy, Option.bind, Option.map]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
end Flapjack.Compiler.Backend.FlatSem
