module

public import Flapjack.Compiler.Inference.InferT.Display
public import Flapjack.Misc.Location
public import Flapjack.Translator.Monadic.MonadBase

@[expose] public section

/-! Generic inference state-and-exception operations and diagnostics. -/
namespace Flapjack.Compiler.Inference.Infer.Operations
open Flapjack.TypeSystemHOL Flapjack.NamespaceHOL Flapjack.Misc.Location
  Flapjack.Basis.Pure.MlString Flapjack.Translator.Monadic.MonadBase
  Flapjack.Compiler.Inference.InferTDisplay

@[hol "cakeml/compiler/inference/inferScript.sml" "err_var"]
abbrev ErrVar := TenvAbbrev

@[hol "cakeml/compiler/inference/inferScript.sml" "loc_err_info"]
structure LocErrInfo where
  loc : Option Locs
  err : ErrVar

@[hol "cakeml/compiler/inference/inferScript.sml" "failwith_def"]
def failwith {state value error : Type} (l : LocErrInfo) (msg : error) :
    M state value (Option Locs × error) :=
  fun s => (.failure (l.loc, msg), s)

@[hol "cakeml/compiler/inference/inferScript.sml" "guard_def"]
def guard {state error : Type} (p : Bool) (l : LocErrInfo) (msg : error) :
    M state Unit (Option Locs × error) :=
  if p then ret () else failwith l msg

@[hol "cakeml/compiler/inference/inferScript.sml" "bind_guard"]
theorem bindGuard {state value error : Type} (p : Bool) (l : LocErrInfo) (msg : error)
    (next : Unit → M state value (Option Locs × error)) :
    bind (guard p l msg) next = fun s =>
      if p then next () s else (.failure (l.loc, msg), s) := by
  cases p <;> rfl

@[hol "cakeml/compiler/inference/inferScript.sml" "ignore_bind_guard"]
theorem ignoreBindGuard {state value error : Type} (p : Bool) (l : LocErrInfo) (msg : error)
    (next : M state value (Option Locs × error)) :
    ignoreBind (guard p l msg) next = fun s =>
      if p then next s else (.failure (l.loc, msg), s) := by
  cases p <;> rfl

@[hol "cakeml/compiler/inference/inferScript.sml" "read_def"]
def read {state error : Type} : M state state error :=
  fun s => (.success s, s)

@[hol "cakeml/compiler/inference/inferScript.sml" "write_def"]
def write {state error : Type} (v : state) : M state Unit error :=
  fun _ => (.success (), v)

@[hol "cakeml/compiler/inference/inferScript.sml" "lookup_st_ex_def"]
def lookupStEx {state value : Type} (l : LocErrInfo) (kind : MlString)
    (id : Ident MlString MlString) (env : Namespace MlString MlString value) :
    M state value (Option Locs × MlString) :=
  fun st => match nsLookup env id with
    | none => (.failure (l.loc, MlString.concat [ofString "Undefined ", kind, ofString ": ", idToString id]), st)
    | some v => (.success v, st)

end Flapjack.Compiler.Inference.Infer.Operations
