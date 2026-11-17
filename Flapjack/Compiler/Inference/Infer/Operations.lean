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

@[hol "cakeml/compiler/inference/inferScript.sml" "option_case_rand"]
theorem optionCaseRand {α β γ : Type} (x : Option α) (y : β → γ)
    (f : α → β → γ) (s : β) :
    (match x with | none => y | some a => f a) s =
      match x with | none => y s | some a => f a s := by
  cases x <;> rfl

@[hol "cakeml/compiler/inference/inferScript.sml" "st_ex_bind_failure"]
theorem bindFailure {state value result error : Type}
    (f : M state value error) (g : value → M state result error)
    (s s' : state) (r : error) :
    bind f g s = (.failure r, s') ↔
      f s = (.failure r, s') ∨
        ∃ x st, f s = (.success x, st) ∧ g x st = (.failure r, s') := by
  cases h : f s with
  | mk outcome st =>
    cases outcome <;> simp [Flapjack.Translator.Monadic.MonadBase.bind, h, and_assoc]

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

@[hol "cakeml/compiler/inference/inferScript.sml" "st_ex_bind_pair"]
theorem bindPair {state a b value error : Type} (op : M state (a × b) error)
    (next : a × b → M state value error) :
    bind op next = fun s =>
      match op s with
      | (.success (x, y), s') => next (x, y) s'
      | (.failure e, s') => (.failure e, s') := by
  funext s
  cases h : op s with
  | mk result state => cases result with
    | success pair => cases pair <;> simp [Flapjack.Translator.Monadic.MonadBase.bind, h]
    | failure e => simp [Flapjack.Translator.Monadic.MonadBase.bind, h]

@[hol "cakeml/compiler/inference/inferScript.sml" "st_ex_bind_triple"]
theorem bindTriple {state a b c value error : Type} (op : M state (a × b × c) error)
    (next : a × b × c → M state value error) :
    bind op next = fun s =>
      match op s with
      | (.success (x, y, z), s') => next (x, y, z) s'
      | (.failure e, s') => (.failure e, s') := by
  funext s
  cases h : op s with
  | mk result state => cases result with
    | success triple => rcases triple with ⟨x, y, z⟩; simp [Flapjack.Translator.Monadic.MonadBase.bind, h]
    | failure e => simp [Flapjack.Translator.Monadic.MonadBase.bind, h]

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
