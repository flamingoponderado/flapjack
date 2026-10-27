import Flapjack.AstHOL.Syntax
import Flapjack.FfiHOL

/-! CakeML source-semantics value and store carriers. Statement review is
pending; the source evaluator and compiler correctness theorem are not yet
ported by this module. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.NamespaceHOL

/-- Unique identities for datatype and exception constructors. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "stamp"]
inductive Stamp where
  | typeStamp : ConN → Nat → Stamp
  | exnStamp : Nat → Stamp

/-- Lexical value and constructor environments. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "sem_env"]
structure SemEnv (α : Type) where
  v : Namespace ModN VarN α
  c : Namespace ModN ConN (Nat × Stamp)

/-- CakeML source values, including lexical and recursive closures. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "v"]
inductive Value where
  | litv : Lit → Value
  | conv : Option Stamp → List Value → Value
  | closure : SemEnv Value → VarN → AstHOL.Exp → Value
  | recclosure : SemEnv Value → List (VarN × VarN × AstHOL.Exp) → VarN → Value
  | loc : Bool → Nat → Value
  | vectorv : List Value → Value
  | env : SemEnv Value → (Nat × Nat) → Value

/-- Source-evaluation aborts, including final FFI events. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "abort"]
inductive Abort where
  | typeError
  | timeoutError
  | ffiError : HolFinalEvent → Abort

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "error_result"]
inductive ErrorResult (α : Type) where
  | raise : α → ErrorResult α
  | abort : Abort → ErrorResult α

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "result"]
inductive Result (α β : Type) where
  | val : α → Result α β
  | err : ErrorResult β → Result α β

/-- Source store elements retain HOL's byte words and thunk mode. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_v"]
inductive StoreValue (α : Type) where
  | refv : α → StoreValue α
  | w8array : List (BitVec 8) → StoreValue α
  | varray : List α → StoreValue α
  | thunk : ThunkMode → α → StoreValue α

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_v_same_type_def"]
def storeValueSameType {α : Type} : StoreValue α → StoreValue α → Bool
  | .refv _, .refv _ => true
  | .w8array _, .w8array _ => true
  | .varray _, .varray _ => true
  | .thunk .notEvaluated _, .thunk _ _ => true
  | _, _ => false

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store"]
abbrev Store (α : Type) := List (StoreValue α)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "empty_store_def"]
def emptyStore {α : Type} : Store α := []

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_lookup_def"]
def storeLookup {α : Type} (n : Nat) (store : Store α) : Option (StoreValue α) :=
  store[n]?

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_alloc_def"]
def storeAlloc {α : Type} (value : StoreValue α) (store : Store α) : Store α × Nat :=
  (store ++ [value], store.length)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_assign_def"]
def storeAssign {α : Type} (n : Nat) (value : StoreValue α) (store : Store α) : Option (Store α) := do
  let old ← store[n]?
  if storeValueSameType old value then some (store.set n value) else none

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "bind_stamp_def"]
def bindStamp : Stamp := .exnStamp 0
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "chr_stamp_def"]
def chrStamp : Stamp := .exnStamp 1
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "div_stamp_def"]
def divStamp : Stamp := .exnStamp 2
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "subscript_stamp_def"]
def subscriptStamp : Stamp := .exnStamp 3

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "bind_exn_v_def"]
def bindExnV : Value := .conv (some bindStamp) []
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "chr_exn_v_def"]
def chrExnV : Value := .conv (some chrStamp) []
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "div_exn_v_def"]
def divExnV : Value := .conv (some divStamp) []
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "sub_exn_v_def"]
def subExnV : Value := .conv (some subscriptStamp) []

end Flapjack.SemanticPrimitivesHOL
