import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Native interference application data. FFI payload bytes have fixed width eight;
cache-clear addresses retain the machine word dimension. Both pre/post states are
arbitrary. The phantom word dimension on an FFI constructor is retained. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "interference_app" (words_as_type_indexed_bitvec)]
inductive InterferenceApp (width : Nat) [NeZero width] (state : Type) where
  | ffiApp (index : Nat) (newBytes : List (BitVec 8)) (pre post : state)
  | ccApp (address length : BitVec width) (pre post : state)

/-- Literal constructor classifier. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "is_ffi_app_def" (words_as_type_indexed_bitvec)]
def isFfiApp {width : Nat} [NeZero width] {state : Type} :
    InterferenceApp width state → Bool
  | .ffiApp _ _ _ _ => true
  | .ccApp _ _ _ _ => false

/-- Literal post-state projection. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "app_post_def" (words_as_type_indexed_bitvec)]
def appPost {width : Nat} [NeZero width] {state : Type} :
    InterferenceApp width state → state
  | .ffiApp _ _ _ post => post
  | .ccApp _ _ _ post => post

end Flapjack.Compiler.Backend.Semantics.TargetProps
