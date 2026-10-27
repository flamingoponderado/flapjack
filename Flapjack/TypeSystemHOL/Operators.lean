import Flapjack.TypeSystemHOL.Patterns

/-! Declarative primitive-operator typing from the source type system.
These rules are separate from the executable inference implementation. -/
namespace Flapjack.TypeSystemHOL
open Flapjack.AstHOL

@[hol "cakeml/semantics/typeSystemScript.sml" "t_of_def"]
def typeOf : PrimType → SemanticT
  | .boolT => .app [] 1
  | .intT => .app [] 5
  | .charT => .app [] 2
  | .strT => .app [] 8
  | .wordT .w8 => .app [] 12
  | .wordT .w64 => .app [] 11
  | .float64T => .app [] 14

@[hol "cakeml/semantics/typeSystemScript.sml" "supported_test_def"]
def supportedTest (test : Test) (ty : PrimType) : Bool :=
  match test with
  | .equal => true
  | .compare _ => ty ∈ [PrimType.intT, .charT, .wordT .w8, .float64T, .strT]
  | .altCompare _ => ty == .strT

@[hol "cakeml/semantics/typeSystemScript.sml" "supported_arith_def"]
def supportedArith (op : Arith) : PrimType → Option Nat
  | .intT => if op ∈ [Arith.add, .sub, .mul, .div, .mod] then some 2 else none
  | .float64T => if op ∈ [Arith.abs, .neg, .sqrt] then some 1
    else if op ∈ [Arith.add, .sub, .mul, .div] then some 2
    else if op == .fma then some 3 else none
  | .wordT _ => if op ∈ [Arith.add, .sub, .and, .or, .xor] then some 2 else none
  | .boolT => if op == .not then some 1 else none
  | _ => none

@[hol "cakeml/semantics/typeSystemScript.sml" "supported_conversion_def"]
def supportedConversion : PrimType → PrimType → Bool
  | .wordT _, .intT | .intT, .wordT _ | .charT, .intT | .intT, .charT
  | .charT, .wordT .w8 | .wordT .w8, .charT | .float64T, .wordT .w64
  | .wordT .w64, .float64T => true
  | _, _ => false

@[hol "cakeml/semantics/typeSystemScript.sml" "type_op_def"]
def typeOp (op : Op) (ts : List SemanticT) (t : SemanticT) : Prop :=
  match op, ts with
  | .opapp, [t₁, t₂] => t₁ = .app [t₂, t] 4
  | .shift .w8 _ _, [t₁] => t₁ = .app [] 12 ∧ t = .app [] 12
  | .shift .w64 _ _, [t₁] => t₁ = .app [] 11 ∧ t = .app [] 11
  | .equality, [t₁, t₂] => t₁ = t₂ ∧ t = .app [] 1
  | .arith a ty, args => (∀ arg, arg ∈ args → arg = typeOf ty) ∧ t = typeOf ty ∧
      supportedArith a ty = some args.length
  | .fromTo fromTy toTy, [t₁] => t₁ = typeOf fromTy ∧ t = typeOf toTy ∧ supportedConversion fromTy toTy = true
  | .test test ty, [t₁, t₂] => t₁ = t₂ ∧ t = .app [] 1 ∧ t₁ = typeOf ty ∧ supportedTest test ty = true
  | .opassign, [t₁, t₂] => t₁ = .app [t₂] 7 ∧ t = .app [] 9
  | .opref, [t₁] => t = .app [t₁] 7
  | .opderef, [t₁] => t₁ = .app [t] 7
  | .aw8alloc, [t₁, t₂] => t₁ = .app [] 5 ∧ t₂ = .app [] 12 ∧ t = .app [] 13
  | .aw8sub, [t₁, t₂] => t₁ = .app [] 13 ∧ t₂ = .app [] 5 ∧ t = .app [] 12
  | .aw8length, [t₁] => t₁ = .app [] 13 ∧ t = .app [] 5
  | .aw8update, [t₁, t₂, t₃] => t₁ = .app [] 13 ∧ t₂ = .app [] 5 ∧ t₃ = .app [] 12 ∧ t = .app [] 9
  | .copyStrStr, [t₁, t₂, t₃] => t₁ = .app [] 8 ∧ t₂ = .app [] 5 ∧ t₃ = .app [] 5 ∧ t = .app [] 8
  | .copyStrAw8, [t₁, t₂, t₃, t₄, t₅] =>
    t₁ = .app [] 8 ∧ t₂ = .app [] 5 ∧ t₃ = .app [] 5 ∧ t₄ = .app [] 13 ∧ t₅ = .app [] 5 ∧ t = .app [] 9
  | .copyAw8Str, [t₁, t₂, t₃] => t₁ = .app [] 13 ∧ t₂ = .app [] 5 ∧ t₃ = .app [] 5 ∧ t = .app [] 8
  | .copyAw8Aw8, [t₁, t₂, t₃, t₄, t₅] =>
    t₁ = .app [] 13 ∧ t₂ = .app [] 5 ∧ t₃ = .app [] 5 ∧ t₄ = .app [] 13 ∧ t₅ = .app [] 5 ∧ t = .app [] 9
  | .implode, [t₁] => t₁ = .app [.app [] 2] 6 ∧ t = .app [] 8
  | .explode, [t₁] => t₁ = .app [] 8 ∧ t = .app [.app [] 2] 6
  | .strsub, [t₁, t₂] => t₁ = .app [] 8 ∧ t₂ = .app [] 5 ∧ t = .app [] 2
  | .strlen, [t₁] => t₁ = .app [] 8 ∧ t = .app [] 5
  | .strcat, [t₁] => t₁ = .app [.app [] 8] 6 ∧ t = .app [] 8
  | .vfromList, [.app [t₁] ctor] => ctor = 6 ∧ t = .app [t₁] 10
  | .vsub, [t₁, t₂] => t₂ = .app [] 5 ∧ .app [t] 10 = t₁
  | .vlength, [.app [_] ctor] => ctor = 10 ∧ t = .app [] 5
  | .aalloc, [t₁, t₂] => t₁ = .app [] 5 ∧ t = .app [t₂] 0
  | .aallocEmpty, [t₁] => t₁ = .app [] 9 ∧ ∃ t₂, t = .app [t₂] 0
  | .asub, [t₁, t₂] => t₂ = .app [] 5 ∧ .app [t] 0 = t₁
  | .alength, [.app [_] ctor] => ctor = 0 ∧ t = .app [] 5
  | .aupdate, [t₁, t₂, t₃] => t₁ = .app [t₃] 0 ∧ t₂ = .app [] 5 ∧ t = .app [] 9
  | .configGC, [t₁, t₂] => t₁ = .app [] 5 ∧ t₂ = .app [] 5 ∧ t = .app [] 9
  | .ffi _, [t₁, t₂] => t₁ = .app [] 8 ∧ t₂ = .app [] 13 ∧ t = .app [] 9
  | .listAppend, [.app [t₁] ctor, t₂] => ctor = 6 ∧ t₂ = .app [t₁] ctor ∧ t = t₂
  | _, _ => False

end Flapjack.TypeSystemHOL
