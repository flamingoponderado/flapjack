module

public import Flapjack.TypeSystemHOL.Patterns

@[expose] public section

/-! Declarative primitive-operator typing from the source type system.
These rules are separate from the executable inference implementation. -/
namespace Flapjack.TypeSystemHOL
open Flapjack.AstHOL

@[hol "cakeml/semantics/typeSystemScript.sml" "t_of_def"]
def typeOf : PrimType → SemanticT
  | .boolT => Tbool
  | .intT => Tint
  | .charT => Tchar
  | .strT => Tstring
  | .wordT .w8 => Tword8
  | .wordT .w64 => Tword64
  | .float64T => Tdouble

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
  | .opapp, [t₁, t₂] => t₁ = Tfn t₂ t
  | .shift .w8 _ _, [t₁] => t₁ = Tword8 ∧ t = Tword8
  | .shift .w64 _ _, [t₁] => t₁ = Tword64 ∧ t = Tword64
  | .equality, [t₁, t₂] => t₁ = t₂ ∧ t = Tbool
  | .arith a ty, args => (∀ arg, arg ∈ args → arg = typeOf ty) ∧ t = typeOf ty ∧
      supportedArith a ty = some args.length
  | .fromTo fromTy toTy, [t₁] => t₁ = typeOf fromTy ∧ t = typeOf toTy ∧ supportedConversion fromTy toTy = true
  | .test test ty, [t₁, t₂] => t₁ = t₂ ∧ t = Tbool ∧ t₁ = typeOf ty ∧ supportedTest test ty = true
  | .opassign, [t₁, t₂] => t₁ = Tref t₂ ∧ t = Ttup []
  | .opref, [t₁] => t = Tref t₁
  | .opderef, [t₁] => t₁ = Tref t
  | .aw8alloc, [t₁, t₂] => t₁ = Tint ∧ t₂ = Tword8 ∧ t = Tword8array
  | .aw8sub, [t₁, t₂] => t₁ = Tword8array ∧ t₂ = Tint ∧ t = Tword8
  | .aw8length, [t₁] => t₁ = Tword8array ∧ t = Tint
  | .aw8update, [t₁, t₂, t₃] => t₁ = Tword8array ∧ t₂ = Tint ∧ t₃ = Tword8 ∧ t = Ttup []
  | .copyStrStr, [t₁, t₂, t₃] => t₁ = Tstring ∧ t₂ = Tint ∧ t₃ = Tint ∧ t = Tstring
  | .copyStrAw8, [t₁, t₂, t₃, t₄, t₅] =>
    t₁ = Tstring ∧ t₂ = Tint ∧ t₃ = Tint ∧ t₄ = Tword8array ∧ t₅ = Tint ∧ t = Ttup []
  | .copyAw8Str, [t₁, t₂, t₃] => t₁ = Tword8array ∧ t₂ = Tint ∧ t₃ = Tint ∧ t = Tstring
  | .copyAw8Aw8, [t₁, t₂, t₃, t₄, t₅] =>
    t₁ = Tword8array ∧ t₂ = Tint ∧ t₃ = Tint ∧ t₄ = Tword8array ∧ t₅ = Tint ∧ t = Ttup []
  | .implode, [t₁] => t₁ = Tlist Tchar ∧ t = Tstring
  | .explode, [t₁] => t₁ = Tstring ∧ t = Tlist Tchar
  | .strsub, [t₁, t₂] => t₁ = Tstring ∧ t₂ = Tint ∧ t = Tchar
  | .strlen, [t₁] => t₁ = Tstring ∧ t = Tint
  | .strcat, [t₁] => t₁ = Tlist Tstring ∧ t = Tstring
  | .vfromList, [.app [t₁] ctor] => ctor = TlistNum ∧ t = Tvector t₁
  | .vsub, [t₁, t₂] => t₂ = Tint ∧ Tvector t = t₁
  | .vlength, [.app [_] ctor] => ctor = TvectorNum ∧ t = Tint
  | .aalloc, [t₁, t₂] => t₁ = Tint ∧ t = Tarray t₂
  | .aallocEmpty, [t₁] => t₁ = Ttup [] ∧ ∃ t₂, t = Tarray t₂
  | .asub, [t₁, t₂] => t₂ = Tint ∧ Tarray t = t₁
  | .alength, [.app [_] ctor] => ctor = TarrayNum ∧ t = Tint
  | .aupdate, [t₁, t₂, t₃] => t₁ = Tarray t₃ ∧ t₂ = Tint ∧ t = Ttup []
  | .configGC, [t₁, t₂] => t₁ = Tint ∧ t₂ = Tint ∧ t = Ttup []
  | .ffi _, [t₁, t₂] => t₁ = Tstring ∧ t₂ = Tword8array ∧ t = Ttup []
  | .listAppend, [.app [t₁] ctor, t₂] => ctor = TlistNum ∧ t₂ = .app [t₁] ctor ∧ t = t₂
  | _, _ => False

end Flapjack.TypeSystemHOL
