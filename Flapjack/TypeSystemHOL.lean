module

public import Flapjack.AstHOL.LitOp

@[expose] public section

/-! CakeML semantic type carrier used by inference. -/
namespace Flapjack.TypeSystemHOL
open Flapjack.Basis.Pure.MlString

@[hol "cakeml/semantics/typeSystemScript.sml" "type_ident"]
abbrev TypeIdent := Nat

@[hol "cakeml/semantics/typeSystemScript.sml" "t"]
inductive SemanticT where
  | var : MlString → SemanticT
  | varDb : Nat → SemanticT
  | app : List SemanticT → TypeIdent → SemanticT
  deriving Repr

end Flapjack.TypeSystemHOL

namespace Flapjack.TypeSystemHOL

/-! Primitive type-constructor identifiers and their type abbreviations,
ported from the source definitions `Tarray_num_def` ... `Tdouble_def`. -/

@[hol "cakeml/semantics/typeSystemScript.sml" "Tarray_num_def"]
abbrev TarrayNum : Nat := 0
@[hol "cakeml/semantics/typeSystemScript.sml" "Tbool_num_def"]
abbrev TboolNum : Nat := 1
@[hol "cakeml/semantics/typeSystemScript.sml" "Tchar_num_def"]
abbrev TcharNum : Nat := 2
@[hol "cakeml/semantics/typeSystemScript.sml" "Texn_num_def"]
abbrev TexnNum : Nat := 3
@[hol "cakeml/semantics/typeSystemScript.sml" "Tfn_num_def"]
abbrev TfnNum : Nat := 4
@[hol "cakeml/semantics/typeSystemScript.sml" "Tint_num_def"]
abbrev TintNum : Nat := 5
@[hol "cakeml/semantics/typeSystemScript.sml" "Tlist_num_def"]
abbrev TlistNum : Nat := 6
@[hol "cakeml/semantics/typeSystemScript.sml" "Tref_num_def"]
abbrev TrefNum : Nat := 7
@[hol "cakeml/semantics/typeSystemScript.sml" "Tstring_num_def"]
abbrev TstringNum : Nat := 8
@[hol "cakeml/semantics/typeSystemScript.sml" "Ttup_num_def"]
abbrev TtupNum : Nat := 9
@[hol "cakeml/semantics/typeSystemScript.sml" "Tvector_num_def"]
abbrev TvectorNum : Nat := 10
@[hol "cakeml/semantics/typeSystemScript.sml" "Tword64_num_def"]
abbrev Tword64Num : Nat := 11
@[hol "cakeml/semantics/typeSystemScript.sml" "Tword8_num_def"]
abbrev Tword8Num : Nat := 12
@[hol "cakeml/semantics/typeSystemScript.sml" "Tword8array_num_def"]
abbrev Tword8arrayNum : Nat := 13
@[hol "cakeml/semantics/typeSystemScript.sml" "Tdouble_num_def"]
abbrev TdoubleNum : Nat := 14

@[hol "cakeml/semantics/typeSystemScript.sml" "Tarray_def"]
abbrev Tarray (t : SemanticT) : SemanticT := SemanticT.app [t] TarrayNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tbool_def"]
abbrev Tbool : SemanticT := SemanticT.app [] TboolNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tchar_def"]
abbrev Tchar : SemanticT := SemanticT.app [] TcharNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Texn_def"]
abbrev Texn : SemanticT := SemanticT.app [] TexnNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tfn_def"]
abbrev Tfn (t₁ t₂ : SemanticT) : SemanticT := SemanticT.app [t₁, t₂] TfnNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tint_def"]
abbrev Tint : SemanticT := SemanticT.app [] TintNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tlist_def"]
abbrev Tlist (t : SemanticT) : SemanticT := SemanticT.app [t] TlistNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tref_def"]
abbrev Tref (t : SemanticT) : SemanticT := SemanticT.app [t] TrefNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tstring_def"]
abbrev Tstring : SemanticT := SemanticT.app [] TstringNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Ttup_def"]
abbrev Ttup (ts : List SemanticT) : SemanticT := SemanticT.app ts TtupNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tvector_def"]
abbrev Tvector (t : SemanticT) : SemanticT := SemanticT.app [t] TvectorNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tword64_def"]
abbrev Tword64 : SemanticT := SemanticT.app [] Tword64Num
@[hol "cakeml/semantics/typeSystemScript.sml" "Tword8_def"]
abbrev Tword8 : SemanticT := SemanticT.app [] Tword8Num
@[hol "cakeml/semantics/typeSystemScript.sml" "Tword8array_def"]
abbrev Tword8array : SemanticT := SemanticT.app [] Tword8arrayNum
@[hol "cakeml/semantics/typeSystemScript.sml" "Tdouble_def"]
abbrev Tdouble : SemanticT := SemanticT.app [] TdoubleNum

end Flapjack.TypeSystemHOL
