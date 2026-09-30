import Flapjack.Pancake.PanStructs.CompileProgCorrespondence

/-! Executed program codec for the reviewed PanStructs program compiler.
This is Flapjack infrastructure for the String-backed production syntax; the
HOL definition is compileProgExact, which this wrapper calls directly. -/
namespace Flapjack
open Pancake.PanLang Pancake.PanStructs.CompileShapeExact

/-- Execute the reviewed program compiler through the production syntax codecs.
The parser-backed caller supplies the byte-range invariants used below. This
wrapper is not a separate HOL declaration and therefore has no HOL tag. -/
def structCompileProgHOLExactProduction {width : Nat} [NeZero width]
    (context : StructPassContext) (program : Prog (BitVec width)) : Prog (BitVec width) :=
  progOfHOL (compileProgExact (structPassContextToExact context) (progToHOL program))

/-- Flapjack codec equality with the recursive production traversal, derived
from the full encoding theorem and the actual compiled-output roundtrip. No
output range or compiler result is assumed. -/
theorem structCompileProgHOLExactProduction_eq_traversal {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (program : Prog (BitVec width)) (hp : ProgByteRanged program) :
    structCompileProgHOLExactProduction context program =
      structCompileProgExactProduction context program := by
  unfold structCompileProgHOLExactProduction
  rw [← structCompileProgExactProduction_encode context hc hl hg program hp]
  exact structCompileProgExactProduction_codec_roundtrip context hc hl hg program hp

/-- Equality at the existing production boundary under actual input invariants.
This Flapjack infrastructure theorem has no HOL original. -/
theorem structCompileProgHOLExactProduction_eq_legacy {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (program : Prog (BitVec width)) (hp : ProgByteRanged program) :
    structCompileProgHOLExactProduction context program = structCompileProg context program := by
  rw [structCompileProgHOLExactProduction_eq_traversal context hc hl hg program hp]
  exact structCompileProgExactProduction_eq_legacy context hc hl hg program hp

end Flapjack
