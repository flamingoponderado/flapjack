import Flapjack.Pancake.PanStructs.CompileDeclsCorrespondence

/-! Executed top-level PanStructs codec. The wrapper calls the reviewed HOL-shaped
compiler directly; these production-carrier equalities have no HOL original. -/
namespace Flapjack
open Pancake.PanLang Pancake.PanStructs.CompileShapeExact

/-- Execute the reviewed top compiler through the production declaration codecs.
The parser-backed caller supplies the input range invariant for the equality
below. This wrapper has no separate HOL declaration. -/
def structCompileTopHOLExactProduction {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) : List (Decl (BitVec width)) :=
  (compileTopExact (declarations.map declToHOL)).map declOfHOL

/-- Equality at the production boundary, with compiled-output ranging derived
internally by the output roundtrip theorem. No result invariant is assumed. -/
theorem structCompileTopHOLExactProduction_eq_legacy {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hd : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    structCompileTopHOLExactProduction declarations = structCompileTop declarations := by
  unfold structCompileTopHOLExactProduction
  rw [← structCompileTop_encode declarations hd]
  exact structCompileTop_codec_roundtrip declarations hd

/-- Parser-backed boundary for the literal exact top compiler. -/
def structCompileTopHOLExactOfByteRanged {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (_hd : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    List (Decl (BitVec width)) := structCompileTopHOLExactProduction declarations

/-- Flapjack equality used by the parser-backed pipeline caller. -/
theorem structCompileTopHOLExact_eq_legacyOfByteRanged {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hd : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    structCompileTopHOLExactOfByteRanged declarations hd = structCompileTop declarations :=
  structCompileTopHOLExactProduction_eq_legacy declarations hd

end Flapjack
