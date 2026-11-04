import Flapjack.Pancake.PanStructs.CompileProgCorrespondence
import Flapjack.Pancake.PanStructs.CompileDeclsExact

/-! Flapjack codec infrastructure for declaration compilation. These
correspondences have no HOL theorem original; they connect production
carriers to the reviewed exact definitions without assuming compiler results. -/
namespace Flapjack
open Pancake.PanLang Basis.Pure.MlString Pancake.PanStructs.CompileShapeExact

private theorem contextStructs_encode (context : StructPassContext) :
    (structPassContextToExact context).structs =
      structContextToCompileShapeExact context.structs := rfl

private theorem legacyProgram_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (program : Prog (BitVec width)) (hp : ProgByteRanged program) :
    progToHOL (structCompileProg context program) =
      compileProgExact (structPassContextToExact context) (progToHOL program) := by
  rw [← structCompileProgExactProduction_eq_legacy context hc hl hg program hp]
  exact structCompileProgExactProduction_encode context hc hl hg program hp

private theorem compiledParams_encode (context : StructContext) (hc : CtxBR context)
    (parameters : List (String × Shape)) (hp : ListParamByteRanged parameters) :
    (parameters.map (fun p => (p.1, structCompileShape context p.2))).map paramToHOL =
      (parameters.map paramToHOL).map
        (fun p => (p.1, compileShapeExact (structContextToCompileShapeExact context) p.2)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro parameter hparameter
  rcases parameter with ⟨name, shape⟩
  simp only [Function.comp_apply, paramToHOL]
  rw [compileShapeExact_encode context shape hc (hp _ hparameter).2]

private theorem declarationList_codec_roundtrip {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hd : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    (declarations.map declToHOL).map declOfHOL = declarations := by
  rw [List.map_map]
  calc
    declarations.map (declOfHOL ∘ declToHOL) = declarations.map id := by
      apply List.map_congr_left
      intro declaration hdeclaration
      exact declOfHOL_declToHOL declaration (hd declaration hdeclaration)
    _ = declarations := List.map_id declarations

/-- The actual declaration compiler output survives the syntax codec roundtrip.
Output ranging is derived internally from the input/context invariants. This is
Flapjack decoder infrastructure with no HOL theorem original. -/
theorem structCompileDecls_codec_roundtrip {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) (context : StructPassContext)
    (hc : CtxBR context.structs)
    (hd : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ((structCompileDecls declarations context).1.map declToHOL).map declOfHOL =
      (structCompileDecls declarations context).1 :=
  declarationList_codec_roundtrip _ (structCompileDecls_byteRanged declarations context hc hd)

end Flapjack
