import Flapjack.Pancake.PanStructs.CompileProgCorrespondence
import Flapjack.Pancake.PanStructs.CompileDeclsExact

/-! Flapjack codec infrastructure for declaration compilation. These
correspondences have no HOL theorem original; they connect production
carriers to the reviewed exact definitions without assuming compiler results. -/
namespace Flapjack
open Pancake.PanLang Basis.Pure.MlString Pancake.PanStructs.CompileShapeExact

/-- Structure-name collection commutes with the context/declaration codecs.
The left-to-right traversal prepends every name, so duplicate declarations
retain the same shadowing order. Locals and globals are carried unchanged.
No name-range premise is needed: this operation does not compare names. -/
theorem structGetNames_encode {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) (context : StructPassContext) :
    structPassContextToExact (structGetNames context declarations) =
      Pancake.PanStructs.CompileShapeExact.getNamesExact
        (structPassContextToExact context) (declarations.map declToHOL) := by
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration with
      | name name fields =>
          have hfields : fields.map paramToHOL =
              fields.map (fun p => (ofString p.1, shapeToHOL p.2)) := by
            apply List.map_congr_left
            intro p _
            cases p
            rfl
          simpa only [structGetNames, List.foldl_cons, List.map_cons, declToHOL,
            Pancake.PanStructs.CompileShapeExact.getNamesExact,
            structPassContextToExact, structContextToCompileShapeExact, hfields] using
            ih { context with structs := (name, { fields := fields, size := 0 }) :: context.structs }
      | function declaration =>
          simpa only [structGetNames, List.foldl_cons, List.map_cons, declToHOL,
            Pancake.PanStructs.CompileShapeExact.getNamesExact] using ih context
      | decl shape name value =>
          simpa only [structGetNames, List.foldl_cons, List.map_cons, declToHOL,
            Pancake.PanStructs.CompileShapeExact.getNamesExact] using ih context
      | exnDecl name shape =>
          simpa only [structGetNames, List.foldl_cons, List.map_cons, declToHOL,
            Pancake.PanStructs.CompileShapeExact.getNamesExact] using ih context

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

/-- Full declaration compilation commutes with the declaration/context codecs.
The tail recursion and its final globals are proved internally. Function bodies
use that final context with their original source parameters; parameter and
return shapes use the incoming structure context. This is Flapjack codec
infrastructure with no HOL theorem original, not an evaluator simulation. -/
theorem structCompileDecls_encode {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) :
    ∀ (context : StructPassContext), CtxBR context.structs →
      ListParamByteRanged context.locals → ListParamByteRanged context.globals →
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
      ((structCompileDecls declarations context).1.map declToHOL,
        structPassContextToExact (structCompileDecls declarations context).2) =
      compileDeclsExact (structPassContextToExact context) (declarations.map declToHOL) := by
  induction declarations with
  | nil => intro context hc hl hg hd; rfl
  | cons declaration rest ih =>
      intro context hc hl hg hdecls
      have hd := hdecls declaration (by simp)
      have hrest : ∀ item ∈ rest, DeclByteRanged item := by
        intro item hitem
        exact hdecls item (by simp [hitem])
      cases declaration with
      | decl shape name value =>
          simp only [DeclByteRanged] at hd
          rcases hd with ⟨hs, hn, hv⟩
          have hgNext : ListParamByteRanged ((name, shape) :: context.globals) := by
            intro p hp
            simp only [List.mem_cons] at hp
            rcases hp with hp | hp
            · cases hp; exact ⟨hn, hs⟩
            · exact hg p hp
          have hctx : structPassContextToExact
              { context with globals := (name, shape) :: context.globals } =
              { structPassContextToExact context with
                globals := (ofString name, shapeToHOL shape) ::
                  (structPassContextToExact context).globals } := rfl
          simp only [structCompileDecls, List.map_cons, declToHOL, compileDeclsExact]
          rw [← hctx, ← ih { context with globals := (name, shape) :: context.globals }
            hc hl hgNext hrest]
          simp only [contextStructs_encode]
          rw [compileShapeExact_encode context.structs shape hc hs,
            compileExpExact_encode context hc hl hg value hv]
      | function declaration =>
          simp only [DeclByteRanged, FunDeclByteRanged] at hd
          rcases hd with ⟨_, hparams, hbody, hreturn⟩
          have hcTail : CtxBR (structCompileDecls rest context).2.structs := by
            rw [structCompileDecls_structs rest context structCompileShape structOldExpShape]
            exact hc
          have hgTail := structCompileDecls_globals_byteRanged rest context
            structCompileShape structOldExpShape hg hrest
          have hctx : structPassContextToExact
              { (structCompileDecls rest context).2 with locals := declaration.params } =
              { structPassContextToExact (structCompileDecls rest context).2 with
                locals := declaration.params.map paramToHOL } := rfl
          simp only [structCompileDecls, List.map_cons, declToHOL, compileDeclsExact]
          rw [← ih context hc hl hg hrest]
          simp only [funDeclToHOL, contextStructs_encode]
          rw [compiledParams_encode context.structs hc declaration.params hparams,
            legacyProgram_encode
              { (structCompileDecls rest context).2 with locals := declaration.params }
              hcTail hparams hgTail declaration.body hbody,
            compileShapeExact_encode context.structs declaration.returnShape hc hreturn]
          rw [hctx]
          rfl
      | exnDecl name shape =>
          simp only [DeclByteRanged] at hd
          simp only [structCompileDecls, List.map_cons, declToHOL, compileDeclsExact]
          rw [← ih context hc hl hg hrest]
          simp only [contextStructs_encode]
          rw [compileShapeExact_encode context.structs shape hc hd.2]
      | name name fields =>
          simpa only [structCompileDecls, List.map_cons, declToHOL, compileDeclsExact]
            using ih context hc hl hg hrest

/-- Top-level compilation commutes with the declaration codec. The initial
structure context comes from the actual name collector, and its range invariant
is derived from the input declarations. This is Flapjack codec infrastructure
with no HOL theorem original. -/
theorem structCompileTop_encode {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hd : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    (structCompileTop declarations).map declToHOL =
      compileTopExact (declarations.map declToHOL) := by
  let initial : StructPassContext := { structs := [], locals := [], globals := [] }
  have hc : CtxBR (structGetNames initial declarations).structs :=
    structGetNames_ctxBR initial declarations (by simp [initial, CtxBR]) hd
  have hfields := structGetNames_locals_globals initial declarations
  have hl : ListParamByteRanged (structGetNames initial declarations).locals := by
    rw [hfields.1]
    simp [initial, ListParamByteRanged]
  have hg : ListParamByteRanged (structGetNames initial declarations).globals := by
    rw [hfields.2]
    simp [initial, ListParamByteRanged]
  have h := congrArg Prod.fst (structCompileDecls_encode declarations
    (structGetNames initial declarations) hc hl hg hd)
  rw [structGetNames_encode] at h
  simpa [structCompileTop, compileTopExact, initial, structPassContextToExact,
    structContextToCompileShapeExact] using h

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

/-- The actual top-level compiler output survives the syntax codec roundtrip.
The compiler derives its structure context and output range from ranged inputs;
no compiled-result invariant is supplied. This is Flapjack codec infrastructure. -/
theorem structCompileTop_codec_roundtrip {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hd : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ((structCompileTop declarations).map declToHOL).map declOfHOL =
      structCompileTop declarations :=
  declarationList_codec_roundtrip _ (structCompileTop_byteRanged declarations hd)

end Flapjack
