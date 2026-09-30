import Flapjack.Pancake.PanStructs.CompileProgTraversal

/-! Flapjack production declaration and top-level traversal. Program traversal
is factored into its own counterpart-local module so exact program codecs can
be proved without importing declaration callers. -/
namespace Flapjack
open Pancake.PanLang

/-- Production declarations preserve the legacy context flow while invoking
the reviewed expression compiler through its checked codec wrapper. -/
def structCompileDeclsExactProduction {width : Nat} [NeZero width] :
    List (Decl (BitVec width)) → StructPassContext →
      List (Decl (BitVec width)) × StructPassContext
  | [], context => ([], context)
  | .decl shape name value :: declarations, context =>
      let nextContext := { context with globals := (name, shape) :: context.globals }
      let (compiled, finalContext) := structCompileDeclsExactProduction declarations nextContext
      (.decl (structCompileShapeExactProduction context.structs shape) name
        (structCompileExpExactProduction context value) :: compiled,
        finalContext)
  | .function declaration :: declarations, context =>
      let (compiled, finalContext) := structCompileDeclsExactProduction declarations context
      let parameters := declaration.params.map
        (fun (name, shape) => (name, structCompileShapeExactProduction context.structs shape))
      let functionContext := { finalContext with locals := declaration.params }
      let compiledDeclaration := { declaration with
        params := parameters
        body := structCompileProgExactProduction functionContext declaration.body
        returnShape := structCompileShapeExactProduction context.structs declaration.returnShape }
      (.function compiledDeclaration :: compiled, finalContext)
  | .exnDecl exception shape :: declarations, context =>
      let (compiled, finalContext) := structCompileDeclsExactProduction declarations context
      (.exnDecl exception (structCompileShapeExactProduction context.structs shape) :: compiled, finalContext)
  | .name _ _ :: declarations, context =>
      structCompileDeclsExactProduction declarations context

def structCompileTopExpressionsExactProduction {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) : List (Decl (BitVec width)) :=
  let initial : StructPassContext :=
    { structs := [], locals := [], globals := [] }
  (structCompileDeclsExactProduction declarations (structGetNames initial declarations)).1

/-- Flapjack declaration traversal equality, including its returned context.
Only actual source range invariants are premises; there is no result premise. -/
theorem structCompileDeclsExactProduction_eq_legacy {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) :
    ∀ (context : StructPassContext), CtxBR context.structs →
      ListParamByteRanged context.locals → ListParamByteRanged context.globals →
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
      structCompileDeclsExactProduction declarations context =
        structCompileDecls declarations context := by
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
          rcases hd with ⟨hshape, hname, hvalue⟩
          have hg' : ListParamByteRanged ((name, shape) :: context.globals) := by
            intro p hp
            simp only [List.mem_cons] at hp
            rcases hp with hp | hp
            · cases hp; exact ⟨hname, hshape⟩
            · exact hg p hp
          simp only [structCompileDeclsExactProduction, structCompileDecls]
          rw [ih { context with globals := (name, shape) :: context.globals } hc hl hg' hrest,
            structCompileShapeExactProduction_eq_legacy context.structs shape hc hshape,
            structCompileExpExactProduction_eq_legacy context hc hl hg value hvalue]
      | function declaration =>
          simp only [DeclByteRanged, FunDeclByteRanged] at hd
          rcases hd with ⟨_, hparams, hbody, hreturn⟩
          have hcTail : CtxBR (structCompileDecls rest context).2.structs := by
            rw [structCompileDecls_structs rest context structCompileShape structOldExpShape]
            exact hc
          have hgTail := structCompileDecls_globals_byteRanged rest context
            structCompileShape structOldExpShape hg hrest
          have hpEq := structCompileParams_eq_of_shape_eq context.structs
            structCompileShapeExactProduction
            (fun shape hs => structCompileShapeExactProduction_eq_legacy
              context.structs shape hc hs) declaration.params hparams
          simp only [structCompileDeclsExactProduction, structCompileDecls]
          rw [ih context hc hl hg hrest, hpEq,
            structCompileShapeExactProduction_eq_legacy
              context.structs declaration.returnShape hc hreturn,
            structCompileProgExactProduction_eq_legacy
              { (structCompileDecls rest context).2 with locals := declaration.params }
              hcTail hparams hgTail declaration.body hbody]
      | exnDecl exception shape =>
          simp only [DeclByteRanged] at hd
          simp only [structCompileDeclsExactProduction, structCompileDecls]
          rw [ih context hc hl hg hrest,
            structCompileShapeExactProduction_eq_legacy context.structs shape hc hd.2]
      | name name fields =>
          simp only [structCompileDeclsExactProduction, structCompileDecls]
          exact ih context hc hl hg hrest

/-- Flapjack full production expression-route equality for parser-ranged inputs. -/
theorem structCompileTopExpressionsExactProduction_eq_legacy {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdeclarations : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    structCompileTopExpressionsExactProduction declarations = structCompileTop declarations := by
  let initial : StructPassContext := { structs := [], locals := [], globals := [] }
  have hc : CtxBR (structGetNames initial declarations).structs :=
    structGetNames_ctxBR initial declarations (by simp [initial, CtxBR]) hdeclarations
  have hfields := structGetNames_locals_globals initial declarations
  have hl : ListParamByteRanged (structGetNames initial declarations).locals := by
    rw [hfields.1]
    simp [initial, ListParamByteRanged]
  have hg : ListParamByteRanged (structGetNames initial declarations).globals := by
    rw [hfields.2]
    simp [initial, ListParamByteRanged]
  simpa [structCompileTopExpressionsExactProduction, structCompileTop, initial] using
    congrArg Prod.fst (structCompileDeclsExactProduction_eq_legacy declarations
      (structGetNames initial declarations) hc hl hg hdeclarations)

/-- Parser-backed production boundary for exact expression compilation. -/
def structCompileTopExpressionsExactOfByteRanged {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (_hdeclarations : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    List (Decl (BitVec width)) :=
  structCompileTopExpressionsExactProduction declarations

/-- Flapjack equality at the parser-backed production boundary. -/
theorem structCompileTopExpressionsExact_eq_legacyOfByteRanged {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdeclarations : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    structCompileTopExpressionsExactOfByteRanged declarations hdeclarations =
      structCompileTop declarations :=
  structCompileTopExpressionsExactProduction_eq_legacy declarations hdeclarations

end Flapjack
