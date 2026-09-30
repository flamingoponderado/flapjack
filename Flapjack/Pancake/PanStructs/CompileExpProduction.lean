import Flapjack.Pancake.PanStructs.CompileExpCorrespondence

/-! Flapjack production traversal for reviewed expression compilation.
It preserves the existing pass context updates; it is codec infrastructure,
not an independently tagged HOL program-correctness theorem. -/
namespace Flapjack
open Pancake.PanLang

def structCompileProgExactProduction {width : Nat} [NeZero width]
    (context : StructPassContext) : Prog (BitVec width) → Prog (BitVec width)
  | .dec name shape value body =>
      .dec name (structCompileShapeExactProduction context.structs shape)
        (structCompileExpExactProduction context value)
        (structCompileProgExactProduction { context with locals := (name, shape) :: context.locals }
          body)
  | .assign kind name value =>
      .assign kind name (structCompileExpExactProduction context value)
  | .primitive name operator arguments =>
      .primitive name operator (structCompileExps context arguments)
  | .store address value =>
      .store (structCompileExpExactProduction context address)
        (structCompileExpExactProduction context value)
  | .store32 address value =>
      .store32 (structCompileExpExactProduction context address)
        (structCompileExpExactProduction context value)
  | .storeByte address value =>
      .storeByte (structCompileExpExactProduction context address)
        (structCompileExpExactProduction context value)
  | .seq first second =>
      .seq (structCompileProgExactProduction context first)
        (structCompileProgExactProduction context second)
  | .ite condition thenBranch elseBranch =>
      .ite (structCompileExpExactProduction context condition)
        (structCompileProgExactProduction context thenBranch)
        (structCompileProgExactProduction context elseBranch)
  | .while condition body =>
      .while (structCompileExpExactProduction context condition)
        (structCompileProgExactProduction context body)
  | .call info function arguments =>
      let compiledInfo := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar,
              structCompileProgExactProduction context handler))
      .call compiledInfo function (structCompileExps context arguments)
  | .decCall name shape function arguments body =>
      .decCall name (structCompileShapeExactProduction context.structs shape) function
        (structCompileExps context arguments)
        (structCompileProgExactProduction { context with locals := (name, shape) :: context.locals }
          body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (structCompileExpExactProduction context configuration)
        (structCompileExpExactProduction context configurationLength)
        (structCompileExpExactProduction context array)
        (structCompileExpExactProduction context arrayLength)
  | .raise exception value =>
      .raise exception (structCompileExpExactProduction context value)
  | .return value =>
      .return (structCompileExpExactProduction context value)
  | .shMemLoad size kind name address =>
      .shMemLoad size kind name (structCompileExpExactProduction context address)
  | .shMemStore size address value =>
      .shMemStore size (structCompileExpExactProduction context address)
        (structCompileExpExactProduction context value)
  | program => program
termination_by program => sizeOf program
where
  structCompileExps (context : StructPassContext) :
      List (Exp (BitVec width)) → List (Exp (BitVec width))
    | [] => []
    | expression :: expressions =>
        structCompileExpExactProduction context expression ::
          structCompileExps context expressions
termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- Flapjack expression argument-list equality on genuine ranged inputs. -/
theorem structCompileProgExactProduction_exps_eq_legacy {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (expressions : List (Exp (BitVec width))) (he : ∀ e ∈ expressions, ExpByteRanged e) :
    structCompileProgExactProduction.structCompileExps context expressions =
      structCompileProg.structCompileExps context expressions := by
  induction expressions with
  | nil => simp [structCompileProgExactProduction.structCompileExps,
      structCompileProg.structCompileExps]
  | cons expression expressions ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at he
      simp [structCompileProgExactProduction.structCompileExps,
        structCompileProg.structCompileExps,
        structCompileExpExactProduction_eq_legacy context hc hl hg expression he.1, ih he.2]

/-- Flapjack production traversal equality, including local binding and optional
handler contexts. This is codec infrastructure with no HOL theorem original. -/
theorem structCompileProgExactProduction_eq_legacy {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      structCompileProgExactProduction context program = structCompileProg context program
  | .skip, _ => by simp [structCompileProgExactProduction, structCompileProg]
  | .dec name shape value body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hname, hshape, hvalue, hbody⟩
      have hl' : ListParamByteRanged ((name, shape) :: context.locals) := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · cases hp; exact ⟨hname, hshape⟩
        · exact hl p hp
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileShapeExactProduction_eq_legacy context.structs shape hc hshape]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value hvalue]
      rw [structCompileProgExactProduction_eq_legacy
        { context with locals := (name, shape) :: context.locals }
        hc hl' hg body hbody]
  | .assign kind name value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .primitive name operator arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments h.2]
  | .store address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .store32 address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .storeByte address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .seq first second, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg first h.1]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg second h.2]
  | .ite condition thenBranch elseBranch, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg condition h.1]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg thenBranch h.2.1]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg elseBranch h.2.2]
  | .while condition body, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg condition h.1]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg body h.2]
  | .break, _ => by simp [structCompileProgExactProduction, structCompileProg]
  | .continue, _ => by simp [structCompileProgExactProduction, structCompileProg]
  | .call none function arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments h.2.1]
  | .call (some (returns, none)) function arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments h.2.1]
  | .call (some (returns, some (exception, handlerVar, handler))) function arguments, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨_, hargs, _, _, _, hhandler⟩
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments hargs]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg handler hhandler]
  | .decCall name shape function arguments body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hname, hshape, _, hargs, hbody⟩
      have hl' : ListParamByteRanged ((name, shape) :: context.locals) := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · cases hp; exact ⟨hname, hshape⟩
        · exact hl p hp
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileShapeExactProduction_eq_legacy context.structs shape hc hshape]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments hargs]
      rw [structCompileProgExactProduction_eq_legacy
        { context with locals := (name, shape) :: context.locals }
        hc hl' hg body hbody]
  | .extCall function configuration configurationLength array arrayLength, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg configuration h.2.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg configurationLength h.2.2.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg array h.2.2.2.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg arrayLength h.2.2.2.2]
  | .raise exception value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .return value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h]
  | .shMemLoad size kind name address, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.2]
  | .shMemStore size address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .tick, _ => by simp [structCompileProgExactProduction, structCompileProg]
  | .annot tag text, _ => by simp [structCompileProgExactProduction, structCompileProg]
termination_by program _ => sizeOf program
decreasing_by
  all_goals
    first
    | decreasing_trivial
    | (simp_wf; omega)
    | omega


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
