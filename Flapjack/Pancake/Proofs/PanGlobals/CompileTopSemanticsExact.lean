import Flapjack.Pancake.Proofs.PanGlobals
import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopShapeWf
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

namespace Flapjack

open Flapjack.Pancake.PanLang

namespace PanGlobalsCompileTopSemanticsExact

open PanGlobalsCompileDecsStructural
open PanGlobalsDeclListExact
open PanPropsEvalStateFiniteExact

/-- Same-module canonical witness for the exact state finite-map carrier used
by the declaration evaluator theorem below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width]
    : (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
      (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

private theorem updateListCons {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) (entry : α × β)
    (entries : List (α × β)) :
    (map.update entry).updateList entries = map.updateList (entry :: entries) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateList, FUPDATE_LIST_cons]
  rfl

private theorem fpermDecsHOL_append {width : Nat} [NeZero width]
    (source target : MlS) (left right : List (DeclHOL width)) :
    fpermDecsHOL source target (left ++ right) =
      fpermDecsHOL source target left ++ fpermDecsHOL source target right := by
  induction left with
  | nil => simp [fpermDecsHOL]
  | cons declaration left ih =>
      cases declaration <;> simp [fpermDecsHOL, ih]

private theorem resortDeclsHOL_filter_partition {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width))
    (hkinds : ∀ declaration ∈ declarations,
      isFunctionHOL declaration = true ∨ isDeclHOL declaration = true ∨
        isExnDeclHOL declaration = true) :
    resortDeclsHOL declarations =
      declarations.filter isExnDeclHOL ++ declarations.filter isDeclHOL ++
        declarations.filter isFunctionHOL := by
  have hnames : declarations.filter isNameHOL = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro declaration hmem
    have hkind := hkinds declaration hmem
    cases declaration <;> simp [isNameHOL, isFunctionHOL, isDeclHOL,
      isExnDeclHOL] at hkind ⊢
  simp [resortDeclsHOL, hnames]

/-- Flapjack proof infrastructure for the source proof's final function-table
calculation; this list equation is not a separately named HOL theorem. -/
private theorem functionsHOL_map_compile {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) (declarations : List (DeclHOL width)) :
    functionsHOL (declarations.map (fun declaration => match declaration with
      | .function function =>
          .function { function with body := compileProgExactHOL context function.body }
      | _ => .name (Flapjack.Basis.Pure.MlString.ofString "") [])) =
      (functionsHOL declarations).map (fun entry =>
        (entry.1, entry.2.1, compileProgExactHOL context entry.2.2.1, entry.2.2.2)) := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration <;> simp [functionsHOL, ih]

/-- Flapjack proof infrastructure exposing the final context in the sorted
declaration compiler's function suffix. Its premises are structural partition
facts, not a simulation or target-evaluation assumption. -/
private theorem compileDecsHOL_function_suffix {width : Nat} [NeZero width]
    (context finalContext : PanGlobalsContextExact width)
    (initialDecls suffix : List (DeclHOL width))
    (decls : List (ProgHOL width)) (funs exns : List (DeclHOL width))
    (hprefix : ∀ declaration ∈ initialDecls, ¬ isFunctionHOL declaration = true)
    (hsuffix : ∀ declaration ∈ suffix, isFunctionHOL declaration = true)
    (hcompile : compileDecsExactHOL context (initialDecls ++ suffix) =
      (decls, funs, exns, finalContext)) :
    functionsHOL funs = (functionsHOL suffix).map (fun entry =>
      (entry.1, entry.2.1, compileProgExactHOL finalContext entry.2.2.1, entry.2.2.2)) := by
  rcases hp : compileDecsExactHOL context initialDecls with
    ⟨prefixDecls, prefixFuns, prefixExns, middle⟩
  have hpf := compile_decs_decls_thmHOL context initialDecls
    prefixDecls prefixFuns prefixExns middle ⟨hp, hprefix⟩
  rcases hs : compileDecsExactHOL middle suffix with
    ⟨suffixDecls, suffixFuns, suffixExns, last⟩
  obtain ⟨hd, he, hc, hf⟩ := compile_decs_functions_thmHOL middle suffix
    suffixDecls suffixFuns suffixExns last ⟨hs, hsuffix⟩
  simp only [compile_decls_appendHOL, hp, hs, hpf, hd, he, hc] at hcompile
  simp only [List.nil_append, List.append_nil, Prod.mk.injEq] at hcompile
  obtain ⟨_, hfun, _, hcontext⟩ := hcompile
  rw [← hfun, hf, ← hcontext]
  exact functionsHOL_map_compile middle suffix

/-- Flapjack assembly lemma computing the sorted compiler's function table
at its final context, as required by the source compile-top evaluator proof.
It does not claim a separate HOL declaration. -/
private theorem compileDecsHOL_resorted_functions {width : Nat} [NeZero width]
    (context finalContext : PanGlobalsContextExact width)
    (declarations : List (DeclHOL width)) (source target : MlS)
    (decls : List (ProgHOL width)) (funs exns : List (DeclHOL width))
    (hkinds : ∀ declaration ∈ declarations,
      isFunctionHOL declaration = true ∨ isDeclHOL declaration = true ∨
        isExnDeclHOL declaration = true)
    (hcompile : compileDecsExactHOL context
      (fpermDecsHOL source target (resortDeclsHOL declarations)) =
        (decls, funs, exns, finalContext)) :
    functionsHOL funs =
      (functionsHOL (fpermDecsHOL source target declarations)).map (fun entry =>
        (entry.1, entry.2.1, compileProgExactHOL finalContext entry.2.2.1, entry.2.2.2)) := by
  let initialDecls := declarations.filter isExnDeclHOL ++ declarations.filter isDeclHOL
  have hprefix : ∀ declaration ∈ initialDecls, ¬ isFunctionHOL declaration = true := by
    intro declaration hmem
    simp only [initialDecls, List.mem_append, List.mem_filter] at hmem
    cases declaration <;> simp_all [isFunctionHOL, isExnDeclHOL, isDeclHOL]
  have hunchanged : fpermDecsHOL source target initialDecls = initialDecls := by
    apply fperm_decs_declsHOL source target initialDecls ()
    intro declaration hmem
    simpa using hprefix declaration hmem
  have hsuffix : ∀ declaration ∈ fpermDecsHOL source target
      (declarations.filter isFunctionHOL), isFunctionHOL declaration = true := by
    apply EVERY_fperm_decsHOL
    · intro declaration hmem hfalse
      have htrue := (List.mem_filter.mp hmem).2
      simp [hfalse] at htrue
    · intro declaration hmem function heq
      simp [isFunctionHOL]
  have hpartition := resortDeclsHOL_filter_partition declarations hkinds
  have hcompiled : compileDecsExactHOL context
      (initialDecls ++ fpermDecsHOL source target (declarations.filter isFunctionHOL)) =
        (decls, funs, exns, finalContext) := by
    rw [hpartition] at hcompile
    change compileDecsExactHOL context
      (fpermDecsHOL source target
        (initialDecls ++ declarations.filter isFunctionHOL)) = _ at hcompile
    simpa only [fpermDecsHOL_append, hunchanged] using hcompile
  have h := compileDecsHOL_function_suffix context finalContext initialDecls
    (fpermDecsHOL source target (declarations.filter isFunctionHOL))
    decls funs exns hprefix hsuffix hcompiled
  simpa only [fperm_decs_FILTER_is_functionHOL, functionsHOL_filter_isFunction] using h

/-- Same-module canonical multi-carrier witness for the PanSem state used by
the compile-top semantics theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module canonical multi-carrier witness for the compiler context used
by the compile-top semantics theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Exact PanGlobals source lemma `evaluate_decls_only_functions_SOME`
(`pan_globalsProofScript.sml:2390`). Every source declaration is a function,
and the source's nested well-formed-shape premise is preserved literally.
`Classical.propDecidable` supplies the evaluator's implementation-only
decision procedure without adding a theorem hypothesis. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_only_functions_SOME"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsOnlyFunctionsSOMEHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (panCode : List (DeclHOL width))
    (hfunctions : ∀ declaration ∈ panCode, isFunctionHOL declaration = true)
    (hshapes : ∀ declaration ∈ panCode, ∀ function,
      declaration = .function function →
        function.params.all (fun parameter =>
          isWfShapeExactHOL state.structs parameter.2) = true ∧
          isWfShapeExactHOL state.structs function.returnShape = true) :
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ (by exact inferInstance) state
      (fun address => Classical.propDecidable (state.memaddrs address)) panCode =
      some { state with code := state.code.updateList (functionsHOL panCode) } := by
  classical
  induction panCode generalizing state with
  | nil =>
      cases state
      rfl
  | cons declaration declarations ih =>
      cases declaration with
      | name name fields =>
          have hbad := hfunctions (.name name fields) (by simp)
          simp [isFunctionHOL] at hbad
      | decl shape name expression =>
          have hbad := hfunctions (.decl shape name expression) (by simp)
          simp [isFunctionHOL] at hbad
      | exnDecl exceptionName shape =>
          have hbad := hfunctions (.exnDecl exceptionName shape) (by simp)
          simp [isFunctionHOL] at hbad
      | function function =>
          have hshape := hshapes (.function function) (by simp) function rfl
          have hparam : function.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) = true :=
            hshape.1
          have hreturn : isWfShapeExactHOL state.structs function.returnShape = true :=
            hshape.2
          let updated : PanSemStateFiniteExact width σ :=
            { state with code := state.code.update (function.name,
                (function.params, function.body, function.returnShape)) }
          have hrestFunctions : ∀ declaration ∈ declarations,
              isFunctionHOL declaration = true := by
            intro declaration hmem
            exact hfunctions declaration (by simp [hmem])
          have hrestShapes : ∀ declaration ∈ declarations, ∀ function',
              declaration = .function function' →
                function'.params.all (fun parameter =>
                  isWfShapeExactHOL updated.structs parameter.2) = true ∧
                  isWfShapeExactHOL updated.structs function'.returnShape = true := by
            intro declaration hmem function' heq
            have h := hshapes declaration (by simp [hmem]) function' heq
            simpa [updated] using h
          have hrec := ih updated hrestFunctions hrestShapes
          simpa [PanSemStateFiniteExact.evaluateDeclsHOLFinite, hparam, hreturn,
            updated, functionsHOL, updateListCons]
            using hrec

/-- Exact PanGlobals source lemma `evaluate_decls_only_functions_and_exns_SOME`
(`pan_globalsProofScript.sml:2404`). It retains the HOL requirements that
exception identifiers are distinct and fresh in the starting exception map;
those facts permit each `FUPDATE_LIST` in the exact finite-support state. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml"
  "evaluate_decls_only_functions_and_exns_SOME"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsOnlyFunctionsAndExnsSOMEHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (panCode : List (DeclHOL width))
    (hkind : ∀ declaration ∈ panCode,
      isFunctionHOL declaration = true ∨ isExnDeclHOL declaration = true)
    (hfunctions : ∀ declaration ∈ panCode, ∀ function,
      declaration = .function function →
        function.params.all (fun parameter =>
          isWfShapeExactHOL state.structs parameter.2) = true ∧
          isWfShapeExactHOL state.structs function.returnShape = true)
    (hdistinct : ((exceptionsHOL panCode).map Prod.fst).Nodup)
    (hfresh : ∀ entry ∈ exceptionsHOL panCode,
      (state.eshapes.lookup entry.1).isNone = true)
    (hshapes : ∀ entry ∈ exceptionsHOL panCode,
      isWfShapeExactHOL state.structs entry.2 = true) :
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ (by exact inferInstance) state
      (fun address => Classical.propDecidable (state.memaddrs address)) panCode =
      some { state with
        code := state.code.updateList (functionsHOL panCode)
        eshapes := state.eshapes.updateList (exceptionsHOL panCode) } := by
  classical
  induction panCode generalizing state with
  | nil =>
      cases state
      rfl
  | cons declaration declarations ih =>
      cases declaration with
      | name name fields =>
          have hbad := hkind (.name name fields) (by simp)
          simp [isFunctionHOL, isExnDeclHOL] at hbad
      | decl shape name expression =>
          have hbad := hkind (.decl shape name expression) (by simp)
          simp [isFunctionHOL, isExnDeclHOL] at hbad
      | function function =>
          have hfunction := hfunctions (.function function) (by simp) function rfl
          have hparam : function.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) = true :=
            hfunction.1
          have hreturn : isWfShapeExactHOL state.structs function.returnShape = true :=
            hfunction.2
          let updated : PanSemStateFiniteExact width σ :=
            { state with code := state.code.update (function.name,
                (function.params, function.body, function.returnShape)) }
          have hrestKind : ∀ declaration ∈ declarations,
              isFunctionHOL declaration = true ∨ isExnDeclHOL declaration = true := by
            intro declaration hmem
            exact hkind declaration (by simp [hmem])
          have hrestFunctions : ∀ declaration ∈ declarations, ∀ function',
              declaration = .function function' →
                function'.params.all (fun parameter =>
                  isWfShapeExactHOL updated.structs parameter.2) = true ∧
                  isWfShapeExactHOL updated.structs function'.returnShape = true := by
            intro declaration hmem function' heq
            have h := hfunctions declaration (by simp [hmem]) function' heq
            simpa [updated] using h
          have hrestDistinct : ((exceptionsHOL declarations).map Prod.fst).Nodup := by
            simpa [exceptionsHOL] using hdistinct
          have hrestFresh : ∀ entry ∈ exceptionsHOL declarations,
              (updated.eshapes.lookup entry.1).isNone = true := by
            intro entry hmem
            have h := hfresh entry (by simpa [exceptionsHOL] using hmem)
            simpa [updated] using h
          have hrestShapes : ∀ entry ∈ exceptionsHOL declarations,
              isWfShapeExactHOL updated.structs entry.2 = true := by
            intro entry hmem
            have h := hshapes entry (by simpa [exceptionsHOL] using hmem)
            simpa [updated] using h
          have hrec := ih updated hrestKind hrestFunctions hrestDistinct hrestFresh hrestShapes
          simpa [PanSemStateFiniteExact.evaluateDeclsHOLFinite, hparam, hreturn,
            updated, functionsHOL, exceptionsHOL, updateListCons]
            using hrec
      | exnDecl exceptionName shape =>
          have hallowed := hkind (.exnDecl exceptionName shape) (by simp)
          simp [isFunctionHOL, isExnDeclHOL] at hallowed
          have hshape : isWfShapeExactHOL state.structs shape = true :=
            hshapes ((exceptionName, shape) : MlS × ShapeHOL) (by simp [exceptionsHOL])
          have hfreshHead : (state.eshapes.lookup exceptionName).isNone = true :=
            hfresh ((exceptionName, shape) : MlS × ShapeHOL) (by simp [exceptionsHOL])
          have hdistinctRest : exceptionName ∉
              (exceptionsHOL declarations).map Prod.fst := by
            have hcons : List.Nodup
                (exceptionName :: (exceptionsHOL declarations).map Prod.fst) := by
              simpa [exceptionsHOL] using hdistinct
            exact (List.nodup_cons.mp hcons).1
          have hrestDistinct : ((exceptionsHOL declarations).map Prod.fst).Nodup := by
            have hcons : List.Nodup
                (exceptionName :: (exceptionsHOL declarations).map Prod.fst) := by
              simpa [exceptionsHOL] using hdistinct
            exact (List.nodup_cons.mp hcons).2
          let updated : PanSemStateFiniteExact width σ :=
            { state with eshapes := state.eshapes.update (exceptionName, shape) }
          have hrestKind : ∀ declaration ∈ declarations,
              isFunctionHOL declaration = true ∨ isExnDeclHOL declaration = true := by
            intro declaration hmem
            exact hkind declaration (by simp [hmem])
          have hrestFunctions : ∀ declaration ∈ declarations, ∀ function,
              declaration = .function function →
                function.params.all (fun parameter =>
                  isWfShapeExactHOL updated.structs parameter.2) = true ∧
                  isWfShapeExactHOL updated.structs function.returnShape = true := by
            intro declaration hmem function heq
            have h := hfunctions declaration (by simp [hmem]) function heq
            simpa [updated] using h
          have hrestFresh : ∀ entry ∈ exceptionsHOL declarations,
              (updated.eshapes.lookup entry.1).isNone = true := by
            intro entry hmem
            have hlookup := hfresh entry (by simp [exceptionsHOL, hmem])
            have hkey : exceptionName ≠ entry.1 := by
              intro heq
              subst exceptionName
              apply hdistinctRest
              exact List.mem_map.mpr ⟨entry, hmem, rfl⟩
            simpa [updated, HolFiniteMapExact.lookup_update, FUPDATE, hkey] using hlookup
          have hrestShapes : ∀ entry ∈ exceptionsHOL declarations,
              isWfShapeExactHOL updated.structs entry.2 = true := by
            intro entry hmem
            have h := hshapes entry (by simp [exceptionsHOL, hmem])
            simpa [updated] using h
          have hrec := ih updated hrestKind hrestFunctions hrestDistinct hrestFresh hrestShapes
          simpa [PanSemStateFiniteExact.evaluateDeclsHOLFinite, hshape, hfreshHead,
            updated, functionsHOL, exceptionsHOL, updateListCons]
            using hrec

/-- Flapjack assembly infrastructure: compiled declaration evaluation updates
the two exact tables extracted from the compiled list. The source theorem's
explicit compiler-result tables are computed separately before tagging the
assembled source result. -/
private theorem evaluateDeclsCompileTopUpdates {width : Nat} {σ : Type}
    [NeZero width] (state result : PanSemStateFiniteExact width σ)
    (declarations : List (DeclHOL width)) (start : MlS)
    (entry : List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
    (heval : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address)) declarations =
        some result)
    (hstart : (functionsHOL declarations).lookup start = some entry)
    (hkinds : ∀ declaration ∈ declarations,
      isFunctionHOL declaration = true ∨ isDeclHOL declaration = true ∨
        isExnDeclHOL declaration = true) :
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (compileTopExactHOL declarations start) =
        some { state with
          code := state.code.updateList (functionsHOL (compileTopExactHOL declarations start))
          eshapes := state.eshapes.updateList
            (exceptionsHOL (compileTopExactHOL declarations start)) } := by
  classical
  have hcanonical : evaluateDeclsPanPropsCanonical
      (PanPropsEvalStateFiniteExact.ofPanSemFinite state) declarations =
        some (PanPropsEvalStateFiniteExact.ofPanSemFinite result) := by
    simpa [evaluateDeclsPanPropsCanonical] using
      congrArg (Option.map PanPropsEvalStateFiniteExact.ofPanSemFinite) heval
  have hex := evaluateDeclsExnsWfHOLFinite
    (PanPropsEvalStateFiniteExact.ofPanSemFinite state) declarations
    (PanPropsEvalStateFiniteExact.ofPanSemFinite result) hcanonical
  have hexceptions := exceptions_compile_topHOL declarations start entry hstart
  apply evaluateDeclsOnlyFunctionsAndExnsSOMEHOLFinite
  · exact compile_top_only_functions_or_exnsHOL declarations start
  · intro declaration hmem function heq
    have hwf := PanGlobalsCompileTopShapeWf.compile_top_shape_wfHOL
      state result declarations start ⟨heval, hkinds⟩ declaration hmem function heq
    exact ⟨List.all_eq_true.mpr hwf.1, hwf.2⟩
  · simpa only [hexceptions] using hex.1
  · intro current hmem
    rw [hexceptions] at hmem
    exact List.all_eq_true.mp hex.2.1 current hmem
  · intro current hmem
    rw [hexceptions] at hmem
    exact List.all_eq_true.mp hex.2.2 current hmem

/-- Exact `evaluate_decls_compile_top` (`pan_globalsProofScript.sml:2543-2610`).
The four conjuncts are HOL's successful source evaluation, first-match entry
lookup, declaration-kind restriction, and compiler-result equation. The
conclusion proves the compiled evaluation and the explicit code/exception
updates. HOL's `TailCall` is `Call NONE` (panLangScript.sml:127), represented
by `.call none`. No target-evaluation or post-state premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_compile_top"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsCompileTopHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state result : PanSemStateFiniteExact width σ)
    (declarations : List (DeclHOL width)) (start : MlS)
    (arguments : List (MlS × ShapeHOL)) (body : ProgHOL width) (returnShape : ShapeHOL)
    (initializers : List (ProgHOL width)) (funs exns : List (DeclHOL width))
    (context : PanGlobalsContextExact width) :
    (@PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address)) declarations =
        some result) ∧
    (functionsHOL declarations).lookup start = some (arguments, body, returnShape) ∧
    (∀ declaration ∈ declarations,
      isFunctionHOL declaration = true ∨ isDeclHOL declaration = true ∨
        isExnDeclHOL declaration = true) ∧
    compileDecsExactHOL
      { globals := HolFiniteMapExact.empty, globalsSize := 0,
        maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
          ((decShapesHOL declarations).map sizeOfShapeHOL).sum }
      (fpermDecsHOL start (newMainNameHOL declarations) (resortDeclsHOL declarations)) =
        (initializers, funs, exns, context) →
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (compileTopExactHOL declarations start) =
        some { state with
          code := (state.code.update (start, arguments,
            .seq (nestedSeqHOL initializers)
              (.call none (newMainNameHOL declarations)
                (arguments.map (fun parameter => .var .local parameter.1))), returnShape)).updateList
            ((functionsHOL (fpermDecsHOL start (newMainNameHOL declarations) declarations)).map
              (fun entry => (entry.1, entry.2.1,
                compileProgExactHOL context entry.2.2.1, entry.2.2.2)))
          eshapes := state.eshapes.updateList (exceptionsHOL exns) } := by
  intro ⟨heval, hstart, hkinds, hcompile⟩
  let initial : PanGlobalsContextExact width :=
    { globals := HolFiniteMapExact.empty, globalsSize := 0,
      maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
        ((decShapesHOL declarations).map sizeOfShapeHOL).sum }
  let renamed := fpermDecsHOL start (newMainNameHOL declarations)
    (resortDeclsHOL declarations)
  have hc : compileDecsExactHOL initial renamed = (initializers, funs, exns, context) :=
    hcompile
  let main : DeclHOL width := .function
      { name := start
        inline := false
        exported := false
        params := arguments
        body := .seq (nestedSeqHOL initializers)
          (.call none (newMainNameHOL declarations)
            (arguments.map (fun parameter => .var .local parameter.1)))
        returnShape := returnShape }
  have htop : compileTopExactHOL declarations start = exns ++ (main :: funs) := by
    simp only [compileTopExactHOL, compileTopFunctionLookup_eq_lookup, hstart,
      dec_shapes_fperm_decsHOL, dec_shapes_resort_declsHOL, hcompile, main]
  have hf := compileDecsHOL_resorted_functions initial context declarations start
    (newMainNameHOL declarations) initializers funs exns hkinds hc
  have he := compile_decs_exns_are_exnsHOL initial renamed initializers funs exns context hc
  have hexnFunctions : functionsHOL exns = [] := by
    rw [he]
    exact functions_FILTER_exn_declHOL renamed
  have hfunKinds := compile_decs_EVERY_is_functionHOL initial renamed
    initializers funs exns context hc
  have hfunExceptions : exceptionsHOL funs = [] := by
    rw [← List.filter_eq_self.mpr hfunKinds]
    exact (exceptions_FILTER_is_functionHOL funs).1
  have hfunctions := congrArg (fun code => functionsHOL code) htop
  simp only [functionsHOL_append, hexnFunctions, List.nil_append, main, functionsHOL] at hfunctions
  rw [hf] at hfunctions
  have hexceptions : exceptionsHOL (compileTopExactHOL declarations start) =
      exceptionsHOL exns := by
    rw [htop, exceptions_appendHOL]
    simp only [main, exceptionsHOL, hfunExceptions, List.append_nil]
  have hresult := evaluateDeclsCompileTopUpdates state result declarations start
    (arguments, body, returnShape) heval hstart hkinds
  simpa only [hfunctions, hexceptions, ← updateListCons] using hresult

end PanGlobalsCompileTopSemanticsExact

end Flapjack
