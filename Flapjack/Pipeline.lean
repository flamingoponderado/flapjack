import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanGlobalsByteRanged
import Flapjack.Pancake.PanStructs.CompileTopProduction
import Flapjack.Pancake.PanSimpByteRanged
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileProgCorrespondence
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.CrepToLoop.Optimise
import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.CompFuncProductionRoute
import Flapjack.Word
import Flapjack.RiscV.Allocator
import Flapjack.RiscV.WordExpressionFlatten
import Flapjack.RiscV.WordSimp
import Flapjack.RiscV.RegAlloc
import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.WordDeadCode
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordInstSelect
import Flapjack.RiscV.WordUnreach
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Loops
import Flapjack.RiscV.Link
import Flapjack.RiscV.Lab
import Flapjack.Display

/-!
An executable composition of the currently ported Pancake passes.

The result keeps each intermediate representation visible so the eventual
simulation theorem can be proved pass by pass. This composition covers the
front-end normalization and structure/global passes, Pancake-to-Crepe,
Crepe-to-Loop, and Loop-to-Word. The typed RISC-V artifact boundary is also
exposed, while instruction selection remains partial in
`Flapjack.RiscV.Backend`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

def pipelineExceptionCodes (fromNat : Nat → α) : Nat → List (Decl α) → InfoMap α
  | _, [] => []
  | index, .exnDecl exception _ :: declarations =>
      (exception, fromNat index) :: pipelineExceptionCodes fromNat (index + 1) declarations
  | index, _ :: declarations => pipelineExceptionCodes fromNat index declarations

/-! Source-shaped port of Pancake's `get_eids_def`
    (`cakeml/pancake/pan_to_crepScript.sml:346-353`).  Unlike
    `get_eids_from_decls`, this pass scans the exception identifiers reachable
    from function bodies, removes repeats in first-occurrence order, and only
    then assigns consecutive target words. -/
def pipelineExceptionIds (fromNat : Nat → α) : Nat → List ExceptionId → InfoMap α
  | _, [] => []
  | index, exception :: exceptions =>
      (exception, fromNat index) :: pipelineExceptionIds fromNat (index + 1) exceptions

def pipelineGetEids (fromNat : Nat → α) (functions : List (FunDecl α)) : InfoMap α :=
  pipelineExceptionIds fromNat 0
    ((functions.flatMap (fun function => expIds function.body)).eraseDups)

/-! Source-named port of the active CakeML Pancake
    `get_eids_from_decls_def` (`pan_to_crepScript.sml:356`).  Cake first
    filters to exception declarations, then numbers that filtered list from
    zero; the accumulator above expresses the same `MAP FST (exceptions ...)`
    and `GENLIST n2w` result without assigning IDs to ordinary declarations. -/
def crepGetEidsFromDecls (fromNat : Nat → α) (declarations : List (Decl α)) :
    InfoMap α :=
  pipelineExceptionCodes fromNat 0 declarations

/-! The exception-code table has exactly one entry for each declared
    exception.  This is the Lean counterpart of the size premise used by
    Cake's `get_eids_imp_excp_rel`: the table's finite-domain cardinality is
    fixed by the source declaration list, independently of the word map. -/
theorem pipelineExceptionCodes_length
    (fromNat : Nat → α) (index : Nat) (declarations : List (Decl α)) :
    (pipelineExceptionCodes fromNat index declarations).length =
      sizeOfEids declarations := by
  induction declarations generalizing index with
  | nil =>
      simp [pipelineExceptionCodes, sizeOfEids]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [pipelineExceptionCodes, sizeOfEids_cons, isExnDecl, ih] <;> omega

theorem crepGetEidsFromDecls_length
    (fromNat : Nat → α) (declarations : List (Decl α)) :
    (crepGetEidsFromDecls fromNat declarations).length =
      sizeOfEids declarations := by
  exact pipelineExceptionCodes_length fromNat 0 declarations

/-- The exception-code table depends only on the exception declarations, so
    simplifying the function bodies with `pan_simp` leaves it unchanged.  This
    is the Flapjack counterpart of Cake's `get_eids_pan_simp_compile_eq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:105`), whose
    `FDOM (get_eids_from_decls prog)` is the finite-domain projection of
    `crepGetEidsFromDecls`. -/
theorem pipelineExceptionCodes_panSimpDecls (fromNat : Nat → α) (index : Nat)
    (declarations : List (Decl α)) :
    pipelineExceptionCodes fromNat index (panSimpDecls declarations) =
      pipelineExceptionCodes fromNat index declarations := by
  rw [panSimpDecls_eq_map]
  induction declarations generalizing index with
  | nil => simp [pipelineExceptionCodes]
  | cons declaration declarations ih =>
      cases declaration <;> simp [panSimpDecl, pipelineExceptionCodes, ih]

theorem crepGetEidsFromDecls_panSimpDecls (fromNat : Nat → α)
    (declarations : List (Decl α)) :
    crepGetEidsFromDecls fromNat (panSimpDecls declarations) =
      crepGetEidsFromDecls fromNat declarations :=
  pipelineExceptionCodes_panSimpDecls fromNat 0 declarations

/-! Cake's `get_eids_imp_excp_rel` begins by proving that every declared
    exception has a target code.  This constructive lookup half is useful at
    the generic Raise boundary: the exception-code premise is obtained from
    the source declaration table rather than guessed by an evaluator wrapper. -/
theorem crepGetEidsFromDecls_lookup_of_exception
    [BEq String] [LawfulBEq String]
    (fromNat : Nat → α) (index : Nat) :
    ∀ (declarations : List (Decl α)) (exception : ExceptionId) (shape : Shape),
      (exception, shape) ∈ exceptionEntries declarations →
      ∃ code, lookupInfo exception
        (pipelineExceptionCodes fromNat index declarations) = some code := by
  intro declarations
  induction declarations generalizing index with
  | nil =>
      intro exception shape hmem
      simp [exceptionEntries] at hmem
  | cons declaration declarations ih =>
      cases declaration with
      | exnDecl declaredException declaredShape =>
          intro exception shape hmem
          by_cases heq : exception == declaredException
          · have heq' : exception = declaredException := eq_of_beq heq
            subst exception
            exact ⟨fromNat index, by simp [pipelineExceptionCodes, lookupInfo]⟩
          · have htail : (exception, shape) ∈ exceptionEntries declarations := by
              have hmem' :
                  (exception = declaredException ∧ shape = declaredShape) ∨
                    (exception, shape) ∈ exceptionEntries declarations := by
                simpa [exceptionEntries] using hmem
              rcases hmem' with ⟨hname, _⟩ | htail
              · exfalso
                apply heq
                simp [hname]
              · exact htail
            have hne : (declaredException == exception) = false := by
              rw [Bool.eq_false_iff]
              intro h
              apply heq
              exact beq_iff_eq.mpr (eq_of_beq h).symm
            obtain ⟨code, hcode⟩ := ih (index + 1) exception shape htail
            exact ⟨code, by simp [pipelineExceptionCodes, lookupInfo, hne, hcode]⟩
      | decl declaredShape name value =>
          intro exception shape hmem
          exact ih index exception shape (by simpa [exceptionEntries] using hmem)
      | function declaration =>
          intro exception shape hmem
          exact ih index exception shape (by simpa [exceptionEntries] using hmem)
      | name struct fields =>
          intro exception shape hmem
          exact ih index exception shape (by simpa [exceptionEntries] using hmem)

/-! The finite-domain half of Cake get_eids_imp_excp_rel: the generated exception-code table has a lookup exactly when the source declaration list contains that exception. The code value remains abstract, matching Cake separate word-size and code-assignment premises. -/
theorem crepGetEidsFromDecls_lookup_iff_exception
    [BEq String] [LawfulBEq String]
    (fromNat : Nat → α) (index : Nat) :
    ∀ (declarations : List (Decl α)) (exception : ExceptionId),
      (∃ shape, (exception, shape) ∈ exceptionEntries declarations) ↔
        ∃ code, lookupInfo exception
          (pipelineExceptionCodes fromNat index declarations) = some code := by
  intro declarations
  induction declarations generalizing index with
  | nil =>
      intro exception
      simp [exceptionEntries, pipelineExceptionCodes, lookupInfo]
  | cons declaration declarations ih =>
      cases declaration with
      | exnDecl declaredException declaredShape =>
          intro exception
          by_cases heq : exception == declaredException
          · have heqEq : exception = declaredException := eq_of_beq heq
            subst exception
            simp [exceptionEntries, pipelineExceptionCodes, lookupInfo]
          · have hneq : exception ≠ declaredException := by
              intro h
              apply heq
              simp [h]
            have hne : (declaredException == exception) = false := by
              rw [Bool.eq_false_iff]
              intro h
              apply heq
              exact beq_iff_eq.mpr (eq_of_beq h).symm
            simpa [exceptionEntries, pipelineExceptionCodes, lookupInfo, heq, hne, hneq] using
              (ih (index + 1) exception)
      | decl declaredShape name value =>
          intro exception
          simpa [exceptionEntries, pipelineExceptionCodes, lookupInfo] using
            (ih index exception)
      | function declaration =>
          intro exception
          simpa [exceptionEntries, pipelineExceptionCodes, lookupInfo] using
            (ih index exception)
      | name struct fields =>
          intro exception
          simpa [exceptionEntries, pipelineExceptionCodes, lookupInfo] using
            (ih index exception)

def pipelineInlineNames : List (Decl α) → List FunName
  | [] => []
  | .function declaration :: declarations =>
      if declaration.inline then
        declaration.name :: pipelineInlineNames declarations
      else pipelineInlineNames declarations
  | _ :: declarations => pipelineInlineNames declarations
termination_by declarations => sizeOf declarations

/-! Faithful port of `pan_to_crep$compile_prog` from
    `cakeml/pancake/pan_to_crepScript.sml:393-398`.

    The source first builds the Crep table and then applies the inline pass to
    exactly the names of declarations marked `inlinable`; the callee body is
    recursively inlined before being spliced in (`crep_inlineScript.sml:215`). -/
def compileProgToCrep [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    List (CompiledFunction α) :=
  panToCrepCompileInlTop (pipelineInlineNames declarations)
    (compileToCrep context declarations)

/-! Cake's `first_compile_prog_all_distinct`
    (`pan_to_crepProofScript.sml:4556-4564`) at the complete
    `compile_prog` boundary.  The source declaration-name invariant first
    applies to `compile_to_crep`; the inline pass then preserves that table
    invariant because it changes only function bodies. -/
theorem compileProgToCrep_names_nodup
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (hnodup : (functionDeclarationNames declarations).Nodup) :
    (compileProgToCrep context declarations).map CompiledFunction.name |>.Nodup := by
  unfold compileProgToCrep
  apply panToCrepCompileInlTop_names_nodup
  exact compileToCrep_names_nodup context declarations hnodup

/-! Source-facing form of Cake's `first_compile_prog_all_distinct`: the
    distinctness premise is stated on the filtered function projection and
    the result includes the complete inline boundary. -/
theorem compileProgToCrep_names_nodup_of_functionDeclarations
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α))
    (hnodup : ((functionDeclarations declarations).map
      (fun declaration => declaration.name)).Nodup) :
    (compileProgToCrep context declarations).map CompiledFunction.name |>.Nodup := by
  unfold compileProgToCrep
  apply panToCrepCompileInlTop_names_nodup
  exact compileToCrep_names_nodup_of_functionDeclarations context declarations hnodup

/-! Cake's `compile_prog_distinct_params` at the complete source-shaped
    `compile_prog` boundary.  The pre-inline parameter invariant is supplied
    by `compileToCrep_params_nodup`; the inline pass preserves each record's
    parameter field. -/
theorem compileProgToCrep_params_nodup
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    ∀ function ∈ compileProgToCrep context declarations,
      function.params.Nodup := by
  unfold compileProgToCrep
  apply panToCrepCompileInlTop_params_nodup
  exact compileToCrep_params_nodup _ _

def pipelineFindFunction (name : FunName) :
    List (Decl α) → Option (FunDecl α)
  | [] => none
  | .function declaration :: declarations =>
      if declaration.name == name then some declaration
      else pipelineFindFunction name declarations
  | _ :: declarations => pipelineFindFunction name declarations
termination_by declarations => sizeOf declarations

/-! `pan_to_target_all` first moves the requested entry declaration to the
    front of the Pancake list (`pan_passesScript.sml:20-37`).  Keeping this
    source-order operation explicit is important because the linked section
    order is observable in the RISC-V artifact. -/
def panTargetMoveStartToFront [BEq String]
    (start : FunName) (declarations : List (Decl α)) : List (Decl α) :=
  globalDeclsFilter (fun declaration =>
      match declaration with
      | .function function => function.name == start
      | _ => false) declarations ++
    globalDeclsFilter (fun declaration =>
      match declaration with
      | .function function => function.name != start
      | _ => true) declarations

private theorem mem_of_mem_globalDeclsFilter {α : Type} {predicate : Decl α → Bool}
    {declaration : Decl α} {declarations : List (Decl α)}
    (hmem : declaration ∈ globalDeclsFilter predicate declarations) :
    declaration ∈ declarations := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def] at hmem; simp at hmem
  | cons head tail ih =>
      simp only [globalDeclsFilter] at hmem
      by_cases hpred : predicate head = true
      · simp [hpred] at hmem
        rcases hmem with heq | htail
        · subst heq; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem head (ih htail)
      · simp [hpred] at hmem
        exact List.mem_cons_of_mem head (ih hmem)

/-- Entry relocation preserves the declaration byte-range invariant because
    both output lists are filters of the input list. -/
theorem panTargetMoveStartToFront_byteRanged [BEq String] {width : Nat}
    (start : FunName) (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ d ∈ panTargetMoveStartToFront start declarations, DeclByteRanged d := by
  intro d hd
  unfold panTargetMoveStartToFront at hd
  rw [List.mem_append] at hd
  rcases hd with hd | hd
  · exact h d (mem_of_mem_globalDeclsFilter hd)
  · exact h d (mem_of_mem_globalDeclsFilter hd)

/-! Source-shaped port of CakeML Pancake's `exports_def`
    (`cakeml/pancake/pan_to_targetScript.sml:10`).  Export collection walks
    declarations in source order, keeps only exported functions, and ignores
    globals, exceptions, and structure declarations.  Keeping this as a
    separate executable helper preserves the observable export list without
    changing the target section ordering. -/
def panTargetExports : List (Decl α) → List FunName
  | [] => []
  | .function declaration :: declarations =>
      if declaration.exported then
        declaration.name :: panTargetExports declarations
      else
        panTargetExports declarations
  | _ :: declarations => panTargetExports declarations
termination_by declarations => sizeOf declarations

def pipelineCrepeContext [BEq α] [Add α]
    (bytesInWord : α) (fromNat : Nat → α)
    (program : GlobalCompiledProgram α) : CompileContext α :=
  { vars := []
    functions := []
    exceptions := crepGetEidsFromDecls fromNat program.declarations
    maxVar := 0
    bytesInWord := bytesInWord }

def pipelineCrepeCompileContext [BEq α] [Add α]
    (fromNat : Nat → α) (program : GlobalCompiledProgram α) :
    PanToCrepHOLContext α :=
  { vars := FEMPTY
    funcs := FEMPTY
    eids := FUPDATE_LIST FEMPTY (crepGetEidsFromDecls fromNat program.declarations)
    vmax := 0 }

/-- The executed RV64 compiler context obtains Cake's fixed byte width from
    the word type, not a caller-controlled field. -/
theorem pipelineCrepeCompileContext_riscv64
    (fromNat : Nat → BitVec 64) (program : GlobalCompiledProgram (BitVec 64)) :
    compileExpHOL (pipelineCrepeCompileContext fromNat program) .bytesInWord =
      ([.const CrepBytesInWord.bytesInWord], .one) := by
  simp [compileExpHOL]

/-- The production RV64 context lowers a structured load at Cake's fixed
    byte stride. -/
theorem compileExp_load_pipelineRiscv64
    (fromNat : Nat → BitVec 64) (program : GlobalCompiledProgram (BitVec 64))
    (shape : Shape) (expression : Exp (BitVec 64)) (head : CrepExp (BitVec 64))
    (rest : List (CrepExp (BitVec 64))) (shape' : Shape)
    (hcompile : compileExpHOL (pipelineCrepeCompileContext fromNat program)
      expression = (head :: rest, shape')) :
    (compileExpHOL (pipelineCrepeCompileContext fromNat program)
        (.load shape expression)).1 =
      loadShapeBytes 0 (Shape.shapeSize shape) head :=
  by
    simp only [compileExpHOL, hcompile]
    exact loadShape_eq_loadShapeBytes_of_stride_eq _ _ _ _ rfl

/-! Source-named ports of CakeML Pancake's `first_name_def` and
    `make_funcs_def` (`crep_to_loopScript.sml:243-255`).  The executable
    pipeline also needs a caller-selected label base when runtime sections
    reserve labels before user functions, so the parameterized helper keeps
    Cake's consecutive numbering while allowing that established ABI base. -/
def crepFirstName : Nat := 64

def crepMakeFuncsAt (firstName : Nat) :
    List (CompiledFunction α) → InfoMap (Nat × Nat)
  | [] => []
  | function :: functions =>
      (function.name, (firstName, function.params.length)) ::
        crepMakeFuncsAt (firstName + 1) functions

def crepMakeFuncs :
    List (CompiledFunction α) → InfoMap (Nat × Nat) :=
  crepMakeFuncsAt crepFirstName

def pipelineFunctionInfos (firstLabel : Nat) :
    List (CompiledFunction α) → InfoMap (Nat × Nat) :=
  crepMakeFuncsAt firstLabel

/-- Cake's `distinct_funcs` (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:60`):
    the numeric label assigned to a function is injective on the function
    names, in the list-backed `InfoMap` representation. -/
def crepDistinctFuncs (functions : InfoMap (Nat × Nat)) : Prop :=
  ∀ (x y : FunName) (n m : Nat) (rm rm' : Nat),
    lookupInfo x functions = some (n, rm) →
    lookupInfo y functions = some (m, rm') → n = m → x = y

theorem crepMakeFuncsAt_label_ge (start : Nat)
    (functions : List (CompiledFunction α)) :
    ∀ {x : FunName} {n rm : Nat},
      lookupInfo x (crepMakeFuncsAt start functions) = some (n, rm) →
        start ≤ n := by
  induction functions generalizing start with
  | nil => intro x n rm h; simp [crepMakeFuncsAt, lookupInfo] at h
  | cons function functions ih =>
      intro x n rm h
      simp only [crepMakeFuncsAt, lookupInfo] at h
      by_cases hc : (function.name == x) = true
      · rw [if_pos hc] at h
        have hpair := Option.some.inj h
        have : start = n := congrArg Prod.fst hpair
        omega
      · rw [if_neg hc] at h
        have := ih (start := start + 1) h
        omega

theorem crepDistinctFuncs_crepMakeFuncsAt (start : Nat)
    (functions : List (CompiledFunction α)) :
    crepDistinctFuncs (crepMakeFuncsAt start functions) := by
  intro x y n m rm rm' hx hy hnm
  induction functions generalizing start with
  | nil => simp [crepMakeFuncsAt, lookupInfo] at hx
  | cons function functions ih =>
      simp only [crepMakeFuncsAt, lookupInfo] at hx hy
      by_cases hcx : (function.name == x) = true
      · rw [if_pos hcx] at hx
        have hxn : start = n := congrArg Prod.fst (Option.some.inj hx)
        by_cases hcy : (function.name == y) = true
        · rw [if_pos hcy] at hy
          have hxname : x = function.name := (beq_iff_eq.mp hcx).symm
          have hyname : y = function.name := (beq_iff_eq.mp hcy).symm
          exact hxname.trans hyname.symm
        · rw [if_neg hcy] at hy
          have hge := crepMakeFuncsAt_label_ge (start := start + 1) functions hy
          omega
      · rw [if_neg hcx] at hx
        by_cases hcy : (function.name == y) = true
        · rw [if_pos hcy] at hy
          have hyn : start = m := congrArg Prod.fst (Option.some.inj hy)
          have hge := crepMakeFuncsAt_label_ge (start := start + 1) functions hx
          omega
        · rw [if_neg hcy] at hy
          exact ih (start := start + 1) hx hy

/-- Cake's `distinct_make_funcs`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3757`): the function
    table built by `make_funcs` has distinct labels. -/
theorem crepDistinctFuncs_crepMakeFuncs (functions : List (CompiledFunction α)) :
    crepDistinctFuncs (crepMakeFuncs functions) :=
  crepDistinctFuncs_crepMakeFuncsAt crepFirstName functions

/-- Cake's `initial_prog_make_funcs_el`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:3942`): the label a
    function receives from `make_funcs` identifies the position of that
    function in the source list.  CakeML writes the label of the `n`-th
    function as `n + first_name`; the list-backed Flapjack port instead
    inverts a successful lookup into the index whose label is
    `start + index`. -/
theorem crepMakeFuncsAt_exists_index (start : Nat)
    (functions : List (CompiledFunction α))
    {name : FunName} {label rm : Nat}
    (h : lookupInfo name (crepMakeFuncsAt start functions) = some (label, rm)) :
    ∃ n, label = start + n ∧
      (functions[n]?).map (fun function => function.name) = some name ∧
        n < functions.length := by
  induction functions generalizing start with
  | nil => simp [crepMakeFuncsAt, lookupInfo] at h
  | cons function functions ih =>
      simp only [crepMakeFuncsAt, lookupInfo] at h
      by_cases hc : (function.name == name) = true
      · rw [if_pos hc] at h
        have hlabel : label = start := (congrArg Prod.fst (Option.some.inj h)).symm
        exact ⟨0, by omega, by simp [beq_iff_eq.mp hc], by simp⟩
      · rw [if_neg hc] at h
        obtain ⟨n, hlabel, hget, hn⟩ := ih (start := start + 1) h
        refine ⟨n + 1, by omega, ?_, by simp; omega⟩
        simp only [List.getElem?_cons_succ]
        exact hget

/-- Cake's `initial_prog_make_funcs_el` for the `make_funcs` label base. -/
theorem crepMakeFuncs_exists_index (functions : List (CompiledFunction α))
    {name : FunName} {label rm : Nat}
    (h : lookupInfo name (crepMakeFuncs functions) = some (label, rm)) :
    ∃ n, label = crepFirstName + n ∧
      (functions[n]?).map (fun function => function.name) = some name ∧
        n < functions.length :=
  crepMakeFuncsAt_exists_index crepFirstName functions h

/-! Source-facing port of `crep_to_loop$compile_prog`.  Pancake's `comp_func`
    context sets `vmax = LENGTH params - 1`. -/
def pipelineLoopFunctionsSourceAux [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (functionInfos : InfoMap (Nat × Nat)) :
    Nat → List (CompiledFunction α) → List (Nat × List Nat × LoopProg α)
  | _, [] => []
  | label, function :: functions =>
      (label, List.range function.params.length,
        crepCompFunc architecture functionInfos function.params function.body) ::
        pipelineLoopFunctionsSourceAux architecture functionInfos (label + 1) functions

def pipelineLoopFunctionsSource [OfNat α 0] [OfNat α 1]
    (architecture : RiscV.Architecture) (firstLabel : Nat)
    (functions : List (CompiledFunction α)) :
    List (Nat × List Nat × LoopProg α) :=
  pipelineLoopFunctionsSourceAux architecture (pipelineFunctionInfos firstLabel functions)
    firstLabel functions

private theorem pipelineFunctionInfos_byteRanged {width : Nat}
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hnames : ∀ function ∈ functions, CrepNameRanged function.name) :
    ∀ entry ∈ pipelineFunctionInfos firstLabel functions,
      CrepNameRanged entry.1 := by
  induction functions generalizing firstLabel with
  | nil => simp [pipelineFunctionInfos, crepMakeFuncsAt]
  | cons function functions ih =>
      intro entry hentry
      change entry ∈
        (function.name, (firstLabel, function.params.length)) ::
          crepMakeFuncsAt (firstLabel + 1) functions at hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with hhead | htail
      · cases hhead
        exact hnames function (by simp)
      · exact ih (firstLabel + 1)
          (fun next hnext => hnames next (by simp [hnext])) entry htail

private def pipelineLoopFunctionsSourceExactAux {width : Nat} [NeZero width]
    (architecture : RiscV.Architecture) (functionInfos : InfoMap (Nat × Nat))
    (hFunctionNames : ∀ entry ∈ functionInfos, CrepNameRanged entry.1) :
    Nat → (programs : List (CompiledFunction (BitVec width))) →
      (∀ function ∈ programs, CrepProgNameRanged function.body) →
      List (Nat × List Nat × LoopProg (BitVec width))
  | _, [], _ => []
  | label, function :: programs, hBodies =>
      let hBody := hBodies function (by simp)
      let hTail : ∀ next ∈ programs, CrepProgNameRanged next.body := by
        intro next hnext
        exact hBodies next (by simp [hnext])
      (label, List.range function.params.length,
        crepCompFuncThroughHOLExact architecture functionInfos function.params
          function.body hBody hFunctionNames) ::
        pipelineLoopFunctionsSourceExactAux architecture functionInfos hFunctionNames
          (label + 1) programs hTail
termination_by _ programs _ => programs.length

/-- Rebase a function label from the exact compiler's generated interval to the
production pipeline's interval. This is Flapjack-only bridge infrastructure:
HOL's compiler does not perform this cross-pipeline label-space translation. -/
def rebaseHOLFunctionLabel (firstLabel functionCount label : Nat) : Nat :=
  if firstLoopName ≤ label && label < firstLoopName + functionCount then
    firstLabel + (label - firstLoopName)
  else
    label

/-- Structurally rebase function/code labels in executable Loop syntax. Only
direct call targets and `locValue` code sources in the generated function-label
interval change; break/continue labels are local control-flow labels. This is
an untagged Flapjack production bridge, not a HOL declaration. -/
def rebaseHOLFunctionLabels (firstLabel functionCount : Nat) :
    LoopProg α → LoopProg α
  | .skip => .skip
  | .assign name value => .assign name value
  | .primitive destinations operator arguments =>
      .primitive destinations operator arguments
  | .arith operation => .arith operation
  | .store address value => .store address value
  | .setGlobal address value => .setGlobal address value
  | .load32 address destination => .load32 address destination
  | .loadByte address destination => .loadByte address destination
  | .store32 address value => .store32 address value
  | .storeByte address value => .storeByte address value
  | .seq first second =>
      .seq (rebaseHOLFunctionLabels firstLabel functionCount first)
        (rebaseHOLFunctionLabels firstLabel functionCount second)
  | .ite operator condition right thenBranch elseBranch live =>
      .ite operator condition right
        (rebaseHOLFunctionLabels firstLabel functionCount thenBranch)
        (rebaseHOLFunctionLabels firstLabel functionCount elseBranch) live
  | .loop liveIn body liveOut =>
      .loop liveIn (rebaseHOLFunctionLabels firstLabel functionCount body) liveOut
  | .break label => .break label
  | .continue label => .continue label
  | .raise exception => .raise exception
  | .return values => .return values
  | .shMem operator name address => .shMem operator name address
  | .tick => .tick
  | .mark body =>
      .mark (rebaseHOLFunctionLabels firstLabel functionCount body)
  | .fail => .fail
  | .locValue destination source =>
      .locValue destination (rebaseHOLFunctionLabel firstLabel functionCount source)
  | .call returns target arguments handler =>
      let rebasedHandler :=
        match handler with
        | none => none
        | some (exception, first, second, live) =>
            some (exception,
              rebaseHOLFunctionLabels firstLabel functionCount first,
              rebaseHOLFunctionLabels firstLabel functionCount second,
              live)
      .call returns (target.map (rebaseHOLFunctionLabel firstLabel functionCount)) arguments
        rebasedHandler
  | .ffi function configuration configurationLength array arrayLength live =>
      .ffi function configuration configurationLength array arrayLength live
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [LoopProg.call.sizeOf_spec]; omega)

/-- The exact-carrier structural counterpart used to state the projection
commutation theorem. HOL has no declaration for cross-pipeline label rebasing;
this is Flapjack-only infrastructure and makes no claim about code tables or
runtime state references. -/
def rebaseHOLFunctionLabelsExact {width : Nat} [NeZero width]
    (firstLabel functionCount : Nat) : HolLoopProg width → HolLoopProg width
  | .skip => .skip
  | .assign name value => .assign name value
  | .primitive destinations operator arguments => .primitive destinations operator arguments
  | .arith operation => .arith operation
  | .store address value => .store address value
  | .setGlobal address value => .setGlobal address value
  | .load32 address destination => .load32 address destination
  | .loadByte address destination => .loadByte address destination
  | .store32 address value => .store32 address value
  | .storeByte address value => .storeByte address value
  | .seq first second =>
      .seq (rebaseHOLFunctionLabelsExact firstLabel functionCount first)
        (rebaseHOLFunctionLabelsExact firstLabel functionCount second)
  | .ite operator condition right thenBranch elseBranch live =>
      .ite operator condition right
        (rebaseHOLFunctionLabelsExact firstLabel functionCount thenBranch)
        (rebaseHOLFunctionLabelsExact firstLabel functionCount elseBranch) live
  | .loop liveIn body liveOut =>
      .loop liveIn (rebaseHOLFunctionLabelsExact firstLabel functionCount body) liveOut
  | .break label => .break label
  | .continue label => .continue label
  | .raise exception => .raise exception
  | .return values => .return values
  | .shMem operator name address => .shMem operator name address
  | .tick => .tick
  | .mark body => .mark (rebaseHOLFunctionLabelsExact firstLabel functionCount body)
  | .fail => .fail
  | .locValue destination source =>
      .locValue destination (rebaseHOLFunctionLabel firstLabel functionCount source)
  | .call returns target arguments handler =>
      let rebasedHandler :=
        match handler with
        | none => none
        | some (exception, first, second, live) =>
            some (exception,
              rebaseHOLFunctionLabelsExact firstLabel functionCount first,
              rebaseHOLFunctionLabelsExact firstLabel functionCount second,
              live)
      .call returns (target.map (rebaseHOLFunctionLabel firstLabel functionCount)) arguments
        rebasedHandler
  | .ffi function configuration configurationLength array arrayLength live =>
      .ffi function configuration configurationLength array arrayLength live
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [HolLoopProg.call.sizeOf_spec]; omega)

/-- The rebase is structural on the exact HOL syntax and its executable
projection. It changes only `locValue` code sources and direct call targets in
the generated function-label interval; local/register numbers, expressions,
call-handler variable IDs, break/continue labels, live sets, and FFI names are
preserved. This establishes only a syntax-level relation. The whole-program
bridge must separately relate code-table keys and runtime `WordLoc` values
before claiming execution equivalence. -/
theorem rebaseHOLFunctionLabels_projection {width : Nat} [NeZero width]
    (firstLabel functionCount : Nat) (program : HolLoopProg width) :
    rebaseHOLFunctionLabels firstLabel functionCount
        (holLoopProgToExecutableCanonical program) =
      holLoopProgToExecutableCanonical
        (rebaseHOLFunctionLabelsExact firstLabel functionCount program) := by
  let mProg : HolLoopProg width → Prop := fun p =>
    rebaseHOLFunctionLabels firstLabel functionCount
        (holLoopProgToExecutableCanonical p) =
      holLoopProgToExecutableCanonical
        (rebaseHOLFunctionLabelsExact firstLabel functionCount p)
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  change mProg program
  refine HolLoopProg.rec
      (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
      (motive_4 := mTriple) (motive_5 := mPair)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ program <;>
    simp_all [mProg, mPair, mTriple, mQuad, mHandler,
      rebaseHOLFunctionLabels, rebaseHOLFunctionLabelsExact,
      holLoopProgToExecutableCanonical, holLoopProgToExecutable]
  case refine_23 =>
    intro returns target arguments handler hHandler
    cases handler with
    | none =>
        simp [rebaseHOLFunctionLabels, rebaseHOLFunctionLabelsExact,
          holLoopProgToExecutable]

    | some value =>
        rcases value with ⟨exception, first, second, live⟩
        rcases hHandler with ⟨hFirst, hSecond⟩
        simp [rebaseHOLFunctionLabels, rebaseHOLFunctionLabelsExact,
          holLoopProgToExecutable, hFirst, hSecond]

/-- Flapjack production adapter around exact whole-program `compile_prog_def`:
it converts byte-ranged production names to `MlString`, projects exact
`HolLoopProg`, and rebases function labels to this caller's label base. This is
not itself a HOL declaration or a claim that code-table/runtime-state
relations follow from syntax projection. -/
def pipelineLoopFunctionsSourceCompileProgExact {width : Nat} [NeZero width]
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (_hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (_hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    List (Nat × List Nat × LoopProg (BitVec width)) :=
  let holPrograms := functions.map fun function =>
    (Flapjack.Basis.Pure.MlString.ofString function.name, function.params,
      crepProgToHOL function.body)
  (compileProgHOLExact .riscv holPrograms).map fun (label, parameters, body) =>
      (rebaseHOLFunctionLabel firstLabel functions.length label, parameters,
      rebaseHOLFunctionLabels firstLabel functions.length
        (holLoopProgToExecutableCanonical body))

/-- Tested alternative, NOT executed: a per-function source-pipeline route
through exact `compile_def`/`ocompile_def` whenever all compiled-body names and
sibling function keys lie in HOL `mlstring`'s byte range (runtime guard, with
fallback to the production route). The executed route is
`pipelineLoopFunctionsSource` (PR #1174 review). -/
def pipelineLoopFunctionsSourceRouted {width : Nat} [NeZero width]
    (architecture : RiscV.Architecture) (firstLabel : Nat)
    (functions : List (CompiledFunction (BitVec width))) :
    List (Nat × List Nat × LoopProg (BitVec width)) :=
  let functionInfos := pipelineFunctionInfos firstLabel functions
  let byteRanged := functions.all (fun function =>
    CrepNameRangedBool function.name && CrepProgNameRangedBool function.body)
  if hRanged : byteRanged = true then
    have hEach : ∀ function ∈ functions,
        CrepNameRangedBool function.name && CrepProgNameRangedBool function.body := by
      change functions.all (fun function =>
        CrepNameRangedBool function.name && CrepProgNameRangedBool function.body) = true
        at hRanged
      simpa only [List.all_eq_true] using hRanged
    have hNames : ∀ function ∈ functions, CrepNameRanged function.name := by
      intro function hfunction
      have h := hEach function hfunction
      have ⟨hname, _⟩ : CrepNameRangedBool function.name = true ∧
          CrepProgNameRangedBool function.body = true := by simpa using h
      exact crepNameRangedBool_eq_true_iff function.name |>.mp hname
    have hBodies : ∀ function ∈ functions, CrepProgNameRanged function.body := by
      intro function hfunction
      have h := hEach function hfunction
      have ⟨_, hbody⟩ : CrepNameRangedBool function.name = true ∧
          CrepProgNameRangedBool function.body = true := by simpa using h
      exact (crepProgNameRangedBool_eq_true_iff function.body).mp hbody
    pipelineLoopFunctionsSourceExactAux architecture functionInfos
      (pipelineFunctionInfos_byteRanged firstLabel functions hNames)
      firstLabel functions hBodies
  else
    pipelineLoopFunctionsSourceAux architecture functionInfos firstLabel functions

/-! Tested alternative, NOT executed: a Crep-to-Loop route through exact
whole-program `compile_prog_def`. The runtime byte-range guard prevents lossy
conversion of production String names to HOL `mlstring` and otherwise falls
back to the production route; the exact HOL label range is rebased to the
selected label base. No compiler entrypoint calls it until its output equality
with `pipelineLoopFunctionsSource` is proved (PR #1174 review); the executed
route is `pipelineLoopFunctionsSource`. -/
def pipelineLoopFunctionsSourceCompileProgRouted {width : Nat} [NeZero width]
    (architecture : RiscV.Architecture) (firstLabel : Nat)
    (functions : List (CompiledFunction (BitVec width))) :
    List (Nat × List Nat × LoopProg (BitVec width)) :=
  let functionInfos := pipelineFunctionInfos firstLabel functions
  let byteRanged := functions.all (fun function =>
    CrepNameRangedBool function.name && CrepProgNameRangedBool function.body)
  if hRanged : byteRanged = true then
    have hEach : ∀ function ∈ functions,
        CrepNameRangedBool function.name && CrepProgNameRangedBool function.body := by
      change functions.all (fun function =>
        CrepNameRangedBool function.name && CrepProgNameRangedBool function.body) = true
        at hRanged
      simpa only [List.all_eq_true] using hRanged
    have hNames : ∀ function ∈ functions, CrepNameRanged function.name := by
      intro function hfunction
      have h := hEach function hfunction
      have ⟨hname, _⟩ : CrepNameRangedBool function.name = true ∧
          CrepProgNameRangedBool function.body = true := by simpa using h
      exact crepNameRangedBool_eq_true_iff function.name |>.mp hname
    have hBodies : ∀ function ∈ functions, CrepProgNameRanged function.body := by
      intro function hfunction
      have h := hEach function hfunction
      have ⟨_, hbody⟩ : CrepNameRangedBool function.name = true ∧
          CrepProgNameRangedBool function.body = true := by simpa using h
      exact (crepProgNameRangedBool_eq_true_iff function.body).mp hbody
    pipelineLoopFunctionsSourceCompileProgExact firstLabel functions hNames hBodies
  else
    pipelineLoopFunctionsSourceAux architecture functionInfos firstLabel functions

/-- On the checked name-ranged fragment, the parser-backed production wrapper
returns exactly the label-rebased executable projection of the exact whole
`compile_prog_def` result. The premise is the runtime guard's logical form and
discharges each production String-to-HOL MlString conversion. This theorem is
about the compiler output only; relating any incoming state containing
`WordLoc` values to the rebased code table remains a separate obligation. -/
theorem pipelineLoopFunctionsSourceCompileProgRouted_exact
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    pipelineLoopFunctionsSourceCompileProgRouted architecture firstLabel functions =
      (compileProgHOLExact .riscv (functions.map fun function =>
        (Flapjack.Basis.Pure.MlString.ofString function.name, function.params,
          crepProgToHOL function.body))).map fun (label, parameters, body) =>
        (rebaseHOLFunctionLabel firstLabel functions.length label, parameters,
          rebaseHOLFunctionLabels firstLabel functions.length
            (holLoopProgToExecutableCanonical body)) := by
  have hByteRanged : functions.all (fun function =>
      CrepNameRangedBool function.name && CrepProgNameRangedBool function.body) = true := by
    apply List.all_eq_true.mpr
    intro function hFunction
    have hName := (crepNameRangedBool_eq_true_iff function.name).mpr
      (hFunctionNames function hFunction)
    have hBody := (crepProgNameRangedBool_eq_true_iff function.body).mpr
      (hProgramNames function hFunction)
    simp [hName, hBody]
  simp [pipelineLoopFunctionsSourceCompileProgRouted, hByteRanged,
    pipelineLoopFunctionsSourceCompileProgExact]

/-- Each indexed row from the source-routed exact whole-program compiler is
stored at the caller's corresponding production function label. This is the
per-row key component of the code-table bridge, not a state/evaluation theorem.
HOL `compile_prog_def` fixes its label base at `first_name`; translating those
rows to this caller-selected base is Flapjack-only infrastructure, so this
theorem has no separate HOL original. -/
theorem pipelineLoopFunctionsSourceCompileProgRouted_rowLabel
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body)
    (index : Nat) (hindex : index < functions.length) :
    ((pipelineLoopFunctionsSourceCompileProgRouted architecture firstLabel functions)[index]?).map
        Prod.fst = some (firstLabel + index) := by
  rw [pipelineLoopFunctionsSourceCompileProgRouted_exact architecture firstLabel functions
    hFunctionNames hProgramNames]
  have hreb : rebaseHOLFunctionLabel firstLabel functions.length
      (firstLoopName + index) = firstLabel + index := by
    simp [rebaseHOLFunctionLabel, firstLoopName]
    omega
  have hreb' : rebaseHOLFunctionLabel firstLabel functions.length
      (index + 64) = firstLabel + index := by
    rw [show index + 64 = firstLoopName + index by simp [firstLoopName, Nat.add_comm]]
    exact hreb
  simp [compileProgHOLExact, firstLoopName, hreb', hindex]

/-- Every body emitted by the parser-backed source route is related to the
corresponding exact `compile_prog_def` body after the same structural label
rebase. This carries the syntax-level relation through the complete routed
list, including direct-call target rebasing inside bodies. It does not relate
the caller's name-indexed context or target code table, nor runtime states;
those remain separate obligations. This bridge has no separate HOL original. -/
theorem pipelineLoopFunctionsSourceCompileProgRouted_body_rel
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body) :
    ∀ entry ∈ pipelineLoopFunctionsSourceCompileProgRouted architecture firstLabel functions,
      ∃ faithfulBody : HolLoopProg width,
        loopProgExecRel entry.2.2 faithfulBody := by
  intro entry hentry
  rw [pipelineLoopFunctionsSourceCompileProgRouted_exact architecture firstLabel functions
    hFunctionNames hProgramNames] at hentry
  simp only [List.mem_map] at hentry
  rcases hentry with ⟨exactEntry, hexactEntry, hentry⟩
  cases hentry
  refine ⟨rebaseHOLFunctionLabelsExact firstLabel functions.length exactEntry.2.2, ?_⟩
  rw [rebaseHOLFunctionLabels_projection]
  exact holLoopProgToExecutableCanonical_rel _

/-- Indexing the parser-backed source route commutes with its exact
`compile_prog_def` list mapping: each present row has the same rebased label
and parameters, and its body is the structural executable projection of that
exact row's rebased HOL body. This explicitly preserves the association
between source-list position and emitted code-row contents; it still does not
state a name-map or runtime-state relation. HOL `compile_prog_def` fixes the
`first_name` label base and has no parser-backed caller-label adapter, so this
wrapper theorem has no separate HOL original. -/
theorem pipelineLoopFunctionsSourceCompileProgRouted_indexedExact
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body)
    (index : Nat) :
    (pipelineLoopFunctionsSourceCompileProgRouted architecture firstLabel functions)[index]? =
      ((compileProgHOLExact .riscv (functions.map fun function =>
        (Flapjack.Basis.Pure.MlString.ofString function.name, function.params,
          crepProgToHOL function.body)))[index]?).map
        (fun (label, parameters, body) =>
          (rebaseHOLFunctionLabel firstLabel functions.length label, parameters,
            rebaseHOLFunctionLabels firstLabel functions.length
              (holLoopProgToExecutableCanonical body))) := by
  rw [pipelineLoopFunctionsSourceCompileProgRouted_exact architecture firstLabel functions
    hFunctionNames hProgramNames]
  simp

/-- A successful lookup in the production name-indexed function context points
to the routed output row at the same source-list position. Its label is both
the production `firstLabel + index` assignment and the key of that output row.
Together with `indexedExact`, the row's body is paired position-for-position
with the rebased exact `compile_prog_def` body. This only bridges context keys
to the compiler's emitted list; no Spt/code-state or evaluator relation is
asserted here. HOL `compile_prog_def` has no declaration relating its fixed
`mlstring`/`first_name` inputs to this parser-backed String/InfoMap caller, so
this Flapjack bridge theorem has no separate HOL original. -/
theorem pipelineLoopFunctionsSourceCompileProgRouted_lookupRowKey
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body)
    {name : FunName} {label arity : Nat}
    (hlookup : lookupInfo name (pipelineFunctionInfos firstLabel functions) =
      some (label, arity)) :
    ∃ index, index < functions.length ∧
      (functions[index]?).map (fun function => function.name) = some name ∧
      label = firstLabel + index ∧
      ((pipelineLoopFunctionsSourceCompileProgRouted architecture firstLabel functions)[index]?).map
        Prod.fst = some label := by
  change lookupInfo name (crepMakeFuncsAt firstLabel functions) =
    some (label, arity) at hlookup
  obtain ⟨index, hlabel, hname, hindex⟩ :=
    crepMakeFuncsAt_exists_index firstLabel functions hlookup
  refine ⟨index, hindex, hname, hlabel, ?_⟩
  rw [pipelineLoopFunctionsSourceCompileProgRouted_rowLabel architecture firstLabel
    functions hFunctionNames hProgramNames index hindex]
  exact congrArg some hlabel.symm

/-- A production context lookup selects the same indexed output row as exact
`compile_prog_def`, after projecting that exact row through caller-label/body
rebasing. The emitted list row is the production compiler's table entry at
this boundary. The result does not introduce a synthetic Spt runtime carrier
or claim equality with an evaluator's `code` field; the latter is a separate
HOL state-relation obligation. This Flapjack-only bridge has no HOL original
because HOL `compile_prog_def` has no caller `InfoMap`/label-rebase wrapper. -/
theorem pipelineLoopFunctionsSourceCompileProgRouted_lookupExactRow
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (firstLabel : Nat) (functions : List (CompiledFunction (BitVec width)))
    (hFunctionNames : ∀ function ∈ functions, CrepNameRanged function.name)
    (hProgramNames : ∀ function ∈ functions, CrepProgNameRanged function.body)
    {name : FunName} {label arity : Nat}
    (hlookup : lookupInfo name (pipelineFunctionInfos firstLabel functions) =
      some (label, arity)) :
    ∃ index, index < functions.length ∧
      (functions[index]?).map (fun function => function.name) = some name ∧
      label = firstLabel + index ∧
      (pipelineLoopFunctionsSourceCompileProgRouted architecture firstLabel
        functions)[index]? =
        ((compileProgHOLExact .riscv (functions.map fun function =>
          (Flapjack.Basis.Pure.MlString.ofString function.name, function.params,
            crepProgToHOL function.body)))[index]?).map
          (fun (exactLabel, parameters, body) =>
            (rebaseHOLFunctionLabel firstLabel functions.length exactLabel,
              parameters, rebaseHOLFunctionLabels firstLabel functions.length
                (holLoopProgToExecutableCanonical body))) := by
  obtain ⟨index, hindex, hname, hlabel, _hrouteLabel⟩ :=
    pipelineLoopFunctionsSourceCompileProgRouted_lookupRowKey architecture firstLabel
      functions hFunctionNames hProgramNames hlookup
  refine ⟨index, hindex, hname, hlabel, ?_⟩
  exact pipelineLoopFunctionsSourceCompileProgRouted_indexedExact architecture
    firstLabel functions hFunctionNames hProgramNames index

/-! ### Exact-carrier bridge for the source-routed Loop output

The tested alternative `pipelineLoopFunctionsSourceRouted` uses
`crepCompFuncThroughHOLExact` when all function and body names are
byte-ranged (it is not executed by the compiler). This bridge records the resulting
executable `LoopProg` bodies against the exact `HolLoopProg` carrier. The
generic fallback is deliberately excluded: arbitrary Lean `String` names do
not embed into HOL `mlstring` without the byte-range premise. -/

private theorem pipelineLoopFunctionsSourceExactAux_body_rel
    {width : Nat} [NeZero width] (architecture : RiscV.Architecture)
    (functionInfos : InfoMap (Nat × Nat))
    (hFunctionNames : ∀ entry ∈ functionInfos, CrepNameRanged entry.1) :
    ∀ (firstLabel : Nat) (programs : List (CompiledFunction (BitVec width)))
      (hBodies : ∀ function ∈ programs, CrepProgNameRanged function.body)
      (entry : Nat × List Nat × LoopProg (BitVec width))
      (_hentry : entry ∈ pipelineLoopFunctionsSourceExactAux architecture functionInfos
        hFunctionNames firstLabel programs hBodies),
      ∃ faithfulBody : HolLoopProg width,
        loopProgExecRel entry.2.2 faithfulBody := by
  intro firstLabel programs
  induction programs generalizing firstLabel with
  | nil =>
      intro hBodies entry hentry
      simp [pipelineLoopFunctionsSourceExactAux] at hentry
  | cons function programs ih =>
      intro hBodies entry hentry
      simp only [pipelineLoopFunctionsSourceExactAux, List.mem_cons] at hentry
      rcases hentry with hhead | htail
      · rw [hhead]
        let context : LoopContext (BitVec width) :=
          crepMkCtxt architecture (crepMakeVmap function.params) functionInfos
            (function.params.length - 1)
        let exactContext := productionLoopContextToExact context
        let faithfulBody := optimiseHOL (compFuncHOLExact exactContext.target
          exactContext.funcs function.params (crepProgToHOL function.body))
        refine ⟨faithfulBody, ?_⟩
        simpa [pipelineLoopFunctionsSourceExactAux,
          crepCompFuncThroughHOLExact, context, exactContext, faithfulBody] using
          crepCompFuncThroughHOLExact_rel architecture functionInfos
            function.params function.body (hBodies function (by simp))
            hFunctionNames
      · exact ih (firstLabel + 1)
          (fun next hnext => hBodies next (by simp [hnext])) entry
          (by simpa only [pipelineLoopFunctionsSourceExactAux] using htail)

/-- Every function body emitted by the actual source-routed pipeline under its
byte-range guard is related to a body in the exact `HolLoopProg` carrier. The
program projection is the reviewed `loopProgExecRel` bridge. The exact state
relation is `LoopSemStateFiniteExact.prodRel` and is used when relating
evaluation states; this theorem itself does not claim evaluator result
correspondence or an executed CLI evaluation path. -/
theorem pipelineLoopFunctionsSourceRouted_body_rel {width : Nat} [NeZero width]
    (architecture : RiscV.Architecture) (firstLabel : Nat)
    (functions : List (CompiledFunction (BitVec width)))
    (hRanged : functions.all (fun function =>
      CrepNameRangedBool function.name && CrepProgNameRangedBool function.body) = true) :
    ∀ entry ∈ pipelineLoopFunctionsSourceRouted architecture firstLabel functions,
      ∃ faithfulBody : HolLoopProg width,
        loopProgExecRel entry.2.2 faithfulBody := by
  have hEach : ∀ function ∈ functions,
      CrepNameRangedBool function.name && CrepProgNameRangedBool function.body := by
    simpa only [List.all_eq_true] using hRanged
  have hNames : ∀ function ∈ functions, CrepNameRanged function.name := by
    intro function hfunction
    have ⟨hname, _⟩ : CrepNameRangedBool function.name = true ∧
        CrepProgNameRangedBool function.body = true := by
      simpa using hEach function hfunction
    exact crepNameRangedBool_eq_true_iff function.name |>.mp hname
  have hBodies : ∀ function ∈ functions, CrepProgNameRanged function.body := by
    intro function hfunction
    have ⟨_, hbody⟩ : CrepNameRangedBool function.name = true ∧
        CrepProgNameRangedBool function.body = true := by
      simpa using hEach function hfunction
    exact (crepProgNameRangedBool_eq_true_iff function.body).mp hbody
  have hFunctionNames : ∀ entry ∈ pipelineFunctionInfos firstLabel functions,
      CrepNameRanged entry.1 :=
    pipelineFunctionInfos_byteRanged firstLabel functions hNames
  unfold pipelineLoopFunctionsSourceRouted
  simp only [dif_pos hRanged]
  exact pipelineLoopFunctionsSourceExactAux_body_rel architecture
    (pipelineFunctionInfos firstLabel functions) hFunctionNames firstLabel
    functions hBodies

/-! Source-facing port of `loop_to_word$compile_prog`.  CakeML rebuilds a
    dense even-register context from
    `params ++ fromNumSet (difference (acc_vars body) params)`.  Use that
    context for source-entry artifacts, including the identity lowering path;
    otherwise the identity path can disagree with the full-SSA fallback on
    programs whose assigned variables are sparse. -/
def pipelineWordFunctionsSource [OfNat α 1]
    (functions : List (Nat × List Nat × LoopProg α)) :
    List (Nat × List Nat × WordProg α) :=
  functions.map (fun (label, parameters, body) =>
    (label, LoopToWord.loopToWordCompParameters parameters body,
      wordProgDCE (LoopToWord.loopToWordCompFunc label parameters body)))

/-- Fixed-width production source route for `compile_prog`. Encodable Loop
    syntax with byte-ranged FFI names uses exact HOL `comp_func` followed by
    the reviewed WordProg projection; executable-only `crepOp`/`cmp` syntax or
    non-byte FFI names retain the compatibility implementation. -/
def pipelineWordFunctionsSourceRouted {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width))) :
    List (Nat × List Nat × WordProg (BitVec width)) :=
  functions.map (fun (label, parameters, body) =>
    (label, loopToWordCompParametersRouted parameters body,
      wordProgDCE (loopToWordCompFuncRouted label parameters body)))

/-! Source-shaped `loop_to_word$compile_prog` output.  The ordinary pipeline
    keeps parameter names for later register allocation; `pan_to_word` instead
    exposes each function's source label, arity (including the entry slot), and
    compiled body. -/
def pipelineWordCompileProg [OfNat α 1]
    (functions : List (Nat × List Nat × LoopProg α)) :
    List (Nat × Nat × WordProg α) :=
  LoopToWord.loopToWordCompileProg functions

def panToWordCompileProgCompat [OfNat α 1]
    (functions : List (Nat × List Nat × LoopProg α)) :
    List (Nat × Nat × WordProg α) :=
  pipelineWordCompileProg functions

/-- Fixed-width `pan_to_word$compile_prog` production route. -/
def panToWordCompileProgRouted {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width))) :
    List (Nat × Nat × WordProg (BitVec width)) :=
  functions.map (fun (label, parameters, body) =>
    (label, parameters.length + 1, loopToWordCompFuncRouted label parameters body))

/-- The executed fixed-width `pan_to_word$compile_prog` route. The generic
    compatibility helper remains available for non-word carrier experiments. -/
def panToWordCompileProg {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width))) :
    List (Nat × Nat × WordProg (BitVec width)) :=
  panToWordCompileProgRouted functions

/-! Full-SSA Lab sections use label 0 for their public entry and label 1 for
    the tail-sequence entry marker.  Handler labels are function-specific, so
    continuation labels must also start above every function label; otherwise
    a handler in the highest-numbered function can alias its call continuation.
    This helper computes that fresh lower bound from the generated functions. -/
def fullSsaInitialLabLabel : List (Nat × List Nat × StackProg Nat) → Nat
  | [] => 2
  | (label, _, _) :: functions =>
      max (label + 1) (fullSsaInitialLabLabel functions)

theorem lookupNatInfo_map_add_two_of_mem (slots : List Nat) (name : Nat)
    (hname : name ∈ slots) :
    lookupNatInfo name (slots.map (fun value => (value, value + 2))) =
      some (name + 2) := by
  induction slots with
  | nil => simp at hname
  | cons head tail ih =>
      simp only [List.mem_cons] at hname
      rcases hname with rfl | hname
      · simp [lookupNatInfo]
      · by_cases heq : head == name
        · have : head = name := by simpa using heq
          subst head
          simp [lookupNatInfo]
        · simp [lookupNatInfo, heq, ih hname]

def pipelineWordContext (slots : List Nat) : WordContext :=
  { vars := slots.map (fun name => (name, name + 2)) }

theorem wordFindVar_pipelineWordContext_of_mem (slots : List Nat) (name : Nat)
    (hname : name ∈ slots) :
    wordFindVar (pipelineWordContext slots) name = name + 2 := by
  simp [pipelineWordContext, wordFindVar,
    lookupNatInfo_map_add_two_of_mem slots name hname]

def pipelinePrependInitializers (initializers : List (Prog α)) :
    List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      if declaration.name = "main" then
        .function { declaration with body :=
          (.seq (nestedSeq initializers) declaration.body) } :: declarations
      else
        .function declaration :: pipelinePrependInitializers initializers declarations
  | declaration :: declarations =>
      declaration :: pipelinePrependInitializers initializers declarations

structure FlapjackPipelineResult (α : Type u) where
  simplified : List (Decl α)
  structured : List (Decl α)
  globals : GlobalCompiledProgram α
  crepe : List (CompiledFunction α)
  loop : List (Nat × List Nat × LoopProg α)
  word : List (Nat × List Nat × WordProg α)

/-! Typed output-boundary port of Cake's `pan_compile_tap_def`
    (`pan_passesScript.sml:668-674`).  The pass pipeline supplies the
    already-computed output and typed intermediate stages; this wrapper keeps
    Cake's exact explore-flag behavior and `pp_with_title` ordering. -/
def panCompileTapReports [CakeDisplayWord α]
    (stages : List (String × AnyPanProg α)) : List String :=
  match stages with
  | [] => []
  | (title, stage) :: stages =>
      ["# ", title, "\n\n"] ++ anyPanProgPp stage ++
        panCompileTapReports stages

def panCompileTap [CakeDisplayWord α]
    (exploreFlag : Bool) (output : β)
    (stages : List (String × AnyPanProg α)) : β × List String :=
  if exploreFlag then
    (output, panCompileTapReports stages)
  else
    (output, [])

/-! Source-facing Pancake compiler entry point. This executes the fixed-interface
    `globalCompileTopCake` result at the global pass boundary.  The remaining
    metadata is retained from `globalCompileTop` for callers that inspect the
    intermediate pipeline record; the declarations sent into Crep are the
    direct output of Cake's tagged `compile_top`. Parser-backed production
    entrypoints provide the byte-range proof composed through the earlier
    passes, selecting `structCompileTopHOLExactOfByteRanged` (which executes the
    reviewed exact top, declaration, program, expression, shape and old-shape compilers through their codecs), `globalCompileTopCakeRouted` (which executes
    the reviewed exact `compileTopExactHOL` for a byte-ranged start name), and
    `compileProgNativeWithMetadataRouted` at the
    declaration-to-Crep boundary. With standard BitVec literals that branch executes
    the reviewed exact whole declaration compiler and exact inliner, then decodes
    for the existing production metadata representation;
    `compileFlapjackEntryCake_ofExact_eq` below proves the whole pipeline result
    equals the compatibility route. Crep-to-Loop is the single production route
    `pipelineLoopFunctionsSource`, which the CLI drivers reuse. The exact
    `compile_prog`/`comp_func` Crep-to-Loop routes are
    tested alternatives only, until their output equality is proved.
    The optional proof preserves this helper's source compatibility
    for callers that do not carry the codec invariant. -/
def compileFlapjackEntryCake {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1] [Add (BitVec width)] [Mul (BitVec width)]
    [AndOp (BitVec width)] [ShiftRight (BitVec width)]
    [PanShiftWidth (BitVec width)]
    (architecture : RiscV.Architecture) (bytesInWord : BitVec width)
    (fromNat : Nat → BitVec width) (start : FunName)
    (declarations : List (Decl (BitVec width)))
    (hdeclarations : Option (Decidable
      (∀ declaration ∈ declarations, DeclByteRanged declaration)) := none) :
    Option (FlapjackPipelineResult (BitVec width)) :=
  let moved := panTargetMoveStartToFront start declarations
  let simplified := panSimpDecls moved
  let structured :=
    match hdeclarations with
    | some (.isTrue hinput) =>
        let hmoved := panTargetMoveStartToFront_byteRanged start declarations hinput
        let hsimplified := panSimpDecls_byteRanged moved hmoved
        structCompileTopHOLExactOfByteRanged simplified hsimplified
    | _ => structCompileTop simplified
  let compiled :=
    match hproof : hdeclarations with
    | some (.isTrue hinput) =>
        let hmoved := panTargetMoveStartToFront_byteRanged start declarations hinput
        let hsimplified := panSimpDecls_byteRanged moved hmoved
        let hstructured : ∀ declaration ∈ structured, DeclByteRanged declaration := by
          simpa only [structured, hproof, structCompileTopHOLExact_eq_legacyOfByteRanged]
            using structCompileTop_byteRanged simplified hsimplified
        let cakeDeclarations := globalCompileTopCakeRouted structured start hstructured
        let hcake := globalCompileTopCakeRouted_byteRanged structured start hstructured
        (cakeDeclarations, compileProgNativeWithMetadataRouted cakeDeclarations hcake)
    | _ =>
        let cakeDeclarations := globalCompileTopCake structured start
        (cakeDeclarations, compileProgTopHOLWithMetadata cakeDeclarations)
  let cakeDeclarations := compiled.1
  match cakeDeclarations with
  | [] => none
  | _ :: _ =>
      let renamed := globalNewMainName structured
      let prepared := globalRenameDecls start renamed (globalResortDecls structured)
      let metadata := globalCompileTop bytesInWord fromNat prepared
      let globals := { metadata with declarations := cakeDeclarations }
      let crepe := crepSimpFunctions fromNat compiled.2
      let loop := pipelineLoopFunctionsSource architecture 1 crepe
      let word := pipelineWordFunctionsSourceRouted loop
      some (FlapjackPipelineResult.mk simplified structured globals crepe loop word)

/-- The parser-proved exact-carrier route returns the same entire pipeline
    result as the compatibility route. This composes the reviewed struct,
    global and declaration-to-Crep pass
    equalities at the entrypoint, so the optional proof changes which tagged
    definitions execute, not the compiler output. -/
theorem compileFlapjackEntryCake_ofExact_eq {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1] [Add (BitVec width)] [Mul (BitVec width)]
    [AndOp (BitVec width)] [ShiftRight (BitVec width)]
    [PanShiftWidth (BitVec width)]
    (architecture : RiscV.Architecture) (bytesInWord : BitVec width)
    (fromNat : Nat → BitVec width) (start : FunName)
    (declarations : List (Decl (BitVec width)))
    (h : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    compileFlapjackEntryCake architecture bytesInWord fromNat start declarations
        (some (.isTrue h)) =
      compileFlapjackEntryCake architecture bytesInWord fromNat start declarations none := by
  unfold compileFlapjackEntryCake
  simp only [structCompileTopHOLExact_eq_legacyOfByteRanged, globalCompileTopCakeRouted_eq,
    compileProgNativeWithMetadataRouted_eq]

/-! Executable mirror of the missing-`main` branch of `pan_to_target_all`
    (`cakeml/pancake/pan_passesScript.sml:20-37`): when the program has no
    `main` declaration the original synthesizes `main = «return 0»` and
    prepends it before running the remaining passes. -/
def panTargetDeclarationsWithDefaultMain [OfNat α 0] [OfNat α 1]
    (declarations : List (Decl α)) : List (Decl α) :=
  if declarations.any (fun declaration =>
      match declaration with
      | .function function => function.name == "main"
      | _ => false) then
    declarations
  else match declarations with
    | [] => []
    | _ =>
      .function
        { name := "main", inline := false, exported := false, params := [],
          body := .return (.const 0), returnShape := .one } :: declarations

/-- The target's synthetic default entry uses only byte-range-safe literals,
    so adding it preserves the parser's declaration codec premise. -/
theorem panTargetDeclarationsWithDefaultMain_byteRanged {width : Nat}
    [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (h : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ∀ declaration ∈ panTargetDeclarationsWithDefaultMain declarations,
      DeclByteRanged declaration := by
  unfold panTargetDeclarationsWithDefaultMain
  split
  · exact h
  · cases declarations with
    | nil => simp [DeclByteRanged]
    | cons first rest =>
        intro declaration hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with heq | hrest
        · subst declaration
          simp [DeclByteRanged, FunDeclByteRanged, ProgByteRanged,
            ExpByteRanged, NameRanged, ShapeByteRanged, ListParamByteRanged]
        · exact h declaration (by simp [hrest])

end Flapjack
