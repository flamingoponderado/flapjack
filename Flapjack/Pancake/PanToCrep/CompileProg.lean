import Flapjack.HolRef
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.PanToCrep.CompileExpBridge
import Flapjack.Pancake.PanToCrep.ContextProductionEvidence
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanLang.ProgHOLInduction

/-!
HOL-shaped top-level Pancake-to-Crep compiler boundary. The per-function
exact adapter here retains the production inliner and is proved equal to the
compatibility route. The parser-backed pipeline now uses
`compileProgNativeWithMetadataRouted` in `CompileProgCorrespondence`: with
standard BitVec literals it executes the reviewed exact whole declaration
compiler and exact inliner, then decodes for production metadata. The separate
`compileProgTopHOLProductionExactInline` variant remains an unused alternative.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

private def panToCrepShapeSlotsExact : List ShapeHOL → Nat → List (List Nat)
  | [], _ => []
  | shape :: shapes, offset =>
      (List.range (sizeOfShapeHOL shape)).map (offset + ·) ::
        panToCrepShapeSlotsExact shapes (offset + sizeOfShapeHOL shape)

/-- The exact `with_shape` partition of the global slot range gives the same
    per-parameter slots as the production allocator's increasing offset. This
    is the allocation fact needed before replacing the executed production
    `compFuncHOL` call with the tagged HOL-shaped `compFuncExactHOLW`. -/
private theorem withShapeHOL_range_offset (shapes : List ShapeHOL) (offset : Nat) :
    withShapeHOL shapes
        ((List.range (sizeOfShapeHOL (.comb shapes))).map (offset + ·)) =
      panToCrepShapeSlotsExact shapes offset := by
  induction shapes generalizing offset with
  | nil => simp [withShapeHOL, panToCrepShapeSlotsExact]
  | cons shape shapes ih =>
      simp only [withShapeHOL, panToCrepShapeSlotsExact, sizeOfShapeHOL,
        sizeOfShapesHOL]
      rw [List.range_add]
      have htail := ih (offset + sizeOfShapeHOL shape)
      simpa [sizeOfShapeHOL, sizeOfShapesHOL, Nat.add_assoc,
        Function.comp_def] using htail

private def panToCrepParamsVmapEntriesOffset :
    List (VarName × Shape) → Nat → List (MlS × (ShapeHOL × List Nat))
  | [], _ => []
  | (name, shape) :: params, offset =>
      (Flapjack.Basis.Pure.MlString.ofString name,
        (shapeToHOL shape,
          (List.range (sizeOfShapeHOL (shapeToHOL shape))).map (offset + ·))) ::
        panToCrepParamsVmapEntriesOffset params
          (offset + Shape.shapeSize shape)

/-- Production's recursive parameter allocator and the exact source
    allocator agree on the ordered update entries, including slot offsets. -/
private theorem compileParamVars_vmap_entries (params : List (VarName × Shape))
    (offset : Nat) :
    (compileParamVars params offset).1.map (fun entry =>
      (Flapjack.Basis.Pure.MlString.ofString entry.1,
        (shapeToHOL entry.2.1, entry.2.2))) =
      panToCrepParamsVmapEntriesOffset params offset := by
  induction params generalizing offset with
  | nil => simp [compileParamVars, panToCrepParamsVmapEntriesOffset]
  | cons parameter params ih =>
      cases parameter with
      | mk name shape =>
          simp [compileParamVars, panToCrepParamsVmapEntriesOffset,
            sizeOfShapeHOL_shapeToHOL, ih]

private theorem panToCrepParamsVmapEntries_exact_offset
    (params : List (VarName × Shape)) (offset : Nat) :
    panToCrepParamsVmapEntriesOffset params offset =
      let exactParams := params.map fun (name, shape) =>
        (Flapjack.Basis.Pure.MlString.ofString name, shapeToHOL shape)
      let shapes := exactParams.map Prod.snd
      (exactParams.map Prod.fst).zip
        (shapes.zip (withShapeHOL shapes
          ((List.range (sizeOfShapeHOL (.comb shapes))).map (offset + ·)))) := by
  induction params generalizing offset with
  | nil => simp [panToCrepParamsVmapEntriesOffset]
  | cons parameter params ih =>
      cases parameter with
      | mk name shape =>
          simp only [panToCrepParamsVmapEntriesOffset, List.map_cons]
          rw [withShapeHOL_range_offset]
          simp only [panToCrepShapeSlotsExact, List.zip_cons_cons]
          have htail := ih (offset + Shape.shapeSize shape)
          dsimp at htail
          rw [withShapeHOL_range_offset] at htail
          simpa [sizeOfShapeHOL_shapeToHOL] using htail

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's
    `pan_to_crep$compile_prog`
    (`cakeml/pancake/pan_to_crepScript.sml:393-397`). It compiles declarations
    to a triple list, selects inline names using `functions (FILTER inlinable
    declarations)` with the filter evaluated by exact `inlinableHOL` on the
    exact one-bit projection adapter, and applies the source-shaped triple-list `compileInlTopHOL`
    pass; the `let` structure and operand order match HOL clause-for-clause.
    The tag is WITHDRAWN as a documented carrier mismatch; see the note below. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port), source-reviewed mismatch. HOL
-- `compile_prog` (`pan_to_crepScript.sml:393-397`) is
-- `compile_inl_top (MAP FST (functions (FILTER inlinable prog)))
--    (compile_to_crep prog)` over a word-indexed `'a prog`; its result is
-- `(mlstring # num list # 'a crepLang$prog) list`, with no additional
-- hypotheses or side conditions. This definition differs on carriers, not
-- just names: (1) declarations and inline names use
-- `FunName` = `String` vs HOL `funname` = `mlstring`; (2) the source is a
-- production `Decl (BitVec width)` with production `Shape` vs HOL's
-- word-indexed `decl` carrying `mlstring`/`shape`; (3) the target is
-- production `CrepProg (BitVec width)` (whose `Call`/`ExtCall` funnames are
-- `String`) via a decode of exact `compileProgExactHOLW` bodies in the
-- parser-backed entry path vs HOL `'a crepLang$prog` via `compile_to_crep`;
-- (4) `compileInlTopHOL` is the source-shaped pass over
-- generic `CrepProg α` vs HOL `compile_inl_top`. The `[BEq FunName]
-- [LawfulBEq FunName] [LawfulHashable FunName] [OfNat (BitVec width) 0/1]`
-- arguments are executable artifacts HOL does not have. `names_as_string`
-- cannot authorize the `Decl`/`Shape`/`CrepProg` carriers and no `NameRanged`
-- witness exists (the output is a triple list, not a name). Direct HOL-EVAL
-- rows `empty`, `duplicate_first`, `nested_inline` in
-- `scripts/hol-probes/compile_prog_probe.out` are reproduced by
-- `Flapjack/Test/CompileProgParity.lean`; the `params_two_words` row is
-- reproduced by `Flapjack/Test/CompileProgParamsParity.lean`. Faithful-port
-- dependency `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`; exact
-- `compile` by `.18.3.5.8.13`, exact `compile_inl_top` by
-- `flapjack-e7w.1`; the exact-carrier inliner is a tested, non-executed
-- alternative until proved equal. The full compile_prog adapter and end-to-end
-- carrier bridge remain tracked by open epic `flapjack-e7w.2`). In
-- `compileFlapjackEntryCake` (Pipeline.lean), the parser-proved branch invokes
-- `compileProgTopHOLWithMetadataOfExact`. Its body route calls exact
-- `compileProgExactHOLW` on each function, decodes at the existing
-- source-shaped Crep boundary and inlines with `compileInlTopHOL`;
-- `compileProgTopHOLProductionExact_eq` proves equality with this generic
-- route. The `compile_prog_def` inventory remains open for the full
-- exact-carrier declaration and end-to-end bridge.
def compileProgTopHOL [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width))) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  let inlineNames :=
    (functionEntries (declarations.filter inlinableThroughHOL)).map
      fun (name, _, _, _) => name
  compileInlTopHOL inlineNames (compileToCrepHOL declarations)

/-! The parser-backed route consumes the exact, word-indexed HOL function
    projection because its input already carries the byte-range evidence needed
    by declToHOL. This Flapjack-only adapter has no HOL original: it decodes
    names and bodies only at the existing production function tuple boundary. -/

/-- Byte-ranged production declarations round-trip through the exact carrier. -/
theorem map_declOfHOL_declToHOL {width : Nat} [NeZero width]
    (declarations : List (Flapjack.Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    (declarations.map declToHOL).map declOfHOL = declarations := by
  induction declarations with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons]
      rw [declOfHOL_declToHOL d (h d (by simp)),
        ih (fun e he => h e (by simp [he]))]

/-- Function entries extracted by the tagged HOL functions definition and
    decoded to the current production interface. -/
def functionEntriesOfHOLExact {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (_h : ∀ d ∈ declarations, DeclByteRanged d) :
    List (FunName × List (VarName × Shape) × Prog (BitVec width) × Shape) :=
  (functionsHOL (declarations.map declToHOL)).map funEntryOfHOL

/-- Flapjack-only bridge theorem (no HOL original): exact functions extraction
    decoded to production entries equals `functionEntries`. The tagged
    `functionsHOL` equation applies after `declToHOL`, and the byte-range
    premise closes the reverse carrier round-trip. -/
theorem functionEntriesOfHOLExact_eq {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    functionEntriesOfHOLExact declarations h = functionEntries declarations := by
  unfold functionEntriesOfHOLExact
  rw [functionsHOL_map_funEntryOfHOL, map_declOfHOL_declToHOL declarations h]

/-- Flapjack-only bridge theorem (no HOL original): the inline-name list staged
    by production `compileProgTopHOL` -- production `String` names from
    `functionEntries` over the `inlinableThroughHOL` filter -- is the decode,
    through the reviewed `MlS`/`String` name codec `toStringOfBytes`, of the
    exact HOL-shaped staging used by `compileProgDeclsHOLW`,
    `MAP FST (functionsHOL (FILTER inlinableHOL (declarations.map declToHOL)))`.
    The byte-range premise closes the `declToHOL`/`declOfHOL` reverse carrier
    round-trip and the `inlinable` filter alignment. -/
theorem compileProgInlineNames_bridge {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ d ∈ declarations, DeclByteRanged d) :
    (functionEntries (declarations.filter inlinableThroughHOL)).map
        (fun e => e.1) =
      (functionsHOL
        ((declarations.map declToHOL).filter inlinableHOL)).map
        (fun e => Flapjack.Basis.Pure.MlString.toStringOfBytes e.1) := by
  have h1 : (functionsHOL
        ((declarations.map declToHOL).filter inlinableHOL)).map funEntryOfHOL =
      functionEntries (declarations.filter inlinableThroughHOL) := by
    rw [functionsHOL_map_funEntryOfHOL]
    rw [← inlinable_map_declOfHOL (declarations.map declToHOL)]
    rw [map_declOfHOL_declToHOL declarations hdecls]
    rw [← filter_inlinableThroughHOL]
  calc
    (functionEntries (declarations.filter inlinableThroughHOL)).map
        (fun e => e.1)
        = ((functionsHOL
            ((declarations.map declToHOL).filter inlinableHOL)).map
            funEntryOfHOL).map (fun e => e.1) := by rw [h1]
    _ = (functionsHOL
            ((declarations.map declToHOL).filter inlinableHOL)).map
            (fun e => Flapjack.Basis.Pure.MlString.toStringOfBytes e.1) := by
          rw [List.map_map]
          congr 1

/-- Executed parser-backed path: `functionsHOL` supplies the entries; each
    extracted function context is exactified with its producer evidence and its
    body is sent through the reviewed HOL-shaped `compileProgExactHOLW`, then
    decoded at the existing source-shaped Crep boundary. -/
def compileProgTopHOLProductionExact {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  let functions := functionEntriesOfHOLExact declarations hdecls
  let functionMap := functionInfosHOL declarations
  -- The exact HOL-shaped lookup rebuilds the full exception map at every
  -- lookup. Use the production map here: the equality theorem below proves
  -- this is the same function for byte-ranged declarations.
  let exceptionMap := panToCrepGetEidsFromDeclsHOL declarations
  let inlineNames :=
    (functionEntries (declarations.filter inlinableThroughHOL)).map
      fun (name, _, _, _) => name
  let compiled := functions.attach.map fun entryWithProof =>
    let entry := entryWithProof.val
    let productionContext :=
      panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
        functionMap
        (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
        exceptionMap
    have hmap : exceptionMap = panToCrepGetEidsFromDeclsHOL declarations := rfl
    have hentry : entry ∈ functionEntries declarations := by
      rw [← functionEntriesOfHOLExact_eq declarations hdecls]
      exact entryWithProof.property
    let evidence := by
      simpa [productionContext, hmap] using
        panToCrepFunctionContextProductionEvidence declarations entry
          hdecls hentry
    let exactContext := panToCrepContextExactOfProduction productionContext evidence
    let exactParams := entry.2.1.map fun (name, shape) =>
      (Flapjack.Basis.Pure.MlString.ofString name,
        Flapjack.Pancake.PanLang.shapeToHOL shape)
    (entry.1, panToCrepVars entry.2.1,
      crepProgOfHOL (compFuncExactHOLW exactContext.funcs exactContext.eids
        exactParams (progToHOL entry.2.2.1)))
  compileInlTopHOL inlineNames compiled

/-- Tested alternative, NOT executed: the parser-backed route with the inline
    stage also on exact carriers.  Each body goes through `compFuncExactHOLW` as
    in `compileProgTopHOLProductionExact`, but inlining uses the tagged
    `CrepInlineCanonical.compileInlTopHOLExact` over `MlString`/`CrepProgHOL`
    (with the `inlinableHOL` name filter) instead of the production
    `compileInlTopHOL`, decoding afterwards.  No equality with the executed
    `compileProgTopHOLProductionExact` is proved yet (PR #1174 review), so the
    compiler keeps executing the proved route; `Flapjack.Test.CompileProgParity`
    checks this alternative against the direct HOL `compile_prog` rows and
    against the executed route on the same fixtures. -/
def compileProgTopHOLProductionExactInline {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  let functions := functionEntriesOfHOLExact declarations hdecls
  let functionMap := functionInfosHOL declarations
  -- The exact HOL-shaped lookup rebuilds the full exception map at every
  -- lookup. Use the production map here: the equality theorem below proves
  -- this is the same function for byte-ranged declarations.
  let exceptionMap := panToCrepGetEidsFromDeclsHOL declarations
  let inlineNamesExact :=
    (functionsHOL ((declarations.map declToHOL).filter inlinableHOL)).map Prod.fst
  let compiledExact := functions.attach.map fun entryWithProof =>
    let entry := entryWithProof.val
    let productionContext :=
      panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
        functionMap
        (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
        exceptionMap
    have hmap : exceptionMap = panToCrepGetEidsFromDeclsHOL declarations := rfl
    have hentry : entry ∈ functionEntries declarations := by
      rw [← functionEntriesOfHOLExact_eq declarations hdecls]
      exact entryWithProof.property
    let evidence := by
      simpa [productionContext, hmap] using
        panToCrepFunctionContextProductionEvidence declarations entry
          hdecls hentry
    let exactContext := panToCrepContextExactOfProduction productionContext evidence
    let exactParams := entry.2.1.map fun (name, shape) =>
      (Flapjack.Basis.Pure.MlString.ofString name,
        Flapjack.Pancake.PanLang.shapeToHOL shape)
    (Flapjack.Basis.Pure.MlString.ofString entry.1, panToCrepVars entry.2.1,
      compFuncExactHOLW exactContext.funcs exactContext.eids exactParams
        (progToHOL entry.2.2.1))
  let inlinedExact :=
    Flapjack.CrepInlineCanonical.compileInlTopHOLExact inlineNamesExact
      compiledExact
  -- `DeclByteRanged` proves names and Crep call names round-trip through this
  -- existing production boundary; the exact inliner itself never observes a
  -- generic String or production Crep carrier.
  inlinedExact.map fun (name, params, body) =>
    (Flapjack.Basis.Pure.MlString.toStringOfBytes name, params,
      crepProgOfHOL body)

/-! Metadata adapter following the exact `compile_prog` triple boundary.
The Cake passes following `compile_prog` consume triples; the production
Flapjack pipeline keeps the source return shape in `CompiledFunction`. -/
def compileProgTopHOLWithMetadata [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width))) :
    List (CompiledFunction (BitVec width)) :=
  (compileToCrepHOLWithMetadata declarations).zipWith
    (fun original (_, _, body) => { original with body })
    (compileProgTopHOL declarations)

/-! Exact-carrier input adapter for the `compile_prog` boundary (bead
    flapjack-pxn.18.3.5.8.6). It consumes the MLString-keyed declaration
carrier `DeclHOL` and converts byte-ranged names at the boundary via
`declOfHOL`, so the exact HOL carriers are the interface type of the
declaration-level compiler boundary. This standalone adapter is retained for
callers that need the production projection. The historical parser-backed adapter
`compileProgTopHOLWithMetadataOfExact` routes every body through the
exact compiler before decoding (output equality:
`compileProgTopHOLWithMetadataOfExact_eq`). Remaining full compile_prog carrier
gaps are documented above. -/
def compileProgTopHOLOfExact {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (DeclHOL width)) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  compileProgTopHOL (declarations.map declOfHOL)

/-- Exact-versus-production bridge for the `Skip` constructor. The complete
    per-function compiler bridge is tracked by
    `flapjack-pxn.18.3.5.8.13.30.1`; this base case is definitional because
    both compiler equations return `Skip` without consulting the context. -/
theorem compileProgExactHOLW_skip_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    crepProgOfHOL (compileProgExactHOLW context .skip) =
      compileProgRiscV context.toProduction .skip := by
  simp [compileProgExactHOLW, compileProgRiscV, compileProgHOL, crepProgOfHOL]

/-- The `Seq` bridge follows from the same-context bridges of both children:
    each compiler preserves the outer `Seq` constructor and recursively
    compiles the two subprograms. -/
theorem compileProgExactHOLW_seq_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (first second : Flapjack.Pancake.PanLang.ProgHOL width)
    (hfirst : crepProgOfHOL (compileProgExactHOLW context first) =
      compileProgRiscV context.toProduction (progOfHOL first))
    (hsecond : crepProgOfHOL (compileProgExactHOLW context second) =
      compileProgRiscV context.toProduction (progOfHOL second)) :
    crepProgOfHOL (compileProgExactHOLW context (.seq first second)) =
      compileProgRiscV context.toProduction (progOfHOL (.seq first second)) := by
  simp [compileProgExactHOLW, compileProgRiscV, compileProgHOL,
    crepProgOfHOL, progOfHOL, hfirst, hsecond]

/-! Basic leaf/control clauses of the exact-to-production compiler bridge. -/
theorem compileProgExactHOLW_break_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    crepProgOfHOL (compileProgExactHOLW context (.break : ProgHOL width)) =
      compileProgRiscV context.toProduction (progOfHOL (.break : ProgHOL width)) := by
  simp [compileProgExactHOLW, compileProgRiscV, compileProgHOL, crepProgOfHOL,
    progOfHOL]

theorem compileProgExactHOLW_continue_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    crepProgOfHOL (compileProgExactHOLW context (.continue : ProgHOL width)) =
      compileProgRiscV context.toProduction (progOfHOL (.continue : ProgHOL width)) := by
  simp [compileProgExactHOLW, compileProgRiscV, compileProgHOL, crepProgOfHOL,
    progOfHOL]

theorem compileProgExactHOLW_tick_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    crepProgOfHOL (compileProgExactHOLW context (.tick : ProgHOL width)) =
      compileProgRiscV context.toProduction (progOfHOL (.tick : ProgHOL width)) := by
  simp [compileProgExactHOLW, compileProgRiscV, compileProgHOL, crepProgOfHOL,
    progOfHOL]

theorem compileProgExactHOLW_annot_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (tag text : MlS) :
    crepProgOfHOL (compileProgExactHOLW context (.annot tag text)) =
      compileProgRiscV context.toProduction (progOfHOL (.annot tag text)) := by
  simp [compileProgExactHOLW, compileProgRiscV, compileProgHOL, crepProgOfHOL,
    progOfHOL]

/-- The exact `Return` equation agrees with production once its expression
    result is decoded. The premise is the paired expression-compiler bridge;
    the shape-size check is preserved because names do not affect shape size. -/
theorem compileProgExactHOLW_return_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (expression : Exp (BitVec width))
    (hcodec :
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression) :
    crepProgOfHOL
        (compileProgExactHOLW context (.return (expToHOL expression))) =
      compileProgRiscV context.toProduction (.return expression) := by
  have hsize (shape : ShapeHOL) :
      Shape.shapeSize (shapeOfHOL shape) = sizeOfShapeHOL shape := by
    have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL shape)
    simpa only [shapeToHOL_shapeOfHOL] using h.symm
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨hexps, hshape⟩
  have hprodsize :
      Shape.shapeSize (compileExpHOL context.toProduction expression).2 =
        sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 := by
    calc
      Shape.shapeSize (compileExpHOL context.toProduction expression).2 =
          Shape.shapeSize (shapeOfHOL
            (compileExpExactHOLW context (expToHOL expression)).2) := by rw [← hshape]
      _ = sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 := hsize _
  simp only [compileProgExactHOLW, compileProgRiscV, compileProgHOL,
    compileReturnExactHOLW]
  rw [hprodsize]
  by_cases hz : sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 = 0
  · simp [hz, crepProgOfHOL]
  · simp [hz, crepProgOfHOL]
    exact hexps

/-- The exact `If` equation agrees with production once the condition
    expression and both recursive branch results are decoded. -/
theorem compileProgExactHOLW_if_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (condition : Exp (BitVec width))
    (thenBranch elseBranch : ProgHOL width)
    (hcodec :
      ((compileExpExactHOLW context (expToHOL condition)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL condition)).2) =
        compileExpHOL context.toProduction condition)
    (hthen : crepProgOfHOL (compileProgExactHOLW context thenBranch) =
      compileProgRiscV context.toProduction (progOfHOL thenBranch))
    (helse : crepProgOfHOL (compileProgExactHOLW context elseBranch) =
      compileProgRiscV context.toProduction (progOfHOL elseBranch)) :
    crepProgOfHOL (compileProgExactHOLW context
        (.ite (expToHOL condition) thenBranch elseBranch)) =
      compileProgRiscV context.toProduction
        (.ite condition (progOfHOL thenBranch) (progOfHOL elseBranch)) := by
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨hexps, _hshape⟩
  simp only [compileProgExactHOLW, compileIfExactHOLW]
  cases hExact : compileExpExactHOLW context (expToHOL condition) with
  | mk exactExpressions exactShape =>
      cases exactExpressions with
      | nil =>
          cases hProduction : compileExpHOL context.toProduction condition with
          | mk productionExpressions productionShape =>
              have hExpressions : productionExpressions = [] := by
                simpa [hExact, hProduction] using hexps.symm
              simp [compileProgRiscV, compileProgHOL, hProduction, hExpressions,
                crepProgOfHOL]
      | cons head tail =>
          cases hProduction : compileExpHOL context.toProduction condition with
          | mk productionExpressions productionShape =>
              have hExpressions : productionExpressions =
                  (crepExpOfHOL head) :: (tail.map crepExpOfHOL) := by
                simpa [hExact, hProduction] using hexps.symm
              cases productionExpressions with
              | nil => simp at hExpressions
              | cons productionHead productionTail =>
                  have hHead : productionHead = crepExpOfHOL head :=
                    (List.cons.inj hExpressions).1
                  simp [compileProgRiscV, compileProgHOL, hProduction, hHead,
                    hthen, helse, crepProgOfHOL]

/-- The exact `While` equation agrees with production once its condition
    expression and recursive body result are decoded. -/
theorem compileProgExactHOLW_while_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (condition : Exp (BitVec width))
    (body : ProgHOL width)
    (hcodec :
      ((compileExpExactHOLW context (expToHOL condition)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL condition)).2) =
        compileExpHOL context.toProduction condition)
    (hbody : crepProgOfHOL (compileProgExactHOLW context body) =
      compileProgRiscV context.toProduction (progOfHOL body)) :
    crepProgOfHOL (compileProgExactHOLW context
        (.while (expToHOL condition) body)) =
      compileProgRiscV context.toProduction
        (.while condition (progOfHOL body)) := by
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨hexps, _hshape⟩
  simp only [compileProgExactHOLW, compileWhileExactHOLW]
  cases hExact : compileExpExactHOLW context (expToHOL condition) with
  | mk exactExpressions exactShape =>
      cases exactExpressions with
      | nil =>
          cases hProduction : compileExpHOL context.toProduction condition with
          | mk productionExpressions productionShape =>
              have hExpressions : productionExpressions = [] := by
                simpa [hExact, hProduction] using hexps.symm
              simp [compileProgRiscV, compileProgHOL, hProduction, hExpressions,
                crepProgOfHOL]
      | cons head tail =>
          cases hProduction : compileExpHOL context.toProduction condition with
          | mk productionExpressions productionShape =>
              have hExpressions : productionExpressions =
                  (crepExpOfHOL head) :: (tail.map crepExpOfHOL) := by
                simpa [hExact, hProduction] using hexps.symm
              cases productionExpressions with
              | nil => simp at hExpressions
              | cons productionHead productionTail =>
                  have hHead : productionHead = crepExpOfHOL head :=
                    (List.cons.inj hExpressions).1
                  simp [compileProgRiscV, compileProgHOL, hProduction, hHead,
                    hbody, crepProgOfHOL]

/-- HOL's Global Assign equation compiles to `Skip` in both carriers. -/
theorem compileProgExactHOLW_global_assign_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : MlS)
    (expression : Flapjack.Pancake.PanLang.ExpHOL width) :
    crepProgOfHOL
        (compileProgExactHOLW context (.assign .global name expression)) =
      compileProgRiscV context.toProduction
        (progOfHOL (.assign .global name expression)) := by
  simp [compileProgExactHOLW, compileGlobalAssignExactHOLW,
    compileProgRiscV, compileProgHOL, crepProgOfHOL, progOfHOL]

/-- HOL's Global ShMemLoad equation compiles to `Skip` in both carriers. -/
theorem compileProgExactHOLW_global_shmem_load_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (operator : OpSize) (name : MlS)
    (address : Flapjack.Pancake.PanLang.ExpHOL width) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.shMemLoad operator .global name address)) =
      compileProgRiscV context.toProduction
        (progOfHOL (.shMemLoad operator .global name address)) := by
  simp [compileProgExactHOLW, compileGlobalShMemLoadExactHOLW,
    compileProgRiscV, compileProgHOL, crepProgOfHOL, progOfHOL]

/-- The exact Store32 equation agrees with production once both expression
    compiler results are decoded. -/
theorem compileProgExactHOLW_store32_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (address value : Exp (BitVec width))
    (haddress :
      ((compileExpExactHOLW context (expToHOL address)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL address)).2) =
        compileExpHOL context.toProduction address)
    (hvalue :
      ((compileExpExactHOLW context (expToHOL value)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL value)).2) =
        compileExpHOL context.toProduction value) :
    crepProgOfHOL (compileProgExactHOLW context
        (.store32 (expToHOL address) (expToHOL value))) =
      compileProgRiscV context.toProduction
        (.store32 address value) := by
  rw [Prod.mk.injEq] at haddress hvalue
  rcases haddress with ⟨haddressList, _⟩
  rcases hvalue with ⟨hvalueList, _⟩
  cases hExactAddress : compileExpExactHOLW context (expToHOL address) with
  | mk exactAddresses addressShape =>
      cases hExactValue : compileExpExactHOLW context (expToHOL value) with
      | mk exactValues valueShape =>
          cases hProductionAddress : compileExpHOL context.toProduction address with
          | mk productionAddresses productionAddressShape =>
              cases hProductionValue : compileExpHOL context.toProduction value with
              | mk productionValues productionValueShape =>
                  cases exactAddresses <;> cases exactValues <;>
                    cases productionAddresses <;> cases productionValues <;>
                    simp_all [compileProgExactHOLW, compileStore32ExactHOLW,
                      compileProgRiscV, compileProgHOL, crepProgOfHOL]

/-- The exact StoreByte equation agrees with production once both expression
    compiler results are decoded. -/
theorem compileProgExactHOLW_store_byte_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (address value : Exp (BitVec width))
    (haddress :
      ((compileExpExactHOLW context (expToHOL address)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL address)).2) =
        compileExpHOL context.toProduction address)
    (hvalue :
      ((compileExpExactHOLW context (expToHOL value)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL value)).2) =
        compileExpHOL context.toProduction value) :
    crepProgOfHOL (compileProgExactHOLW context
        (.storeByte (expToHOL address) (expToHOL value))) =
      compileProgRiscV context.toProduction
        (.storeByte address value) := by
  rw [Prod.mk.injEq] at haddress hvalue
  rcases haddress with ⟨haddressList, _⟩
  rcases hvalue with ⟨hvalueList, _⟩
  cases hExactAddress : compileExpExactHOLW context (expToHOL address) with
  | mk exactAddresses addressShape =>
      cases hExactValue : compileExpExactHOLW context (expToHOL value) with
      | mk exactValues valueShape =>
          cases hProductionAddress : compileExpHOL context.toProduction address with
          | mk productionAddresses productionAddressShape =>
              cases hProductionValue : compileExpHOL context.toProduction value with
              | mk productionValues productionValueShape =>
                  cases exactAddresses <;> cases exactValues <;>
                    cases productionAddresses <;> cases productionValues <;>
                    simp_all [compileProgExactHOLW, compileStoreByteExactHOLW,
                      compileProgRiscV, compileProgHOL, crepProgOfHOL]

private theorem crepProgOfHOL_nestedDecsHOL {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width))
    (body : CrepProgHOL width) :
    crepProgOfHOL (nestedDecsHOL names values body) =
      nestedDecs names (values.map crepExpOfHOL) (crepProgOfHOL body) := by
  induction names generalizing values body with
  | nil => cases values <;> simp [nestedDecsHOL, nestedDecs, crepProgOfHOL]
  | cons name names ih =>
      cases values <;> simp [nestedDecsHOL, nestedDecs, crepProgOfHOL, ih]

private theorem crepProgOfHOL_storesHOL {width : Nat} [NeZero width]
    (address : CrepExpHOL width) (values : List (CrepExpHOL width))
    (offset : BitVec width) :
    (storesHOL address values offset).map crepProgOfHOL =
      stores (crepExpOfHOL address) (values.map crepExpOfHOL) offset
        (BitVec.ofNat width (width / 8)) := by
  induction values generalizing offset with
  | nil => simp [storesHOL, stores]
  | cons value values ih =>
      simp only [storesHOL, List.map_cons, crepProgOfHOL, stores]
      split <;> simp [crepExpOfHOL, ih]

private theorem crepProgOfHOL_zipWith_assign {width : Nat} [NeZero width]
    (names : List Nat) (expressions : List (CrepExpHOL width)) :
    List.map crepProgOfHOL
        (List.zipWith (fun name expression => CrepProgHOL.assign name expression)
          names expressions) =
      List.zipWith (fun name expression => CrepProg.assign name (crepExpOfHOL expression))
        names expressions := by
  rw [List.map_zipWith]
  simp only [crepProgOfHOL]

private theorem crepExpVarsW_flatMap_crepExpOfHOL {width : Nat} [NeZero width]
    (expressions : List (CrepExpHOL width)) :
    expressions.flatMap (fun expression => crepExpVarsW (crepExpOfHOL expression)) =
      (expressions.map crepExpOfHOL).flatMap crepExpVars := by
  simp only [crepExpVarsW]
  rw [List.flatMap_map]

/-- Exact successful-clause bridge for HOL's `Store` equation. It is stated
    over the expression-compiler outputs so the caller supplies the paired
    expression codecs and the successful shape/length condition. This isolates
    the Store-specific proof: exact and production reserve the same address
    slot, allocate `vmax + 2 + i` for each value, and use the same fixed
    `bytes_in_word` stride after decoding. The two `Skip` cases are handled by
    the empty-address and shape/list-length bridge theorems below. -/
theorem compileProgExactHOLW_store_success_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (address value : Exp (BitVec width))
    (exactAddress : CrepExpHOL width) (exactAddressRest : List (CrepExpHOL width))
    (exactAddressShape : ShapeHOL) (exactValues : List (CrepExpHOL width))
    (exactValueShape : ShapeHOL)
    (productionAddress : CrepExp (BitVec width))
    (productionAddressRest : List (CrepExp (BitVec width)))
    (productionAddressShape : Shape)
    (productionValues : List (CrepExp (BitVec width))) (productionValueShape : Shape)
    (hexactAddress : compileExpExactHOLW context (expToHOL address) =
      (exactAddress :: exactAddressRest, exactAddressShape))
    (hexactValue : compileExpExactHOLW context (expToHOL value) =
      (exactValues, exactValueShape))
    (hproductionAddress : compileExpHOL context.toProduction address =
      (productionAddress :: productionAddressRest, productionAddressShape))
    (hproductionValue : compileExpHOL context.toProduction value =
      (productionValues, productionValueShape))
    (haddressCodec : crepExpOfHOL exactAddress = productionAddress)
    (hvaluesCodec : exactValues.map crepExpOfHOL = productionValues)
    (hshapeCodec : shapeOfHOL exactValueShape = productionValueShape)
    (hsuccess : sizeOfShapeHOL exactValueShape = exactValues.length) :
    crepProgOfHOL (compileProgExactHOLW context
        (.store (expToHOL address) (expToHOL value))) =
      compileProgRiscV context.toProduction (.store address value) := by
  have hsize (shape : ShapeHOL) :
      Shape.shapeSize (shapeOfHOL shape) = sizeOfShapeHOL shape := by
    have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL shape)
    simpa only [shapeToHOL_shapeOfHOL] using h.symm
  have hsuccessProduction : productionValues.length = Shape.shapeSize productionValueShape := by
    calc
      productionValues.length = exactValues.length := by
        simpa using congrArg List.length hvaluesCodec.symm
      _ = sizeOfShapeHOL exactValueShape := hsuccess.symm
      _ = Shape.shapeSize (shapeOfHOL exactValueShape) := (hsize _).symm
      _ = Shape.shapeSize productionValueShape := congrArg Shape.shapeSize hshapeCodec
  have hcount : exactValues.length = Shape.shapeSize productionValueShape := by
    calc
      exactValues.length = productionValues.length := by
        simpa using congrArg List.length hvaluesCodec
      _ = Shape.shapeSize productionValueShape := hsuccessProduction
  have hnamesProduction :
      (List.range exactValues.length).map (fun index => context.vmax + 1 + index + 1) =
        freshNamesHOL context.toProduction productionValueShape.shapeSize 2 := by
    simp only [freshNamesHOL, PanToCrepContextExact.toProduction]
    rw [← hcount]
    congr 1
    funext index
    omega
  simp only [compileProgExactHOLW, compileStoreExactHOLW, hexactAddress,
    hexactValue, compileProgRiscV, compileProgHOL, hproductionAddress,
    hproductionValue, hsuccess, hsuccessProduction]
  have hExactGuard : ¬ ((exactValues.length != exactValues.length) = true) := by
    simp
  simp only [if_neg hExactGuard, if_true]
  rw [crepProgOfHOL_nestedDecsHOL, crepProgOfHOL_crepNestedSeqHOL,
    crepProgOfHOL_storesHOL]
  simp [haddressCodec, hvaluesCodec, hnamesProduction,
    PanToCrepContextExact.toProduction, CrepBytesInWord.bytesInWord]
  have hvar :
      crepExpOfHOL ∘ (CrepExpHOL.var : Nat → CrepExpHOL width) =
        (CrepExp.var : Nat → CrepExp (BitVec width)) := by
    funext name
    simp [crepExpOfHOL]
  rw [hvar]
  simp [crepExpOfHOL]

/-- Exact-to-production bridge for HOL's `Store` address-head fallback. The
    HOL `compile_def` equation returns `Skip` when `compile_exp ctxt ad` has
    no head (pan_to_crepScript.sml:174-184); the exact and production
    compilers therefore agree without inspecting the value expression. -/
theorem compileProgExactHOLW_store_empty_address_bridge {width : Nat}
    [NeZero width]
    (context : PanToCrepContextExact width)
    (address value : Exp (BitVec width))
    (exactAddressShape : ShapeHOL) (productionAddressShape : Shape)
    (hexactAddress : compileExpExactHOLW context (expToHOL address) =
      ([], exactAddressShape))
    (hproductionAddress : compileExpHOL context.toProduction address =
      ([], productionAddressShape)) :
    crepProgOfHOL (compileProgExactHOLW context
        (.store (expToHOL address) (expToHOL value))) =
      compileProgRiscV context.toProduction (.store address value) := by
  simp only [compileProgExactHOLW, compileStoreExactHOLW, hexactAddress,
    compileProgRiscV, compileProgHOL, hproductionAddress]
  simp [crepProgOfHOL]

/-- Exact-to-production bridge for the HOL `Store` shape/list-length
    fallback. The caller supplies the paired expression codecs and shape
    codec; these imply that the production guard also fails whenever the HOL
    `size_of_shape sh = LENGTH es` guard fails. The HOL equation returns
    `Skip` in both cases (pan_to_crepScript.sml:174-184). -/
theorem compileProgExactHOLW_store_length_mismatch_bridge {width : Nat}
    [NeZero width]
    (context : PanToCrepContextExact width)
    (address value : Exp (BitVec width))
    (exactAddress : CrepExpHOL width) (exactAddressRest : List (CrepExpHOL width))
    (exactAddressShape : ShapeHOL)
    (exactValues : List (CrepExpHOL width)) (exactValueShape : ShapeHOL)
    (productionAddress : CrepExp (BitVec width))
    (productionAddressRest : List (CrepExp (BitVec width)))
    (productionAddressShape : Shape)
    (productionValues : List (CrepExp (BitVec width)))
    (productionValueShape : Shape)
    (hexactAddress : compileExpExactHOLW context (expToHOL address) =
      (exactAddress :: exactAddressRest, exactAddressShape))
    (hexactValue : compileExpExactHOLW context (expToHOL value) =
      (exactValues, exactValueShape))
    (hproductionAddress : compileExpHOL context.toProduction address =
      (productionAddress :: productionAddressRest, productionAddressShape))
    (hproductionValue : compileExpHOL context.toProduction value =
      (productionValues, productionValueShape))
    (hvaluesCodec : exactValues.map crepExpOfHOL = productionValues)
    (hshapeCodec : shapeOfHOL exactValueShape = productionValueShape)
    (hmismatch : sizeOfShapeHOL exactValueShape ≠ exactValues.length) :
    crepProgOfHOL (compileProgExactHOLW context
        (.store (expToHOL address) (expToHOL value))) =
      compileProgRiscV context.toProduction (.store address value) := by
  have hsize (shape : ShapeHOL) :
      Shape.shapeSize (shapeOfHOL shape) = sizeOfShapeHOL shape := by
    have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL shape)
    simpa only [shapeToHOL_shapeOfHOL] using h.symm
  have hlength : exactValues.length = productionValues.length := by
    have h := congrArg List.length hvaluesCodec
    simpa using h
  have hshapeSize :
      sizeOfShapeHOL exactValueShape = Shape.shapeSize productionValueShape := by
    calc
      sizeOfShapeHOL exactValueShape =
          Shape.shapeSize (shapeOfHOL exactValueShape) := (hsize _).symm
      _ = Shape.shapeSize productionValueShape :=
        congrArg Shape.shapeSize hshapeCodec
  have hproductionMismatch :
      Shape.shapeSize productionValueShape ≠ productionValues.length := by
    intro hproductionSuccess
    apply hmismatch
    calc
      sizeOfShapeHOL exactValueShape = Shape.shapeSize productionValueShape :=
        hshapeSize
      _ = productionValues.length := hproductionSuccess
      _ = exactValues.length := hlength.symm
  simp only [compileProgExactHOLW, compileStoreExactHOLW, hexactAddress,
    hexactValue, compileProgRiscV, compileProgHOL, hproductionAddress,
    hproductionValue]
  simp [crepProgOfHOL, hmismatch, Ne.symm hproductionMismatch]

/-- The complete `Store` compiler clause follows from the paired expression
    outputs and codecs alone. Split on the address-head and value-length
    guards; in the successful branch, the value codec plus shape codec forces
    the production length test to have the same result as HOL's. This is
    Flapjack bridge infrastructure, not a separately tagged HOL declaration. -/
theorem compileProgExactHOLW_store_output_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (address value : Exp (BitVec width))
    (exactAddresses : List (CrepExpHOL width)) (exactAddressShape : ShapeHOL)
    (exactValues : List (CrepExpHOL width)) (exactValueShape : ShapeHOL)
    (productionAddresses : List (CrepExp (BitVec width)))
    (productionAddressShape : Shape)
    (productionValues : List (CrepExp (BitVec width)))
    (productionValueShape : Shape)
    (hexactAddress : compileExpExactHOLW context (expToHOL address) =
      (exactAddresses, exactAddressShape))
    (hexactValue : compileExpExactHOLW context (expToHOL value) =
      (exactValues, exactValueShape))
    (hproductionAddress : compileExpHOL context.toProduction address =
      (productionAddresses, productionAddressShape))
    (hproductionValue : compileExpHOL context.toProduction value =
      (productionValues, productionValueShape))
    (haddressCodec : exactAddresses.map crepExpOfHOL = productionAddresses)
    (hvaluesCodec : exactValues.map crepExpOfHOL = productionValues)
    (hshapeCodec : shapeOfHOL exactValueShape = productionValueShape) :
    crepProgOfHOL (compileProgExactHOLW context
        (.store (expToHOL address) (expToHOL value))) =
      compileProgRiscV context.toProduction (.store address value) := by
  cases exactAddresses with
  | nil =>
      simp only [List.map_nil] at haddressCodec
      cases productionAddresses with
      | nil =>
          simp only [compileProgExactHOLW, compileStoreExactHOLW,
            hexactAddress, compileProgRiscV, compileProgHOL,
            hproductionAddress]
          simp [crepProgOfHOL]
      | cons productionAddress productionAddressRest =>
          simp at haddressCodec
  | cons exactAddress exactAddressRest =>
      cases productionAddresses with
      | nil =>
          simp only [List.map_cons] at haddressCodec
          cases haddressCodec
      | cons productionAddress productionAddressRest =>
          have haddressHead : crepExpOfHOL exactAddress = productionAddress := by
            have h := congrArg List.head? haddressCodec
            simpa using h
          by_cases hsuccess : sizeOfShapeHOL exactValueShape = exactValues.length
          · exact compileProgExactHOLW_store_success_bridge context address value
              exactAddress exactAddressRest exactAddressShape exactValues
              exactValueShape productionAddress productionAddressRest
              productionAddressShape productionValues productionValueShape
              hexactAddress hexactValue hproductionAddress hproductionValue
              haddressHead hvaluesCodec hshapeCodec hsuccess
          · exact compileProgExactHOLW_store_length_mismatch_bridge context
              address value exactAddress exactAddressRest exactAddressShape
              exactValues exactValueShape productionAddress
              productionAddressRest productionAddressShape productionValues
              productionValueShape hexactAddress hexactValue hproductionAddress
              hproductionValue hvaluesCodec hshapeCodec hsuccess

/-- The exact `Raise` clause agrees with production whenever its compiled
    expression is paired by the expression codec. This preserves both
    source-level fallbacks (missing exception id and expression shape/list
    length mismatch) as well as the successful sequence of local declarations,
    global saves, and final raise. The temporary names agree because both
    clauses allocate the compiled value count starting at `vmax + 1`. -/
theorem compileProgExactHOLW_raise_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (exceptionName : String)
    (expression : Exp (BitVec width))
    (hcodec :
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.raise (Flapjack.Basis.Pure.MlString.ofString exceptionName)
            (expToHOL expression))) =
      compileProgRiscV context.toProduction (.raise exceptionName expression) := by
  have hsize (shape : ShapeHOL) :
      Shape.shapeSize (shapeOfHOL shape) = sizeOfShapeHOL shape := by
    have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL shape)
    simpa only [shapeToHOL_shapeOfHOL] using h.symm
  cases hExact : compileExpExactHOLW context (expToHOL expression) with
  | mk exactValues exactShape =>
      cases hProduction : compileExpHOL context.toProduction expression with
      | mk productionValues productionShape =>
          have hcodec' := hcodec
          rw [hExact, hProduction] at hcodec'
          simp only [Prod.mk.injEq] at hcodec'
          rcases hcodec' with ⟨hvalues, hshape⟩
          have hlength : exactValues.length = productionValues.length := by
            have h := congrArg List.length hvalues
            simpa using h
          cases hEid : context.eids.lookup
              (Flapjack.Basis.Pure.MlString.ofString exceptionName) with
          | none =>
              have hProductionEid :
                  context.toProduction.eids exceptionName = none := by
                simpa [PanToCrepContextExact.toProduction,
                  Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes] using hEid
              simp [compileProgExactHOLW, compileRaiseExactHOLW,
                compileProgRiscV, compileProgHOL, FLOOKUP, hProductionEid, hEid,
                crepProgOfHOL]
          | some exceptionCode =>
              have hProductionEid :
                  context.toProduction.eids exceptionName = some exceptionCode := by
                simpa [PanToCrepContextExact.toProduction,
                  Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes] using hEid
              have hshapeCount : sizeOfShapeHOL exactShape =
                  Shape.shapeSize productionShape := by
                calc
                  sizeOfShapeHOL exactShape = Shape.shapeSize (shapeOfHOL exactShape) :=
                    (hsize exactShape).symm
                  _ = Shape.shapeSize productionShape := by rw [hshape]
              have htemporaries :
                  (List.range (sizeOfShapeHOL exactShape)).map
                    (fun index => context.vmax + index + 1) =
                    freshNamesHOL context.toProduction
                      (Shape.shapeSize productionShape) 1 := by
                unfold freshNamesHOL
                change (List.range (sizeOfShapeHOL exactShape)).map
                    (fun index => context.vmax + index + 1) =
                  (List.range (Shape.shapeSize productionShape)).map
                    (fun offset => context.vmax + 1 + offset)
                rw [hshapeCount]
                apply List.map_congr_left
                intro index hin
                omega
              by_cases hcount : sizeOfShapeHOL exactShape = exactValues.length
              · have hproductionCount : productionValues.length =
                    Shape.shapeSize productionShape := by
                  calc
                    productionValues.length = exactValues.length := hlength.symm
                    _ = sizeOfShapeHOL exactShape := hcount.symm
                    _ = Shape.shapeSize (shapeOfHOL exactShape) := (hsize exactShape).symm
                    _ = Shape.shapeSize productionShape := by rw [hshape]
                have hnames :
                    (List.range exactValues.length).map
                      (fun index => context.vmax + index + 1) =
                      freshNamesHOL context.toProduction
                        (Shape.shapeSize productionShape) 1 := by
                  rw [← hcount]
                  exact htemporaries
                have hstores :
                    ∀ address : BitVec 5,
                    ((storeGlobalsHOL (width := width) address
                      ((freshNamesHOL context.toProduction
                        (Shape.shapeSize productionShape) 1).map
                          (CrepExpHOL.var (width := width)))).map
                        (crepProgOfHOL (width := width))) =
                  storeGlobals address
                    ((freshNamesHOL context.toProduction
                      (Shape.shapeSize productionShape) 1).map
                        (CrepExp.var (α := BitVec width))) := by
                  intro address
                  induction freshNamesHOL context.toProduction
                      (Shape.shapeSize productionShape) 1 generalizing address with
                  | nil => simp [storeGlobalsHOL, storeGlobals]
                  | cons name names ih =>
                      simp [storeGlobalsHOL, storeGlobals, crepProgOfHOL,
                        crepExpOfHOL, ih]
                simp [compileProgExactHOLW, compileRaiseExactHOLW,
                  compileProgRiscV, compileProgHOL, FLOOKUP, hProductionEid,
                  hEid, hExact, hProduction, hcount, hproductionCount,
                  hnames, hvalues, crepProgOfHOL,
                  crepProgOfHOL_nestedDecsHOL, crepProgOfHOL_crepNestedSeqHOL]
                apply congrArg (fun body =>
                  nestedDecs (freshNamesHOL context.toProduction
                    (Shape.shapeSize productionShape) 1) productionValues body)
                apply congrArg crepNestedSeq
                exact hstores (0 : BitVec 5)
              · have hproductionMismatch : productionValues.length ≠
                    Shape.shapeSize productionShape := by
                  intro hproductionCount
                  apply hcount
                  calc
                    sizeOfShapeHOL exactShape = Shape.shapeSize (shapeOfHOL exactShape) :=
                      (hsize exactShape).symm
                    _ = Shape.shapeSize productionShape := by rw [hshape]
                    _ = productionValues.length := hproductionCount.symm
                    _ = exactValues.length := hlength.symm
                simp [compileProgExactHOLW, compileRaiseExactHOLW,
                  compileProgRiscV, compileProgHOL, FLOOKUP, hProductionEid, hEid,
                  hExact, hProduction, hcount, hproductionMismatch, crepProgOfHOL]

/-- Source-reviewed bridge for HOL `compile_def`'s local `Assign` clause
    (`cakeml/pancake/pan_to_crepScript.sml:142-158`).  The four source branches
    are preserved: a variable missing from `ctxt.vars` and a compiled
    shape/list length mismatch both compile to `Skip`; disjoint assigned
    variable names compile to `nested_seq (MAP2 Assign ns es)`; interfering
    names first declare fresh temporaries (`ctxt.vmax + 1 ...`) and assign the
    destination variables from those temporaries.  The exact clause
    `compileLocalAssignExactHOLW` allocates the same temporaries as the
    production `freshNamesHOL` names. -/
theorem compileProgExactHOLW_local_assign_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : String)
    (expression : Exp (BitVec width))
    (hcodec :
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.assign .local (Flapjack.Basis.Pure.MlString.ofString name)
            (expToHOL expression))) =
      compileProgRiscV context.toProduction (.assign .local name expression) := by
  cases hExact : compileExpExactHOLW context (expToHOL expression) with
  | mk exactValues exactShape =>
      cases hProduction : compileExpHOL context.toProduction expression with
      | mk productionValues productionShape =>
          have hcodec' := hcodec
          rw [hExact, hProduction] at hcodec'
          simp only [Prod.mk.injEq] at hcodec'
          rcases hcodec' with ⟨hvalues, _hshape⟩
          have hlength : exactValues.length = productionValues.length := by
            have h := congrArg List.length hvalues
            simpa using h
          have hvariables :
              context.toProduction.vars name =
                (context.vars.lookup
                  (Flapjack.Basis.Pure.MlString.ofString name)).map
                  (fun entry => (shapeOfHOL entry.1, entry.2)) := rfl
          cases hlookup : context.vars.lookup
              (Flapjack.Basis.Pure.MlString.ofString name) with
          | none =>
              simp [compileProgExactHOLW, compileLocalAssignExactHOLW,
                compileProgRiscV, compileProgHOL, FLOOKUP, hvariables, hlookup,
                crepProgOfHOL]
          | some entry =>
              obtain ⟨entryShape, names⟩ := entry
              have hProductionVar :
                  FLOOKUP context.toProduction.vars name =
                    some (shapeOfHOL entryShape, names) := by
                unfold FLOOKUP
                rw [hvariables, hlookup]
                rfl
              have hdisjEq :
                  distinctListsHol names
                      (exactValues.flatMap fun compiled =>
                        crepExpVarsW (crepExpOfHOL compiled)) =
                    distinctLists names
                      (productionValues.flatMap crepExpVars) := by
                rw [crepExpVarsW_flatMap_crepExpOfHOL, ← hvalues]
                rw [distinctLists, distinctListsBEq_eq_distinctListsHol]
              have hassign :
                  (names.zipWith
                      (fun name expression => CrepProg.assign name expression)
                      productionValues) =
                    List.zipWith
                      (fun name expression =>
                        CrepProg.assign name (crepExpOfHOL expression))
                      names exactValues := by
                rw [← hvalues]
                rw [List.zipWith_map_right]
              have htemporaries :
                  (List.range names.length).map
                    (fun index => context.vmax + index + 1) =
                    freshNamesHOL context.toProduction names.length 1 := by
                unfold freshNamesHOL
                change (List.range names.length).map
                    (fun index => context.vmax + index + 1) =
                  (List.range names.length).map
                    (fun offset => context.vmax + 1 + offset)
                apply List.map_congr_left
                intro index _hin
                omega
              by_cases hlen : names.length = exactValues.length
              · have hproductionLen :
                    names.length = productionValues.length := by
                  rw [hlen, hlength]
                by_cases hdisj : distinctLists names
                    (productionValues.flatMap crepExpVars) = true
                · have hdisjHol : distinctListsHol names
                      (exactValues.flatMap fun compiled =>
                        crepExpVarsW (crepExpOfHOL compiled)) = true := by
                    rw [hdisjEq]
                    exact hdisj
                  simp only [compileProgExactHOLW, compileLocalAssignExactHOLW,
                    compileProgRiscV, compileProgHOL, hProductionVar,
                    hExact, hProduction]
                  rw [hlookup]
                  dsimp only
                  rw [if_pos hproductionLen, if_pos hdisj,
                    if_neg (by simp [hlen]), if_pos hdisjHol]
                  simp only [crepProgOfHOL_crepNestedSeqHOL,
                    crepProgOfHOL_zipWith_assign]
                  exact congrArg crepNestedSeq hassign.symm
                · have hdisjHol : distinctListsHol names
                      (exactValues.flatMap fun compiled =>
                        crepExpVarsW (crepExpOfHOL compiled)) ≠ true := by
                    rw [hdisjEq]
                    exact hdisj
                  have hassignments :
                      List.zipWith
                          (fun name expression =>
                            CrepProg.assign name (crepExpOfHOL expression))
                          names
                          (List.map (CrepExpHOL.var (width := width))
                            (freshNamesHOL context.toProduction names.length 1)) =
                        List.zipWith
                          (fun name temporary =>
                            CrepProg.assign name (CrepExp.var temporary))
                          names
                          (freshNamesHOL context.toProduction names.length 1) := by
                    rw [List.zipWith_map_right]
                    simp only [crepExpOfHOL]
                  simp only [compileProgExactHOLW, compileLocalAssignExactHOLW,
                    compileProgRiscV, compileProgHOL, hProductionVar,
                    hExact, hProduction]
                  rw [hlookup]
                  dsimp only
                  rw [if_pos hproductionLen, if_neg hdisj,
                    if_neg (by simp [hlen]), if_neg hdisjHol]
                  rw [crepProgOfHOL_nestedDecsHOL,
                    crepProgOfHOL_crepNestedSeqHOL,
                    crepProgOfHOL_zipWith_assign, hvalues]
                  rw [htemporaries, hassignments]
              · have hproductionLen :
                    names.length ≠ productionValues.length := by
                  intro hcontra
                  apply hlen
                  rw [hcontra, hlength]
                simp only [compileProgExactHOLW, compileLocalAssignExactHOLW,
                  compileProgRiscV, compileProgHOL, hProductionVar,
                  hExact, hProduction]
                rw [hlookup]
                dsimp only
                rw [if_neg hproductionLen, if_pos (by simp [hlen])]
                simp only [crepProgOfHOL]

/-- Source-reviewed HOL `ShMemStore` clause bridge (`pan_to_crepScript.sml`,
    `compile_def`): its operands are positional `value` then `address`. The
    production `Prog.shMemStore` names its two fields `address` and `value`,
    but the compiler clause consumes those positions in HOL order: the first
    operand is the stored expression and the second is the destination address.
    The exact clause allocates from `FOLDR MAX 0 (var_cexp value)`; the
    production clause's singleton `maxCrepExpVarHOL` is the same maximum. -/
private theorem foldr_max_zero_eq_max_getD (xs : List Nat) :
    xs.foldr max 0 = xs.max?.getD 0 := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldr_cons, List.max?_cons']
      rw [List.foldl_max]
      rw [ih]
      cases hmax : tail.max? <;> simp <;> omega

/-- Flapjack-specific helper: the codec image of the exact compiled argument
    list equals the production `compileArgsHOL` when the paired `compile_exp`
    codec holds for every argument. HOL has no separate list lemma here; the
    source `Primitive` clause is `pan_to_crepScript.sml:164-175`. -/
private theorem crepProgOfHOL_compileArgumentList_flatMap {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (arguments : List (Exp (BitVec width)))
    (hcodec : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression) :
    ((compileExpExactHOLWList context (arguments.map expToHOL)).flatMap Prod.fst).map crepExpOfHOL =
      compileArgsHOL context.toProduction arguments := by
  induction arguments with
  | nil => simp [compileExpExactHOLWList, compileArgsHOL]
  | cons expression rest ih =>
      have hexp :
          (compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL =
            (compileExpHOL context.toProduction expression).1 := by
        have h := congrArg Prod.fst (hcodec expression (by simp))
        simpa using h
      simp only [List.map_cons, compileExpExactHOLWList, compileArgsHOL, List.flatMap_cons,
        List.map_append]
      rw [hexp]
      rw [ih (fun e he => hcodec e (by simp [he]))]

/-- The same argument-list codec when the production context is related to,
    but not definitionally `context.toProduction`. This is needed after a
    nested ranged variable update, where off-range map keys are intentionally
    not equated. -/
private theorem crepProgOfHOL_compileArgumentList_flatMapAt {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (arguments : List (Exp (BitVec width)))
    (hcodec : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL productionContext expression) :
    ((compileExpExactHOLWList context (arguments.map expToHOL)).flatMap Prod.fst).map crepExpOfHOL =
      compileArgsHOL productionContext arguments := by
  induction arguments with
  | nil => simp [compileExpExactHOLWList, compileArgsHOL]
  | cons expression rest ih =>
      have hexp :
          (compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL =
            (compileExpHOL productionContext expression).1 := by
        have h := congrArg Prod.fst (hcodec expression (by simp))
        simpa using h
      simp only [List.map_cons, compileExpExactHOLWList, compileArgsHOL, List.flatMap_cons,
        List.map_append]
      rw [hexp]
      rw [ih (fun e he => hcodec e (by simp [he]))]

/-- Exact-to-production bridge for HOL `compile_def`'s `Primitive` clause
    (`pan_to_crepScript.sml:164-175`). The exact clause compiles the whole
    argument list internally, so the bridge takes a per-argument list codec
    premise. Covers the missing-variable fallback and the temporaries branch. -/
theorem compileProgExactHOLW_primitive_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : String) (operator : PrimOp)
    (arguments : List (Exp (BitVec width)))
    (hcodec : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression) :
    crepProgOfHOL (compileProgExactHOLW context
        (.primitive (Flapjack.Basis.Pure.MlString.ofString name) operator
          (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction (.primitive name operator arguments) := by
  have hvariables : context.toProduction.vars name =
      (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString name)).map
        (fun entry => (shapeOfHOL entry.1, entry.2)) := rfl
  cases hlookup : context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString name) with
  | none =>
      simp [compileProgExactHOLW, compilePrimitiveExactHOLW, compileProgRiscV,
        compileProgHOL, FLOOKUP, hvariables, hlookup, crepProgOfHOL]
  | some entry =>
      obtain ⟨entryShape, names⟩ := entry
      have hProductionVar : FLOOKUP context.toProduction.vars name =
          some (shapeOfHOL entryShape, names) := by
        unfold FLOOKUP
        rw [hvariables, hlookup]
        rfl
      have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
      have hlen :
          ((compileExpExactHOLWList context (arguments.map expToHOL)).flatMap Prod.fst).length =
            (compileArgsHOL context.toProduction arguments).length := by
        rw [← hargs]
        simp
      have htemporaries :
          (List.range
              ((compileExpExactHOLWList context (arguments.map expToHOL)).flatMap Prod.fst).length).map
            (fun index => context.vmax + index + 1) =
          freshNamesHOL context.toProduction
            (compileArgsHOL context.toProduction arguments).length 1 := by
        unfold freshNamesHOL
        rw [hlen]
        change
          (List.range (compileArgsHOL context.toProduction arguments).length).map
              (fun index => context.vmax + index + 1) =
            (List.range (compileArgsHOL context.toProduction arguments).length).map
              (fun offset => context.vmax + 1 + offset)
        apply List.map_congr_left
        intro index _hin
        omega
      simp only [compileProgExactHOLW, compilePrimitiveExactHOLW, compileProgRiscV,
        compileProgHOL, hProductionVar]
      rw [hlookup]
      dsimp only
      rw [crepProgOfHOL_nestedDecsHOL]
      simp only [crepProgOfHOL]
      rw [hargs]
      rw [htemporaries]

private theorem ofString_injective_on_ranged_names {left right : String}
    (hleft : Flapjack.Pancake.PanLang.NameRanged left)
    (hright : Flapjack.Pancake.PanLang.NameRanged right)
    (h : Flapjack.Basis.Pure.MlString.ofString left =
      Flapjack.Basis.Pure.MlString.ofString right) : left = right := by
  have hdecoded := congrArg Flapjack.Basis.Pure.MlString.toStringOfBytes h
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes left hleft,
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes right hright]
    at hdecoded
  exact hdecoded

private theorem fupdateList_ofString_bridge {β γ : Type}
    (decode : β → γ) (entries : List (String × β))
    (hranged : ∀ entry ∈ entries, Flapjack.Pancake.PanLang.NameRanged entry.1)
    (lookupExact : Flapjack.Basis.Pure.MlString.MlString → Option γ)
    (lookupProduction : String → Option β)
    (hbase : ∀ key,
      lookupExact key = (lookupProduction
        (Flapjack.Basis.Pure.MlString.toStringOfBytes key)).map decode) :
    ∀ key,
      Flapjack.FUPDATE_LIST lookupExact
          (entries.map (fun entry =>
            (Flapjack.Basis.Pure.MlString.ofString entry.1, decode entry.2))) key =
        (Flapjack.FUPDATE_LIST lookupProduction entries
          (Flapjack.Basis.Pure.MlString.toStringOfBytes key)).map decode := by
  induction entries generalizing lookupExact lookupProduction with
  | nil =>
      intro key
      simpa [Flapjack.FUPDATE_LIST_nil] using hbase key
  | cons entry entries ih =>
      obtain ⟨name, value⟩ := entry
      have hname : Flapjack.Pancake.PanLang.NameRanged name :=
        hranged (name, value) (by simp)
      have htail : ∀ entry ∈ entries,
          Flapjack.Pancake.PanLang.NameRanged entry.1 := by
        intro item hitem
        exact hranged item (by simp [hitem])
      have hupdated : ∀ key,
          Flapjack.FUPDATE lookupExact
              (Flapjack.Basis.Pure.MlString.ofString name, decode value) key =
            (Flapjack.FUPDATE lookupProduction (name, value)
              (Flapjack.Basis.Pure.MlString.toStringOfBytes key)).map decode := by
        intro key
        have hkey : Flapjack.Pancake.PanLang.NameRanged
            (Flapjack.Basis.Pure.MlString.toStringOfBytes key) :=
          PanToCrepContextExact.toProduction_key_nameRanged key
        by_cases heq : name = Flapjack.Basis.Pure.MlString.toStringOfBytes key
        · have heq' : Flapjack.Basis.Pure.MlString.ofString name = key := by
            rw [heq, Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
          have hprod : (name == Flapjack.Basis.Pure.MlString.toStringOfBytes key) = true :=
            beq_iff_eq.mpr heq
          have hexact : (Flapjack.Basis.Pure.MlString.ofString name == key) = true :=
            beq_iff_eq.mpr heq'
          simp [Flapjack.FUPDATE, hprod, hexact]
        · have hne : Flapjack.Basis.Pure.MlString.ofString name ≠ key := by
            intro hml
            have hml' : Flapjack.Basis.Pure.MlString.ofString name =
                Flapjack.Basis.Pure.MlString.ofString
                  (Flapjack.Basis.Pure.MlString.toStringOfBytes key) := by
              rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
              exact hml
            exact heq (ofString_injective_on_ranged_names hname hkey hml')
          have hprod : (name == Flapjack.Basis.Pure.MlString.toStringOfBytes key) = false :=
            beq_eq_false_iff_ne.mpr heq
          have hexact : (Flapjack.Basis.Pure.MlString.ofString name == key) = false :=
            beq_eq_false_iff_ne.mpr hne
          simp [Flapjack.FUPDATE, hprod, hexact, hbase key]
      intro key
      simpa only [List.map_cons, Flapjack.FUPDATE_LIST_cons] using
        ih htail (Flapjack.FUPDATE lookupExact
          (Flapjack.Basis.Pure.MlString.ofString name, decode value))
          (Flapjack.FUPDATE lookupProduction (name, value)) hupdated key

private theorem compileParamVars_entries_nameRanged
    (params : List (VarName × Shape)) (offset : Nat)
    (hparams : ∀ p ∈ params, Flapjack.Pancake.PanLang.NameRanged p.1) :
    ∀ entry ∈ (compileParamVars params offset).1,
      Flapjack.Pancake.PanLang.NameRanged entry.1 := by
  induction params generalizing offset with
  | nil => simp [compileParamVars]
  | cons parameter params ih =>
      obtain ⟨name, shape⟩ := parameter
      have hname := hparams (name, shape) (by simp)
      have htail : ∀ p ∈ params, Flapjack.Pancake.PanLang.NameRanged p.1 := by
        intro p hp
        exact hparams p (by simp [hp])
      simp only [compileParamVars]
      intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with hhead | htailMem
      · cases hhead
        exact hname
      · exact ih (offset + Shape.shapeSize shape) htail entry htailMem

/-- The exact `make_vmap` parameter entries are the byte-ranged production
    allocator entries encoded through the String/mlstring and Shape/ShapeHOL
    codecs. This is the finite-map boundary needed to route parser-backed
    `comp_func` through `compFuncExactHOLW`. -/
private theorem panToCrepMakeVmapHOLExactOfProductionParams
    (params : List (VarName × Shape))
    (hparams : ∀ p ∈ params,
      Flapjack.Pancake.PanLang.NameRanged p.1 ∧
        Flapjack.Pancake.PanLang.ShapeByteRanged p.2)
    (key : Flapjack.Basis.Pure.MlString.MlString) :
    (panToCrepMakeVmapHOLExact (params.map fun (name, shape) =>
      (Flapjack.Basis.Pure.MlString.ofString name,
        Flapjack.Pancake.PanLang.shapeToHOL shape))).lookup key =
      (panToCrepMakeVmapHOL params
        (Flapjack.Basis.Pure.MlString.toStringOfBytes key)).map
          (fun value => (Flapjack.Pancake.PanLang.shapeToHOL value.1, value.2)) := by
  let exactParams := params.map fun (name, shape) =>
    (Flapjack.Basis.Pure.MlString.ofString name,
      Flapjack.Pancake.PanLang.shapeToHOL shape)
  have hranged : ∀ entry ∈ (compileParamVars params 0).1,
      Flapjack.Pancake.PanLang.NameRanged entry.1 :=
    compileParamVars_entries_nameRanged params 0 (fun p hp => (hparams p hp).1)
  have hentries :
      ((compileParamVars params 0).1.map fun entry =>
        (Flapjack.Basis.Pure.MlString.ofString entry.1,
          (Flapjack.Pancake.PanLang.shapeToHOL entry.2.1, entry.2.2))) =
        (exactParams.map Prod.fst).zip
          ((exactParams.map Prod.snd).zip
            (Flapjack.Pancake.PanLang.withShapeHOL (exactParams.map Prod.snd)
              (List.range (Flapjack.Pancake.PanLang.sizeOfShapeHOL
                (.comb (exactParams.map Prod.snd)))))) := by
    calc
      _ = panToCrepParamsVmapEntriesOffset params 0 :=
        compileParamVars_vmap_entries params 0
      _ = _ := by
        simpa [exactParams, Function.comp_def] using
          panToCrepParamsVmapEntries_exact_offset params 0
  have hupdate := fupdateList_ofString_bridge
    (β := Shape × List Nat)
    (γ := Flapjack.Pancake.PanLang.ShapeHOL × List Nat)
    (fun value => (Flapjack.Pancake.PanLang.shapeToHOL value.1, value.2))
    (compileParamVars params 0).1
    (fun entry hentry => hranged entry hentry)
    (fun _ => none)
    FEMPTY
    (by intro query; rfl)
    key
  rw [Flapjack.holFmapAsFiniteSupportResultWitness_panToCrepMakeVmapHOLExact]
  simpa [exactParams, FEMPTY, panToCrepMakeVmapHOL,
    panToCrepMakeVmapRaw, hentries] using hupdate

private theorem holFiniteMapExact_ext_local {α β : Type}
    {left right : HolFiniteMapExact α β}
    (h : ∀ key, left.lookup key = right.lookup key) : left = right := by
  cases left with
  | mk l hl =>
    cases right with
    | mk r hr =>
      have heq : l = r := funext h
      subst r
      rfl

/-- Byte-ranged lookup congruence for the exact and production variable-map
    updates used by HOL `Dec` and `DecCall`. This deliberately proves lookup
    agreement only for a ranged update name and ranged query name: arbitrary
    Lean strings can alias after `ofString` truncates characters to HOL bytes,
    so equality of the complete production maps would be false. -/
theorem exactToProduction_decVarUpdate_lookup {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name query : String)
    (shape : ShapeHOL) (names : List Nat)
    (hname : Flapjack.Pancake.PanLang.NameRanged name)
    (hquery : Flapjack.Pancake.PanLang.NameRanged query) :
    (PanToCrepContextExact.toProduction
      { context with vars := (HolFiniteMapExact.update context.vars
          (Flapjack.Basis.Pure.MlString.ofString name, (shape, names))) }).vars query =
      FUPDATE context.toProduction.vars
        (name, (Flapjack.Pancake.PanLang.shapeOfHOL shape, names)) query := by
  have hkey :
      Flapjack.Basis.Pure.MlString.ofString name =
          Flapjack.Basis.Pure.MlString.ofString query ↔ name = query := by
    constructor
    · exact ofString_injective_on_ranged_names hname hquery
    · intro heq
      rw [heq]
  simp only [PanToCrepContextExact.toProduction,
    HolFiniteMapExact.lookup_update, FUPDATE]
  by_cases h : name = query
  · subst query
    simp
  · simp [hkey, h]

/-- The `DecCall` update uses a source-level shape rather than a compiled
    expression shape. Under the shape's byte-range premise its
    `shapeToHOL`/`shapeOfHOL` roundtrip reduces it to the same ranged-key
    lookup congruence as the `Dec` update above. -/
theorem exactToProduction_decCallVarUpdate_lookup {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name query : String)
    (shape : Shape) (names : List Nat)
    (hname : Flapjack.Pancake.PanLang.NameRanged name)
    (hquery : Flapjack.Pancake.PanLang.NameRanged query)
    (hshape : ShapeByteRanged shape) :
    (PanToCrepContextExact.toProduction
      { context with vars := (HolFiniteMapExact.update context.vars
          (Flapjack.Basis.Pure.MlString.ofString name,
            (Flapjack.Pancake.PanLang.shapeToHOL shape, names))) }).vars query =
      FUPDATE context.toProduction.vars (name, (shape, names)) query := by
  rw [exactToProduction_decVarUpdate_lookup context name query
    (Flapjack.Pancake.PanLang.shapeToHOL shape) names hname hquery]
  simp [Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL, hshape]

/-- Flapjack-specific context relation used by recursive exact-to-production
    compilation; there is no standalone HOL declaration for this bridge.
    Every map agrees at byte-ranged source names, and `vmax` agrees. The
    ranged domain is essential for all three maps: `MlString.ofString` keeps
    only the low byte of each character, so a non-ranged String key can alias
    a valid HOL name. Compiler queries decoded from HOL names are ranged. -/
def PanToCrepContextExactProdRel {width : Nat} [NeZero width]
    (exact : PanToCrepContextExact width)
    (production : PanToCrepHOLContext (BitVec width)) : Prop :=
  (∀ name, Flapjack.Pancake.PanLang.NameRanged name →
    exact.toProduction.funcs name = production.funcs name) ∧
  (∀ name, Flapjack.Pancake.PanLang.NameRanged name →
    exact.toProduction.eids name = production.eids name) ∧
  exact.vmax = production.vmax ∧
  (∀ name, Flapjack.Pancake.PanLang.NameRanged name →
    exact.toProduction.vars name = production.vars name)

/-- Flapjack-specific counterexample (no HOL original): `ofString` is not
    injective outside the source byte-name domain: codepoint
    256 aliases NUL. This checked witness explains why the context relation
    below is stated only for `NameRanged` lookup keys. -/
theorem mlString_ofString_alias_outside_byte_range :
    ∃ bad good : String,
      bad ≠ good ∧
      Flapjack.Basis.Pure.MlString.ofString bad =
        Flapjack.Basis.Pure.MlString.ofString good ∧
      ¬ Flapjack.Pancake.PanLang.NameRanged bad := by
  refine ⟨String.singleton (Char.ofNat 256), String.singleton (Char.ofNat 0), ?_⟩
  decide

/-- Flapjack-specific reflexivity helper for the context relation (no HOL
    original): the exact context always relates to its own production projection. -/
theorem panToCrepContextExactProdRel_refl {width : Nat} [NeZero width]
    (exact : PanToCrepContextExact width) :
    PanToCrepContextExactProdRel exact exact.toProduction := by
  refine ⟨?_, ?_, rfl, ?_⟩ <;> intro name _hname <;> rfl

/-- Flapjack-specific production-to-exact context bridge (no HOL original): a
    production context with the compiler's finite-support and byte-range
    evidence relates to its exactified context on every valid name. The
    evidence excludes keys for which `ofString` could alias a different byte
    name; no total String-map equality is claimed. -/
theorem panToCrepContextExactOfProduction_relation {width : Nat} [NeZero width]
    (production : PanToCrepHOLContext (BitVec width))
    (evidence : PanToCrepContextProductionEvidence production) :
    PanToCrepContextExactProdRel
      (panToCrepContextExactOfProduction production evidence) production := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro name hname
    simpa [PanToCrepContextExact.toProduction,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname] using
      panToCrepContextExactOfProduction_funcs_lookup_roundtrip
        production evidence name hname
  · intro name hname
    simp [PanToCrepContextExact.toProduction,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname]
  · intro name hname
    simpa [PanToCrepContextExact.toProduction,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname] using
      panToCrepContextExactOfProduction_vars_lookup_roundtrip
        production evidence name hname

/-- General-context `Seq` case for the relation-polymorphic recursive
    compiler bridge. Both children retain the same context pair, so the
    induction hypotheses consume the incoming ranged relation directly. -/
theorem compileProgExactHOLW_seq_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (first second : Flapjack.Pancake.PanLang.ProgHOL width)
    (hfirst : ∀ exactContext productionContext,
      PanToCrepContextExactProdRel exactContext productionContext →
      crepProgOfHOL (compileProgExactHOLW exactContext first) =
        compileProgHOL productionContext (progOfHOL first))
    (hsecond : ∀ exactContext productionContext,
      PanToCrepContextExactProdRel exactContext productionContext →
      crepProgOfHOL (compileProgExactHOLW exactContext second) =
        compileProgHOL productionContext (progOfHOL second)) :
    crepProgOfHOL (compileProgExactHOLW context (.seq first second)) =
      compileProgHOL productionContext (progOfHOL (.seq first second)) := by
  simp [compileProgExactHOLW, compileProgHOL, crepProgOfHOL, progOfHOL,
    hfirst context productionContext hcontext,
    hsecond context productionContext hcontext]

/-- The context relation is preserved by parallel exact/production variable
    updates when their keys are source-ranged and their decoded payloads agree.
    Unlike the base-context helper above, this form composes through recursive
    Dec and DecCall nests. -/
theorem exactProdRel_decUpdate {width : Nat} [NeZero width]
    (exact : PanToCrepContextExact width)
    (production : PanToCrepHOLContext (BitVec width))
    (hrel : PanToCrepContextExactProdRel exact production)
    (name : String) (exactShape : ShapeHOL) (productionShape : Shape)
    (names : List Nat) (exactBump productionBump : Nat)
    (hname : Flapjack.Pancake.PanLang.NameRanged name)
    (hshape : Flapjack.Pancake.PanLang.shapeOfHOL exactShape = productionShape)
    (hbump : exactBump = productionBump) :
    PanToCrepContextExactProdRel
      { exact with
        vars := HolFiniteMapExact.update exact.vars
          (Flapjack.Basis.Pure.MlString.ofString name, (exactShape, names))
        vmax := exact.vmax + exactBump }
      { production with
        vars := FUPDATE production.vars (name, (productionShape, names))
        vmax := production.vmax + productionBump } := by
  rcases hrel with ⟨hfuncs, heids, hvmax, hvars⟩
  refine ⟨hfuncs, heids, ?_, ?_⟩
  · simpa [hbump] using congrArg (fun value => value + exactBump) hvmax
  · intro query hquery
    have hkey :
        Flapjack.Basis.Pure.MlString.ofString name =
            Flapjack.Basis.Pure.MlString.ofString query ↔ name = query := by
      constructor
      · exact ofString_injective_on_ranged_names hname hquery
      · intro heq
        rw [heq]
    simp only [PanToCrepContextExact.toProduction,
      HolFiniteMapExact.lookup_update, FUPDATE]
    by_cases h : name = query
    · subst query
      simp [hshape]
    · have hExact : Flapjack.Basis.Pure.MlString.ofString name ≠
        Flapjack.Basis.Pure.MlString.ofString query := by
        intro heq
        exact h (hkey.mp heq)
      have hbase :
          (exact.vars.lookup (Flapjack.Basis.Pure.MlString.ofString query)).map
              (fun value => (Flapjack.Pancake.PanLang.shapeOfHOL value.1, value.2)) =
            production.vars query := by
        simpa [PanToCrepContextExact.toProduction] using hvars query hquery
      simpa [beq_iff_eq, hExact, h] using hbase

/-- The recursive expression codec under a ranged exact/production context
    relation. This packages the expression congruence with the exact compiler
    codec for use by program-clause induction. -/
theorem compileExpExactHOLW_prodCodec_of_contextRel {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (production : PanToCrepHOLContext (BitVec width))
    (hrel : PanToCrepContextExactProdRel context production)
    (expression : ExpHOL width) :
    ((compileExpExactHOLW context expression).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context expression).2)
      = compileExpHOL production (expOfHOL expression) := by
  exact compileExpExactHOLW_prodCodec_of_ranged_vars context production
    hrel.2.2.2 expression

/-- A `Dec` variable-map update preserves the ranged context relation needed
    for compiling the recursive body. Parameters expose the update payload and
    counter increments so this lemma can be instantiated from the `Dec` clause
    using its expression codec. -/
theorem exactToProduction_decContext_relation {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : String)
    (exactShape : ShapeHOL) (productionShape : Shape) (names : List Nat)
    (exactBump productionBump : Nat)
    (hname : Flapjack.Pancake.PanLang.NameRanged name)
    (hshape : Flapjack.Pancake.PanLang.shapeOfHOL exactShape = productionShape)
    (hbump : exactBump = productionBump) :
    PanToCrepContextExactProdRel
      { context with
        vars := HolFiniteMapExact.update context.vars
          (Flapjack.Basis.Pure.MlString.ofString name, (exactShape, names))
        vmax := context.vmax + exactBump }
      { context.toProduction with
        vars := FUPDATE context.toProduction.vars (name, (productionShape, names))
        vmax := context.toProduction.vmax + productionBump } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro query _hquery
    rfl
  · intro query _hquery
    rfl
  · simp [PanToCrepContextExact.toProduction, hbump]
  · intro query hquery
    simpa [PanToCrepContextExact.toProduction, hshape] using
      exactToProduction_decVarUpdate_lookup
      context name query exactShape names hname hquery

/-- Instantiation of the ranged context relation for the source-shape update
    used by HOL `DecCall`. The source `NameRanged` and `ShapeByteRanged`
    premises are exactly what make the String/MlString key and shape codecs
    invertible on the update. -/
theorem exactToProduction_decCallContext_relation {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : String) (shape : Shape)
    (names : List Nat)
    (hname : Flapjack.Pancake.PanLang.NameRanged name)
    (hshape : ShapeByteRanged shape) :
    PanToCrepContextExactProdRel
      { context with
        vars := HolFiniteMapExact.update context.vars
          (Flapjack.Basis.Pure.MlString.ofString name,
            (Flapjack.Pancake.PanLang.shapeToHOL shape, names))
        vmax := context.vmax +
          sizeOfShapeHOL (Flapjack.Pancake.PanLang.shapeToHOL shape) }
      { context.toProduction with
        vars := FUPDATE context.toProduction.vars
          (name, (shape, names))
        vmax := context.toProduction.vmax + Shape.shapeSize shape } := by
  apply exactToProduction_decContext_relation
    context name (Flapjack.Pancake.PanLang.shapeToHOL shape) shape names
    (sizeOfShapeHOL (Flapjack.Pancake.PanLang.shapeToHOL shape))
    (Shape.shapeSize shape) hname
  · exact Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL shape hshape
  · exact sizeOfShapeHOL_shapeToHOL shape

/-- Relation-polymorphic `If` case: condition compilation uses the ranged
    context relation, while both recursive branches preserve the same context
    pair and use their structural induction hypotheses. -/
theorem compileProgExactHOLW_if_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
    (hthen : crepProgOfHOL (compileProgExactHOLW context thenBranch) =
      compileProgHOL productionContext (progOfHOL thenBranch))
    (helse : crepProgOfHOL (compileProgExactHOLW context elseBranch) =
      compileProgHOL productionContext (progOfHOL elseBranch)) :
    crepProgOfHOL (compileProgExactHOLW context (.ite condition thenBranch elseBranch)) =
      compileProgHOL productionContext
        (.ite (expOfHOL condition) (progOfHOL thenBranch) (progOfHOL elseBranch)) := by
  have hcodec := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext condition
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨hexps, _hshape⟩
  simp only [compileProgExactHOLW, compileIfExactHOLW]
  cases hExact : compileExpExactHOLW context condition with
  | mk exactExpressions exactShape =>
      cases exactExpressions with
      | nil =>
          cases hProduction : compileExpHOL productionContext (expOfHOL condition) with
          | mk productionExpressions productionShape =>
              have hExpressions : productionExpressions = [] := by
                simpa [hExact, hProduction] using hexps.symm
              simp [compileProgHOL, hProduction, hExpressions, crepProgOfHOL]
      | cons head tail =>
          cases hProduction : compileExpHOL productionContext (expOfHOL condition) with
          | mk productionExpressions productionShape =>
              have hExpressions : productionExpressions =
                  (crepExpOfHOL head) :: (tail.map crepExpOfHOL) := by
                simpa [hExact, hProduction] using hexps.symm
              cases productionExpressions with
              | nil => simp at hExpressions
              | cons productionHead productionTail =>
                  have hHead : productionHead = crepExpOfHOL head :=
                    (List.cons.inj hExpressions).1
                  simp [compileProgHOL, hProduction, hHead, hthen, helse, crepProgOfHOL]

/-- Relation-polymorphic `While` case: condition compilation uses the ranged
    context relation and the body induction hypothesis keeps the same pair. -/
theorem compileProgExactHOLW_while_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (condition : ExpHOL width) (body : ProgHOL width)
    (ih : PanToCrepContextExactProdRel context productionContext →
      crepProgOfHOL (compileProgExactHOLW context body) =
        compileProgHOL productionContext (progOfHOL body)) :
    crepProgOfHOL (compileProgExactHOLW context (.while condition body)) =
      compileProgHOL productionContext
        (.while (expOfHOL condition) (progOfHOL body)) := by
  have hcodec := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext condition
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨hexps, _hshape⟩
  have hbody := ih hcontext
  simp only [compileProgExactHOLW, compileWhileExactHOLW]
  cases hExact : compileExpExactHOLW context condition with
  | mk exactExpressions exactShape =>
      cases exactExpressions with
      | nil =>
          cases hProduction : compileExpHOL productionContext (expOfHOL condition) with
          | mk productionExpressions productionShape =>
              have hExpressions : productionExpressions = [] := by
                simpa [hExact, hProduction] using hexps.symm
              simp [compileProgHOL, hProduction, hExpressions, crepProgOfHOL]
      | cons head tail =>
          cases hProduction : compileExpHOL productionContext (expOfHOL condition) with
          | mk productionExpressions productionShape =>
              have hExpressions : productionExpressions =
                  (crepExpOfHOL head) :: (tail.map crepExpOfHOL) := by
                simpa [hExact, hProduction] using hexps.symm
              cases productionExpressions with
              | nil => simp at hExpressions
              | cons productionHead productionTail =>
                  have hHead : productionHead = crepExpOfHOL head :=
                    (List.cons.inj hExpressions).1
                  simp [compileProgHOL, hProduction, hHead, hbody, crepProgOfHOL]

/-- Relation-polymorphic `Return` case. The exact and production compilers
    consume the same HOL expression, and the ranged context relation supplies
    the expression-codec equality needed to compare emitted names, expressions,
    and shape sizes. -/
theorem compileProgExactHOLW_return_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (expression : ExpHOL width) :
    crepProgOfHOL (compileProgExactHOLW context (.return expression)) =
      compileProgHOL productionContext (.return (expOfHOL expression)) := by
  have hcodec := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext expression
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨hexps, hshape⟩
  have hsize (shape : ShapeHOL) :
      Shape.shapeSize (shapeOfHOL shape) = sizeOfShapeHOL shape := by
    have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL shape)
    simpa only [shapeToHOL_shapeOfHOL] using h.symm
  have hprodsize :
      Shape.shapeSize (compileExpHOL productionContext (expOfHOL expression)).2 =
        sizeOfShapeHOL (compileExpExactHOLW context expression).2 := by
    calc
      Shape.shapeSize (compileExpHOL productionContext (expOfHOL expression)).2 =
          Shape.shapeSize (shapeOfHOL (compileExpExactHOLW context expression).2) := by
            rw [← hshape]
      _ = sizeOfShapeHOL (compileExpExactHOLW context expression).2 := hsize _
  simp only [compileProgExactHOLW, compileProgHOL, compileReturnExactHOLW]
  rw [hprodsize]
  by_cases hz : sizeOfShapeHOL (compileExpExactHOLW context expression).2 = 0
  · simp [hz, crepProgOfHOL]
  · simp [hz, crepProgOfHOL]
    exact hexps

/-- Context-independent leaf clauses remain equal for any related production
    context. These are recursive-induction base cases with no context lookup or
    expression compilation. -/
theorem compileProgExactHOLW_skip_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (_hcontext : PanToCrepContextExactProdRel context productionContext) :
    crepProgOfHOL (compileProgExactHOLW context (.skip : ProgHOL width)) =
      compileProgHOL productionContext (progOfHOL (.skip : ProgHOL width)) := by
  simp [compileProgExactHOLW, compileProgHOL, crepProgOfHOL, progOfHOL]

theorem compileProgExactHOLW_break_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (_hcontext : PanToCrepContextExactProdRel context productionContext) :
    crepProgOfHOL (compileProgExactHOLW context (.break : ProgHOL width)) =
      compileProgHOL productionContext (progOfHOL (.break : ProgHOL width)) := by
  simp [compileProgExactHOLW, compileProgHOL, crepProgOfHOL, progOfHOL]

theorem compileProgExactHOLW_continue_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (_hcontext : PanToCrepContextExactProdRel context productionContext) :
    crepProgOfHOL (compileProgExactHOLW context (.continue : ProgHOL width)) =
      compileProgHOL productionContext (progOfHOL (.continue : ProgHOL width)) := by
  simp [compileProgExactHOLW, compileProgHOL, crepProgOfHOL, progOfHOL]

theorem compileProgExactHOLW_tick_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (_hcontext : PanToCrepContextExactProdRel context productionContext) :
    crepProgOfHOL (compileProgExactHOLW context (.tick : ProgHOL width)) =
      compileProgHOL productionContext (progOfHOL (.tick : ProgHOL width)) := by
  simp [compileProgExactHOLW, compileProgHOL, crepProgOfHOL, progOfHOL]

theorem compileProgExactHOLW_annot_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (_hcontext : PanToCrepContextExactProdRel context productionContext)
    (tag text : MlS) :
    crepProgOfHOL (compileProgExactHOLW context (.annot tag text)) =
      compileProgHOL productionContext (progOfHOL (.annot tag text)) := by
  simp [compileProgExactHOLW, compileProgHOL, crepProgOfHOL, progOfHOL]

theorem compileProgExactHOLW_global_assign_relation_bridge
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (_hcontext : PanToCrepContextExactProdRel context productionContext)
    (name : MlS) (expression : ExpHOL width) :
    crepProgOfHOL
        (compileProgExactHOLW context (.assign .global name expression)) =
      compileProgHOL productionContext
        (progOfHOL (.assign .global name expression)) := by
  simp [compileProgExactHOLW, compileGlobalAssignExactHOLW,
    compileProgHOL, crepProgOfHOL, progOfHOL]

theorem compileProgExactHOLW_global_shmem_load_relation_bridge
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (_hcontext : PanToCrepContextExactProdRel context productionContext)
    (operator : OpSize) (name : MlS) (address : ExpHOL width) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.shMemLoad operator .global name address)) =
      compileProgHOL productionContext
        (progOfHOL (.shMemLoad operator .global name address)) := by
  simp [compileProgExactHOLW, compileGlobalShMemLoadExactHOLW,
    compileProgHOL, crepProgOfHOL, progOfHOL]

/-- Relation-polymorphic Store32 case. The two expression codecs suffice
    because the instruction clause does not inspect other context fields. -/
theorem compileProgExactHOLW_store32_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (address value : ExpHOL width) :
    crepProgOfHOL (compileProgExactHOLW context (.store32 address value)) =
      compileProgHOL productionContext
        (.store32 (expOfHOL address) (expOfHOL value)) := by
  have haddress := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext address
  have hvalue := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext value
  rw [Prod.mk.injEq] at haddress hvalue
  rcases haddress with ⟨haddressList, _haddressShape⟩
  rcases hvalue with ⟨hvalueList, _hvalueShape⟩
  cases hExactAddress : compileExpExactHOLW context address with
  | mk exactAddresses addressShape =>
      cases hExactValue : compileExpExactHOLW context value with
      | mk exactValues valueShape =>
          cases hProductionAddress :
              compileExpHOL productionContext (expOfHOL address) with
          | mk productionAddresses productionAddressShape =>
              cases hProductionValue :
                  compileExpHOL productionContext (expOfHOL value) with
              | mk productionValues productionValueShape =>
                  cases exactAddresses <;> cases exactValues <;>
                    cases productionAddresses <;> cases productionValues <;>
                    simp_all [compileProgExactHOLW, compileStore32ExactHOLW,
                      compileProgHOL, crepProgOfHOL]

/-- Relation-polymorphic StoreByte case, using the same pair of ranged
    expression codecs as Store32. -/
theorem compileProgExactHOLW_store_byte_relation_bridge
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (address value : ExpHOL width) :
    crepProgOfHOL (compileProgExactHOLW context (.storeByte address value)) =
      compileProgHOL productionContext
        (.storeByte (expOfHOL address) (expOfHOL value)) := by
  have haddress := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext address
  have hvalue := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext value
  rw [Prod.mk.injEq] at haddress hvalue
  rcases haddress with ⟨haddressList, _haddressShape⟩
  rcases hvalue with ⟨hvalueList, _hvalueShape⟩
  cases hExactAddress : compileExpExactHOLW context address with
  | mk exactAddresses addressShape =>
      cases hExactValue : compileExpExactHOLW context value with
      | mk exactValues valueShape =>
          cases hProductionAddress :
              compileExpHOL productionContext (expOfHOL address) with
          | mk productionAddresses productionAddressShape =>
              cases hProductionValue :
                  compileExpHOL productionContext (expOfHOL value) with
              | mk productionValues productionValueShape =>
                  cases exactAddresses <;> cases exactValues <;>
                    cases productionAddresses <;> cases productionValues <;>
                    simp_all [compileProgExactHOLW, compileStoreByteExactHOLW,
                      compileProgHOL, crepProgOfHOL]

/-! The recursive `Dec` clause bridge (`pan_to_crepScript.sml:141-152`). Both
    compilers ignore the declared `shape` and store the compiled shape: the
    exact clause extends `context` to `bodyContext` (fresh names from the old
    `vmax`, `vmax` bumped by `sizeOfShapeHOL`), production extends
    `context.toProduction` to `nextContext` (fresh names from
    `allocatedNamesHOL`, `vmax` bumped by `Shape.shapeSize`). The recursive
    hypothesis `hbody` is therefore taken at those two extended contexts; the
    caller discharges the two context equations definitionally and supplies
    `hbody` from the program induction under its ranged-input relation. -/
theorem compileProgExactHOLW_dec_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : String) (shape : Shape)
    (expression : Exp (BitVec width)) (body : ProgHOL width)
    (bodyContext : PanToCrepContextExact width)
    (nextContext : PanToCrepHOLContext (BitVec width))
    (hbodyContext :
      bodyContext =
        { context with
          vars := context.vars.update (Flapjack.Basis.Pure.MlString.ofString name,
            ((compileExpExactHOLW context (expToHOL expression)).2,
              (List.range (sizeOfShapeHOL
                (compileExpExactHOLW context (expToHOL expression)).2)).map
                (fun index => context.vmax + index + 1)))
          vmax := context.vmax +
            sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 })
    (hnextContext :
      nextContext =
        { context.toProduction with
          vars := FUPDATE context.toProduction.vars
            (name, ((compileExpHOL context.toProduction expression).2,
              allocatedNamesHOL context.toProduction
                (compileExpHOL context.toProduction expression).2))
          vmax := context.toProduction.vmax +
            Shape.shapeSize (compileExpHOL context.toProduction expression).2 })
    (hcodec :
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression)
    (hbody :
      crepProgOfHOL (compileProgExactHOLW bodyContext body) =
        compileProgHOL nextContext (progOfHOL body)) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.dec (Flapjack.Basis.Pure.MlString.ofString name) (shapeToHOL shape)
            (expToHOL expression) body)) =
      compileProgRiscV context.toProduction
        (.dec name shape expression (progOfHOL body)) := by
  have hsize (shape : ShapeHOL) :
      Shape.shapeSize (shapeOfHOL shape) = sizeOfShapeHOL shape := by
    have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL shape)
    simpa only [shapeToHOL_shapeOfHOL] using h.symm
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨hvalues, hshape⟩
  have hlength :
      (compileExpExactHOLW context (expToHOL expression)).1.length =
        (compileExpHOL context.toProduction expression).1.length := by
    have h := congrArg List.length hvalues
    simpa using h
  have hshapeSize :
      Shape.shapeSize (compileExpHOL context.toProduction expression).2 =
        sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 := by
    calc Shape.shapeSize (compileExpHOL context.toProduction expression).2
        = Shape.shapeSize
            (shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) := by
          rw [hshape]
      _ = sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 :=
          hsize _
  have hnames :
      (List.range (sizeOfShapeHOL
          (compileExpExactHOLW context (expToHOL expression)).2)).map
        (fun index => context.vmax + index + 1) =
      allocatedNamesHOL context.toProduction
        (compileExpHOL context.toProduction expression).2 := by
    rw [← hshapeSize]
    unfold allocatedNamesHOL
    change
      (List.range (Shape.shapeSize
          (compileExpHOL context.toProduction expression).2)).map
          (fun index => context.vmax + index + 1) =
        (List.range (Shape.shapeSize
          (compileExpHOL context.toProduction expression).2)).map
          (fun offset => context.vmax + 1 + offset)
    apply List.map_congr_left
    intro index _hin
    omega
  subst hbodyContext
  subst hnextContext
  simp only [compileProgExactHOLW, compileDecExactHOLW, compileProgRiscV,
    compileProgHOL]
  by_cases hcount :
      sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 =
        (compileExpExactHOLW context (expToHOL expression)).1.length
  · have hcountProduction :
        Shape.shapeSize (compileExpHOL context.toProduction expression).2 =
          (compileExpHOL context.toProduction expression).1.length := by
      rw [hshapeSize, ← hlength]
      exact hcount
    rw [if_neg (by simp [hcount]), if_pos hcountProduction]
    rw [crepProgOfHOL_nestedDecsHOL]
    rw [hbody]
    rw [hnames, hvalues]
  · have hcountProduction :
        ¬ (Shape.shapeSize (compileExpHOL context.toProduction expression).2 =
          (compileExpHOL context.toProduction expression).1.length) := by
      intro hcontra
      apply hcount
      rw [← hshapeSize, hlength]
      exact hcontra
    rw [if_pos (by simp [hcount]), if_neg hcountProduction]
    simp only [crepProgOfHOL]

/-- Recursive `Dec` bridge driven by the ranged context relation. The induction
    hypothesis is quantified over related exact/production contexts; this
    wrapper derives that relation for the body update and invokes the recursive
    hypothesis there, instead of asking callers to supply the body compiler
    equality as an unrelated premise. -/
theorem compileProgExactHOLW_dec_contextRel_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : String) (shape : Shape)
    (expression : Exp (BitVec width)) (body : ProgHOL width)
    (bodyContext : PanToCrepContextExact width)
    (nextContext : PanToCrepHOLContext (BitVec width))
    (hbodyContext :
      bodyContext =
        { context with
          vars := context.vars.update (Flapjack.Basis.Pure.MlString.ofString name,
            ((compileExpExactHOLW context (expToHOL expression)).2,
              (List.range (sizeOfShapeHOL
                (compileExpExactHOLW context (expToHOL expression)).2)).map
                (fun index => context.vmax + index + 1)))
          vmax := context.vmax +
            sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 })
    (hnextContext :
      nextContext =
        { context.toProduction with
          vars := FUPDATE context.toProduction.vars
            (name, ((compileExpHOL context.toProduction expression).2,
              allocatedNamesHOL context.toProduction
                (compileExpHOL context.toProduction expression).2))
          vmax := context.toProduction.vmax +
            Shape.shapeSize (compileExpHOL context.toProduction expression).2 })
    (hcodec :
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression)
    (hname : Flapjack.Pancake.PanLang.NameRanged name)
    (ih : ∀ exactContext productionContext,
      PanToCrepContextExactProdRel exactContext productionContext →
      crepProgOfHOL (compileProgExactHOLW exactContext body) =
        compileProgHOL productionContext (progOfHOL body)) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.dec (Flapjack.Basis.Pure.MlString.ofString name) (shapeToHOL shape)
            (expToHOL expression) body)) =
      compileProgRiscV context.toProduction
        (.dec name shape expression (progOfHOL body)) := by
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨hvalues, hshape⟩
  have hlength :
      (compileExpExactHOLW context (expToHOL expression)).1.length =
        (compileExpHOL context.toProduction expression).1.length := by
    have h := congrArg List.length hvalues
    simpa using h
  have hsize (exactShape : ShapeHOL) :
      Shape.shapeSize (shapeOfHOL exactShape) = sizeOfShapeHOL exactShape := by
    have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL exactShape)
    simpa only [shapeToHOL_shapeOfHOL] using h.symm
  have hshapeSize :
      Shape.shapeSize (compileExpHOL context.toProduction expression).2 =
        sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 := by
    calc Shape.shapeSize (compileExpHOL context.toProduction expression).2
        = Shape.shapeSize
            (shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) := by
          rw [hshape]
      _ = sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 := hsize _
  have hnames :
      (List.range (sizeOfShapeHOL
          (compileExpExactHOLW context (expToHOL expression)).2)).map
        (fun index => context.vmax + index + 1) =
      allocatedNamesHOL context.toProduction
        (compileExpHOL context.toProduction expression).2 := by
    rw [← hshapeSize]
    unfold allocatedNamesHOL
    change
      (List.range (Shape.shapeSize
          (compileExpHOL context.toProduction expression).2)).map
          (fun index => context.vmax + index + 1) =
        (List.range (Shape.shapeSize
          (compileExpHOL context.toProduction expression).2)).map
          (fun offset => context.vmax + 1 + offset)
    apply List.map_congr_left
    intro index _hin
    omega
  have hshapeRel :
      Flapjack.Pancake.PanLang.shapeOfHOL
        (compileExpExactHOLW context (expToHOL expression)).2 =
        (compileExpHOL context.toProduction expression).2 := by
    exact hshape
  have hbump :
      sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 =
        Shape.shapeSize (compileExpHOL context.toProduction expression).2 :=
    hshapeSize.symm
  have hbodyRel : PanToCrepContextExactProdRel bodyContext nextContext := by
    rw [hbodyContext, hnextContext]
    simpa [hnames] using
      exactToProduction_decContext_relation context name
        (compileExpExactHOLW context (expToHOL expression)).2
        (compileExpHOL context.toProduction expression).2
        (allocatedNamesHOL context.toProduction
          (compileExpHOL context.toProduction expression).2)
        (sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2)
        (Shape.shapeSize (compileExpHOL context.toProduction expression).2)
        hname hshapeRel hbump
  exact compileProgExactHOLW_dec_bridge context name shape expression body
    bodyContext nextContext hbodyContext hnextContext
    (by
      rw [Prod.mk.injEq]
      exact ⟨hvalues, hshape⟩)
    (ih bodyContext nextContext hbodyRel)

/-- General-context `Dec` case for a context-polymorphic structural induction.
    Unlike the specialized bridge above, the production context need only be
    related to `context.toProduction`; this is essential after an earlier
    ranged update, where off-range String lookups need not agree. -/
theorem compileProgExactHOLW_dec_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (name : String) (shape : Shape) (expression : Exp (BitVec width))
    (body : ProgHOL width)
    (bodyContext : PanToCrepContextExact width)
    (nextContext : PanToCrepHOLContext (BitVec width))
    (hbodyContext :
      bodyContext =
        { context with
          vars := context.vars.update (Flapjack.Basis.Pure.MlString.ofString name,
            ((compileExpExactHOLW context (expToHOL expression)).2,
              (List.range (sizeOfShapeHOL
                (compileExpExactHOLW context (expToHOL expression)).2)).map
                (fun index => context.vmax + index + 1)))
          vmax := context.vmax +
            sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 })
    (hnextContext :
      nextContext =
        { productionContext with
          vars := FUPDATE productionContext.vars
            (name, ((compileExpHOL productionContext expression).2,
              allocatedNamesHOL productionContext
                (compileExpHOL productionContext expression).2))
          vmax := productionContext.vmax +
            Shape.shapeSize (compileExpHOL productionContext expression).2 })
    (hcodec :
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL productionContext expression)
    (hname : Flapjack.Pancake.PanLang.NameRanged name)
    (ih : ∀ exactContext productionContext,
      PanToCrepContextExactProdRel exactContext productionContext →
      crepProgOfHOL (compileProgExactHOLW exactContext body) =
        compileProgHOL productionContext (progOfHOL body)) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.dec (Flapjack.Basis.Pure.MlString.ofString name) (shapeToHOL shape)
            (expToHOL expression) body)) =
      compileProgRiscV productionContext
        (.dec name shape expression (progOfHOL body)) := by
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨hvalues, hshape⟩
  have hlength :
      (compileExpExactHOLW context (expToHOL expression)).1.length =
        (compileExpHOL productionContext expression).1.length := by
    have h := congrArg List.length hvalues
    simpa using h
  have hsize (exactShape : ShapeHOL) :
      Shape.shapeSize (shapeOfHOL exactShape) = sizeOfShapeHOL exactShape := by
    have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL exactShape)
    simpa only [shapeToHOL_shapeOfHOL] using h.symm
  have hshapeSize :
      Shape.shapeSize (compileExpHOL productionContext expression).2 =
        sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 := by
    calc Shape.shapeSize (compileExpHOL productionContext expression).2
        = Shape.shapeSize
            (shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) := by
          rw [hshape]
      _ = sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 := hsize _
  have hnames :
      (List.range (sizeOfShapeHOL
          (compileExpExactHOLW context (expToHOL expression)).2)).map
        (fun index => context.vmax + index + 1) =
      allocatedNamesHOL productionContext
        (compileExpHOL productionContext expression).2 := by
    rw [← hshapeSize, hcontext.2.2.1]
    unfold allocatedNamesHOL
    change
      (List.range (Shape.shapeSize
          (compileExpHOL productionContext expression).2)).map
          (fun index => productionContext.vmax + index + 1) =
        (List.range (Shape.shapeSize
          (compileExpHOL productionContext expression).2)).map
          (fun offset => productionContext.vmax + 1 + offset)
    apply List.map_congr_left
    intro index _hin
    omega
  have hbodyRel : PanToCrepContextExactProdRel bodyContext nextContext := by
    rw [hbodyContext, hnextContext]
    have hrel := exactProdRel_decUpdate context productionContext hcontext name
      (compileExpExactHOLW context (expToHOL expression)).2
      (compileExpHOL productionContext expression).2
      (allocatedNamesHOL productionContext
        (compileExpHOL productionContext expression).2)
      (sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2)
      (Shape.shapeSize (compileExpHOL productionContext expression).2)
      hname hshape hshapeSize.symm
    simpa [hnames] using hrel
  have hbody := ih bodyContext nextContext hbodyRel
  have hcountNames :
      (List.range (sizeOfShapeHOL
          (compileExpExactHOLW context (expToHOL expression)).2)).map
        (fun index => context.vmax + index + 1) =
      allocatedNamesHOL productionContext
        (compileExpHOL productionContext expression).2 := hnames
  subst hbodyContext
  subst hnextContext
  simp only [compileProgExactHOLW, compileDecExactHOLW, compileProgRiscV,
    compileProgHOL]
  by_cases hcount :
      sizeOfShapeHOL (compileExpExactHOLW context (expToHOL expression)).2 =
        (compileExpExactHOLW context (expToHOL expression)).1.length
  · have hcountProduction :
        Shape.shapeSize (compileExpHOL productionContext expression).2 =
          (compileExpHOL productionContext expression).1.length := by
      rw [hshapeSize, ← hlength]
      exact hcount
    rw [if_neg (by simp [hcount]), if_pos hcountProduction]
    rw [crepProgOfHOL_nestedDecsHOL]
    rw [hbody]
    rw [hcountNames, hvalues]
  · have hcountProduction :
        ¬ (Shape.shapeSize (compileExpHOL productionContext expression).2 =
          (compileExpHOL productionContext expression).1.length) := by
      intro hcontra
      apply hcount
      rw [← hshapeSize, hlength]
      exact hcontra
    rw [if_pos (by simp [hcount]), if_neg hcountProduction]
    simp only [crepProgOfHOL]

/-! The recursive `DecCall` bridge (`pan_to_crepScript.sml:262-272`). Both
    compilers allocate the declared return shape's slots from the old `vmax`,
    extend the variable map with `(name, (shape, names))` and `vmax` by the
    shape size, zero-initialize the return slots, then emit the target `Call`
    followed by the recursively compiled body. The body is compiled under the
    extended contexts, so `hbody` is taken there (as for `Dec`); `hfunction`
    is the byte-range evidence needed to decode the `MlString` callee. -/
theorem compileProgExactHOLW_decCall_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name function : String)
    (shape : Shape) (arguments : List (Exp (BitVec width))) (body : ProgHOL width)
    (bodyContext : PanToCrepContextExact width)
    (nextContext : PanToCrepHOLContext (BitVec width))
    (hbodyContext :
      bodyContext =
        { context with
          vars := context.vars.update (Flapjack.Basis.Pure.MlString.ofString name,
            (shapeToHOL shape,
              (List.range (sizeOfShapeHOL (shapeToHOL shape))).map
                (fun index => context.vmax + index + 1)))
          vmax := context.vmax + sizeOfShapeHOL (shapeToHOL shape) })
    (hnextContext :
      nextContext =
        { context.toProduction with
          vars := FUPDATE context.toProduction.vars
            (name, (shape,
              (List.range (Shape.shapeSize shape)).map
                (fun offset => context.toProduction.vmax + 1 + offset)))
          vmax := context.toProduction.vmax + Shape.shapeSize shape })
    (hcodec : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hbody :
      crepProgOfHOL (compileProgExactHOLW bodyContext body) =
        compileProgHOL nextContext (progOfHOL body)) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.decCall (Flapjack.Basis.Pure.MlString.ofString name) (shapeToHOL shape)
            (Flapjack.Basis.Pure.MlString.ofString function)
            (arguments.map expToHOL) body)) =
      compileProgRiscV context.toProduction
        (.decCall name shape function arguments (progOfHOL body)) := by
  have hsize (shape : ShapeHOL) :
      Shape.shapeSize (shapeOfHOL shape) = sizeOfShapeHOL shape := by
    have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL shape)
    simpa only [shapeToHOL_shapeOfHOL] using h.symm
  have hsizeArg : sizeOfShapeHOL (shapeToHOL shape) = Shape.shapeSize shape :=
    sizeOfShapeHOL_shapeToHOL shape
  have hfunctionDecode :
      Flapjack.Basis.Pure.MlString.toStringOfBytes
        (Flapjack.Basis.Pure.MlString.ofString function) = function :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hnames :
      (List.range (sizeOfShapeHOL (shapeToHOL shape))).map
          (fun index => context.vmax + index + 1) =
        allocatedNamesHOL context.toProduction shape := by
    rw [hsizeArg]
    unfold allocatedNamesHOL
    apply List.map_congr_left
    intro index _hin
    change context.vmax + index + 1 = context.vmax + 1 + index
    omega
  have hvalues :
      ((List.replicate
            ((List.range (sizeOfShapeHOL (shapeToHOL shape))).map
              (fun index => context.vmax + index + 1)).length
            (CrepExpHOL.const (0 : BitVec width))).map crepExpOfHOL) =
        (allocatedNamesHOL context.toProduction shape).map
          (fun _ => CrepExp.const (0 : BitVec width)) := by
    rw [hnames, List.map_replicate]
    simp only [crepExpOfHOL]
    rw [List.map_const']
  have hargs :=
    crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  subst hbodyContext
  subst hnextContext
  simp only [compileProgExactHOLW, compileDecCallExactHOLW, compileProgRiscV,
    compileProgHOL]
  rw [crepProgOfHOL_nestedDecsHOL]
  simp only [crepProgOfHOL]
  rw [hbody]
  rw [hvalues]
  rw [hargs]
  rw [hfunctionDecode]
  rw [hnames]
  dsimp only
  simp only [allocatedNamesHOL]

/-- Recursive `DecCall` bridge driven by the ranged context relation. This is
    the recursive-context analogue of `compileProgExactHOLW_dec_bridge`: the
    exact and production body contexts are related by the DecCall update, and
    the body compiler equality is obtained by applying a relation-polymorphic
    induction hypothesis at those contexts. -/
theorem compileProgExactHOLW_decCall_contextRel_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name function : String)
    (shape : Shape) (arguments : List (Exp (BitVec width))) (body : ProgHOL width)
    (bodyContext : PanToCrepContextExact width)
    (nextContext : PanToCrepHOLContext (BitVec width))
    (hbodyContext :
      bodyContext =
        { context with
          vars := context.vars.update (Flapjack.Basis.Pure.MlString.ofString name,
            (shapeToHOL shape,
              (List.range (sizeOfShapeHOL (shapeToHOL shape))).map
                (fun index => context.vmax + index + 1)))
          vmax := context.vmax + sizeOfShapeHOL (shapeToHOL shape) })
    (hnextContext :
      nextContext =
        { context.toProduction with
          vars := FUPDATE context.toProduction.vars
            (name, (shape,
              (List.range (Shape.shapeSize shape)).map
                (fun offset => context.toProduction.vmax + 1 + offset)))
          vmax := context.toProduction.vmax + Shape.shapeSize shape })
    (hcodec : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression)
    (hname : Flapjack.Pancake.PanLang.NameRanged name)
    (hshape : ShapeByteRanged shape)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (ih : ∀ exactContext productionContext,
      PanToCrepContextExactProdRel exactContext productionContext →
      crepProgOfHOL (compileProgExactHOLW exactContext body) =
        compileProgHOL productionContext (progOfHOL body)) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.decCall (Flapjack.Basis.Pure.MlString.ofString name) (shapeToHOL shape)
            (Flapjack.Basis.Pure.MlString.ofString function)
            (arguments.map expToHOL) body)) =
      compileProgRiscV context.toProduction
        (.decCall name shape function arguments (progOfHOL body)) := by
  have hnames :
      (List.range (sizeOfShapeHOL (shapeToHOL shape))).map
          (fun index => context.vmax + index + 1) =
        (List.range (Shape.shapeSize shape)).map
          (fun offset => context.toProduction.vmax + 1 + offset) := by
    have hsize := sizeOfShapeHOL_shapeToHOL shape
    simp only [PanToCrepContextExact.toProduction] at hsize ⊢
    rw [hsize]
    apply List.map_congr_left
    intro index _hin
    omega
  have hbodyRel : PanToCrepContextExactProdRel bodyContext nextContext := by
    rw [hbodyContext, hnextContext]
    have hrel := exactToProduction_decCallContext_relation
      context name shape ((List.range (Shape.shapeSize shape)).map
        (fun offset => context.vmax + 1 + offset)) hname hshape
    simpa [PanToCrepContextExact.toProduction, hnames] using hrel
  exact compileProgExactHOLW_decCall_bridge context name function shape arguments body
    bodyContext nextContext hbodyContext hnextContext hcodec hfunction
    (ih bodyContext nextContext hbodyRel)

/-- General-context `DecCall` case for the structural exact/production
    induction. It carries the incoming context relation through the parallel
    variable-map updates and obtains the recursive body equality from the IH. -/
theorem compileProgExactHOLW_decCall_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (name function : String) (shape : Shape)
    (arguments : List (Exp (BitVec width))) (body : ProgHOL width)
    (bodyContext : PanToCrepContextExact width)
    (nextContext : PanToCrepHOLContext (BitVec width))
    (hbodyContext :
      bodyContext =
        { context with
          vars := context.vars.update (Flapjack.Basis.Pure.MlString.ofString name,
            (shapeToHOL shape,
              (List.range (sizeOfShapeHOL (shapeToHOL shape))).map
                (fun index => context.vmax + index + 1)))
          vmax := context.vmax + sizeOfShapeHOL (shapeToHOL shape) })
    (hnextContext :
      nextContext =
        { productionContext with
          vars := FUPDATE productionContext.vars
            (name, (shape,
              (List.range (Shape.shapeSize shape)).map
                (fun offset => productionContext.vmax + 1 + offset)))
          vmax := productionContext.vmax + Shape.shapeSize shape })
    (hcodec : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL productionContext expression)
    (hname : Flapjack.Pancake.PanLang.NameRanged name)
    (hshape : ShapeByteRanged shape)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (ih : ∀ exactContext productionContext,
      PanToCrepContextExactProdRel exactContext productionContext →
      crepProgOfHOL (compileProgExactHOLW exactContext body) =
        compileProgHOL productionContext (progOfHOL body)) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.decCall (Flapjack.Basis.Pure.MlString.ofString name) (shapeToHOL shape)
            (Flapjack.Basis.Pure.MlString.ofString function)
            (arguments.map expToHOL) body)) =
      compileProgRiscV productionContext
        (.decCall name shape function arguments (progOfHOL body)) := by
  have hsizeArg : sizeOfShapeHOL (shapeToHOL shape) = Shape.shapeSize shape :=
    sizeOfShapeHOL_shapeToHOL shape
  have hnames :
      (List.range (sizeOfShapeHOL (shapeToHOL shape))).map
          (fun index => context.vmax + index + 1) =
        allocatedNamesHOL productionContext shape := by
    rw [hsizeArg, hcontext.2.2.1]
    unfold allocatedNamesHOL
    apply List.map_congr_left
    intro index _hin
    change productionContext.vmax + index + 1 = productionContext.vmax + 1 + index
    omega
  have hnamesProd :
      allocatedNamesHOL productionContext shape =
        (List.range (Shape.shapeSize shape)).map
          (fun offset => productionContext.vmax + 1 + offset) := by
    simp [allocatedNamesHOL]
  have hnamesBoth :
      (List.range (sizeOfShapeHOL (shapeToHOL shape))).map
          (fun index => context.vmax + index + 1) =
        (List.range (Shape.shapeSize shape)).map
          (fun offset => productionContext.vmax + 1 + offset) :=
    hnames.trans hnamesProd
  have hbodyRel : PanToCrepContextExactProdRel bodyContext nextContext := by
    rw [hbodyContext, hnextContext]
    have hrel := exactProdRel_decUpdate context productionContext hcontext name
      (shapeToHOL shape) shape
      ((List.range (sizeOfShapeHOL (shapeToHOL shape))).map
        (fun index => context.vmax + index + 1))
      (sizeOfShapeHOL (shapeToHOL shape)) (Shape.shapeSize shape)
      hname (shapeOfHOL_shapeToHOL shape hshape) hsizeArg
    rw [← hnamesBoth]
    exact hrel
  have hbody := ih bodyContext nextContext hbodyRel
  have hfunctionDecode :
      Flapjack.Basis.Pure.MlString.toStringOfBytes
        (Flapjack.Basis.Pure.MlString.ofString function) = function :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hvalues :
      ((List.replicate
            ((List.range (sizeOfShapeHOL (shapeToHOL shape))).map
              (fun index => context.vmax + index + 1)).length
            (CrepExpHOL.const (0 : BitVec width))).map crepExpOfHOL) =
        (allocatedNamesHOL productionContext shape).map
          (fun _ => CrepExp.const (0 : BitVec width)) := by
    rw [hnames, List.map_replicate]
    simp only [crepExpOfHOL]
    rw [List.map_const']
  have hargs := crepProgOfHOL_compileArgumentList_flatMapAt
    context productionContext arguments hcodec
  subst hbodyContext
  subst hnextContext
  simp only [compileProgExactHOLW, compileDecCallExactHOLW, compileProgRiscV,
    compileProgHOL]
  rw [crepProgOfHOL_nestedDecsHOL]
  simp only [crepProgOfHOL]
  rw [hbody]
  rw [hvalues]
  rw [hargs]
  rw [hfunctionDecode]
  rw [hnames]
  simp only [allocatedNamesHOL]

/-- Source-reviewed HOL `ExtCall` success clause (`pan_to_crepScript.sml:274-290`).
    When all four operand shapes are `One` and all four compiled operand lists
    are nonempty, HOL binds four temporaries numbered from one past the maximum
    variable occurring in any compiled operand and emits the target `ExtCall`.
    The caller supplies the two compiler results per operand and the decoded
    heads; the temporary bound is aligned from the four full value-list codecs. -/
theorem compileProgExactHOLW_extCall_success_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (function : String)
    (configuration configurationLength array arrayLength : Exp (BitVec width))
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (exactConfiguration : CrepExpHOL width)
    (exactConfigurationRest : List (CrepExpHOL width))
    (exactConfigurationLength : CrepExpHOL width)
    (exactConfigurationLengthRest : List (CrepExpHOL width))
    (exactArray : CrepExpHOL width) (exactArrayRest : List (CrepExpHOL width))
    (exactArrayLength : CrepExpHOL width)
    (exactArrayLengthRest : List (CrepExpHOL width))
    (productionConfiguration : CrepExp (BitVec width))
    (productionConfigurationRest : List (CrepExp (BitVec width)))
    (productionConfigurationLength : CrepExp (BitVec width))
    (productionConfigurationLengthRest : List (CrepExp (BitVec width)))
    (productionArray : CrepExp (BitVec width))
    (productionArrayRest : List (CrepExp (BitVec width)))
    (productionArrayLength : CrepExp (BitVec width))
    (productionArrayLengthRest : List (CrepExp (BitVec width)))
    (hexactConfiguration : compileExpExactHOLW context (expToHOL configuration) =
      (exactConfiguration :: exactConfigurationRest, .one))
    (hexactConfigurationLength : compileExpExactHOLW context (expToHOL configurationLength) =
      (exactConfigurationLength :: exactConfigurationLengthRest, .one))
    (hexactArray : compileExpExactHOLW context (expToHOL array) =
      (exactArray :: exactArrayRest, .one))
    (hexactArrayLength : compileExpExactHOLW context (expToHOL arrayLength) =
      (exactArrayLength :: exactArrayLengthRest, .one))
    (hproductionConfiguration : compileExpHOL context.toProduction configuration =
      (productionConfiguration :: productionConfigurationRest, .one))
    (hproductionConfigurationLength : compileExpHOL context.toProduction configurationLength =
      (productionConfigurationLength :: productionConfigurationLengthRest, .one))
    (hproductionArray : compileExpHOL context.toProduction array =
      (productionArray :: productionArrayRest, .one))
    (hproductionArrayLength : compileExpHOL context.toProduction arrayLength =
      (productionArrayLength :: productionArrayLengthRest, .one))
    (hvaluesConfiguration :
      (exactConfiguration :: exactConfigurationRest).map crepExpOfHOL =
        productionConfiguration :: productionConfigurationRest)
    (hvaluesConfigurationLength :
      (exactConfigurationLength :: exactConfigurationLengthRest).map crepExpOfHOL =
        productionConfigurationLength :: productionConfigurationLengthRest)
    (hvaluesArray : (exactArray :: exactArrayRest).map crepExpOfHOL =
        productionArray :: productionArrayRest)
    (hvaluesArrayLength :
      (exactArrayLength :: exactArrayLengthRest).map crepExpOfHOL =
        productionArrayLength :: productionArrayLengthRest) :
    crepProgOfHOL (compileProgExactHOLW context
        (.extCall (Flapjack.Basis.Pure.MlString.ofString function)
          (expToHOL configuration) (expToHOL configurationLength)
          (expToHOL array) (expToHOL arrayLength))) =
      compileProgRiscV context.toProduction
        (.extCall function configuration configurationLength array arrayLength) := by
  have hfunctionDecode :
      Flapjack.Basis.Pure.MlString.toStringOfBytes
        (Flapjack.Basis.Pure.MlString.ofString function) = function :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hmax :
      List.foldl (fun maximum variableIndex => Nat.max maximum variableIndex) 0
        (((exactConfiguration :: exactConfigurationRest) ++
          (exactConfigurationLength :: exactConfigurationLengthRest) ++
          (exactArray :: exactArrayRest) ++
          (exactArrayLength :: exactArrayLengthRest)).flatMap
          (fun value => crepExpVarsW (crepExpOfHOL value))) =
      maxCrepExpVarHOL
        ((productionConfiguration :: productionConfigurationRest) ++
          (productionConfigurationLength :: productionConfigurationLengthRest) ++
          (productionArray :: productionArrayRest) ++
          (productionArrayLength :: productionArrayLengthRest)) := by
    rw [crepExpVarsW_flatMap_crepExpOfHOL]
    simp only [maxCrepExpVarHOL, List.map_append,
      hvaluesConfiguration, hvaluesConfigurationLength, hvaluesArray,
      hvaluesArrayLength]
  have hheadConfiguration :
      crepExpOfHOL exactConfiguration = productionConfiguration := by
    have h := hvaluesConfiguration
    simp only [List.map_cons] at h
    exact (List.cons.inj h).1
  have hheadConfigurationLength :
      crepExpOfHOL exactConfigurationLength = productionConfigurationLength := by
    have h := hvaluesConfigurationLength
    simp only [List.map_cons] at h
    exact (List.cons.inj h).1
  have hheadArray : crepExpOfHOL exactArray = productionArray := by
    have h := hvaluesArray
    simp only [List.map_cons] at h
    exact (List.cons.inj h).1
  have hheadArrayLength :
      crepExpOfHOL exactArrayLength = productionArrayLength := by
    have h := hvaluesArrayLength
    simp only [List.map_cons] at h
    exact (List.cons.inj h).1
  simp only [compileProgExactHOLW, compileExtCallExactHOLW, compileProgRiscV,
    compileProgHOL, hexactConfiguration, hexactConfigurationLength, hexactArray,
    hexactArrayLength, hproductionConfiguration, hproductionConfigurationLength,
    hproductionArray, hproductionArrayLength]
  rw [hmax]
  simp only [crepProgOfHOL, nestedDecs, hheadConfiguration,
    hheadConfigurationLength, hheadArray, hheadArrayLength, hfunctionDecode]

/-- Source-reviewed HOL `ExtCall` fallback clause (`pan_to_crepScript.sml:274-290`).
    HOL `compile_ext_call` returns `Skip` unless every one of the four operand
    shapes is `One` and every compiled operand list is nonempty. The caller
    supplies the decoded compiler results and a guard-failure disjunction; the
    production equation agrees because each decoded shape/value failure is
    preserved by `shapeOfHOL` and `List.map crepExpOfHOL`. -/
theorem compileProgExactHOLW_extCall_skip_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (function : String)
    (configuration configurationLength array arrayLength : Exp (BitVec width))
    (exactConfigurationValues : List (CrepExpHOL width))
    (exactConfigurationShape : ShapeHOL)
    (exactConfigurationLengthValues : List (CrepExpHOL width))
    (exactConfigurationLengthShape : ShapeHOL)
    (exactArrayValues : List (CrepExpHOL width)) (exactArrayShape : ShapeHOL)
    (exactArrayLengthValues : List (CrepExpHOL width))
    (exactArrayLengthShape : ShapeHOL)
    (productionConfigurationValues : List (CrepExp (BitVec width)))
    (productionConfigurationShape : Shape)
    (productionConfigurationLengthValues : List (CrepExp (BitVec width)))
    (productionConfigurationLengthShape : Shape)
    (productionArrayValues : List (CrepExp (BitVec width)))
    (productionArrayShape : Shape)
    (productionArrayLengthValues : List (CrepExp (BitVec width)))
    (productionArrayLengthShape : Shape)
    (hexactConfiguration : compileExpExactHOLW context (expToHOL configuration) =
      (exactConfigurationValues, exactConfigurationShape))
    (hexactConfigurationLength : compileExpExactHOLW context (expToHOL configurationLength) =
      (exactConfigurationLengthValues, exactConfigurationLengthShape))
    (hexactArray : compileExpExactHOLW context (expToHOL array) =
      (exactArrayValues, exactArrayShape))
    (hexactArrayLength : compileExpExactHOLW context (expToHOL arrayLength) =
      (exactArrayLengthValues, exactArrayLengthShape))
    (hproductionConfiguration : compileExpHOL context.toProduction configuration =
      (productionConfigurationValues, productionConfigurationShape))
    (hproductionConfigurationLength : compileExpHOL context.toProduction configurationLength =
      (productionConfigurationLengthValues, productionConfigurationLengthShape))
    (hproductionArray : compileExpHOL context.toProduction array =
      (productionArrayValues, productionArrayShape))
    (hproductionArrayLength : compileExpHOL context.toProduction arrayLength =
      (productionArrayLengthValues, productionArrayLengthShape))
    (hconfigurationShapeSymm :
      productionConfigurationShape = shapeOfHOL exactConfigurationShape)
    (hconfigurationLengthShapeSymm :
      productionConfigurationLengthShape = shapeOfHOL exactConfigurationLengthShape)
    (harrayShapeSymm : productionArrayShape = shapeOfHOL exactArrayShape)
    (harrayLengthShapeSymm :
      productionArrayLengthShape = shapeOfHOL exactArrayLengthShape)
    (hconfigurationValuesSymm :
      productionConfigurationValues = exactConfigurationValues.map crepExpOfHOL)
    (hconfigurationLengthValuesSymm :
      productionConfigurationLengthValues = exactConfigurationLengthValues.map crepExpOfHOL)
    (harrayValuesSymm :
      productionArrayValues = exactArrayValues.map crepExpOfHOL)
    (harrayLengthValuesSymm :
      productionArrayLengthValues = exactArrayLengthValues.map crepExpOfHOL)
    (hguard : exactConfigurationShape ≠ .one
      ∨ exactConfigurationLengthShape ≠ .one
      ∨ exactArrayShape ≠ .one
      ∨ exactArrayLengthShape ≠ .one
      ∨ exactConfigurationValues = []
      ∨ exactConfigurationLengthValues = []
      ∨ exactArrayValues = []
      ∨ exactArrayLengthValues = []) :
    crepProgOfHOL (compileProgExactHOLW context
        (.extCall (Flapjack.Basis.Pure.MlString.ofString function)
          (expToHOL configuration) (expToHOL configurationLength)
          (expToHOL array) (expToHOL arrayLength))) =
      compileProgRiscV context.toProduction
        (.extCall function configuration configurationLength array arrayLength) := by
  rcases hguard with h | h | h | h | h | h | h | h
  · cases exactConfigurationShape <;>
      simp_all [compileProgExactHOLW, compileExtCallExactHOLW, compileProgRiscV,
      compileProgHOL, crepProgOfHOL, shapeOfHOL]
  · cases exactConfigurationLengthShape <;>
      simp_all [compileProgExactHOLW, compileExtCallExactHOLW, compileProgRiscV,
      compileProgHOL, crepProgOfHOL, shapeOfHOL]
  · cases exactArrayShape <;>
      simp_all [compileProgExactHOLW, compileExtCallExactHOLW, compileProgRiscV,
      compileProgHOL, crepProgOfHOL, shapeOfHOL]
  · cases exactArrayLengthShape <;>
      simp_all [compileProgExactHOLW, compileExtCallExactHOLW, compileProgRiscV,
      compileProgHOL, crepProgOfHOL, shapeOfHOL]
  · subst h
    simp_all [compileProgExactHOLW, compileExtCallExactHOLW, compileProgRiscV,
      compileProgHOL, crepProgOfHOL, List.map_nil]
  · subst h
    simp_all [compileProgExactHOLW, compileExtCallExactHOLW, compileProgRiscV,
      compileProgHOL, crepProgOfHOL, List.map_nil]
  · subst h
    simp_all [compileProgExactHOLW, compileExtCallExactHOLW, compileProgRiscV,
      compileProgHOL, crepProgOfHOL, List.map_nil]
  · subst h
    simp_all [compileProgExactHOLW, compileExtCallExactHOLW, compileProgRiscV,
      compileProgHOL, crepProgOfHOL, List.map_nil]

/-- Relation-polymorphic `ExtCall` case.  The four exact/production expression
    codecs preserve both the `One`/nonempty guards and every value used to
    compute HOL's maximum temporary index; related contexts then preserve the
    production-side maximum through `vmax` and the four compiled expressions.
    This is Flapjack proof infrastructure, source-reviewed against the HOL
    `compile_def` clause at `pan_to_crepScript.sml:274-290`. -/
theorem compileProgExactHOLW_extCall_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (function : String)
    (configuration configurationLength array arrayLength : Exp (BitVec width))
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hconfiguration : Flapjack.Pancake.PanLang.ExpByteRanged configuration)
    (hconfigurationLength :
      Flapjack.Pancake.PanLang.ExpByteRanged configurationLength)
    (harray : Flapjack.Pancake.PanLang.ExpByteRanged array)
    (harrayLength : Flapjack.Pancake.PanLang.ExpByteRanged arrayLength) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.extCall (Flapjack.Basis.Pure.MlString.ofString function)
            (expToHOL configuration) (expToHOL configurationLength)
            (expToHOL array) (expToHOL arrayLength))) =
      compileProgHOL productionContext
        (.extCall function configuration configurationLength array arrayLength) := by
  have hbaseRel : PanToCrepContextExactProdRel context context.toProduction := by
    exact panToCrepContextExactProdRel_refl context
  have hbaseConfiguration := compileExpExactHOLW_prodCodec_of_contextRel
    context context.toProduction hbaseRel (expToHOL configuration)
  have hbaseConfigurationLength := compileExpExactHOLW_prodCodec_of_contextRel
    context context.toProduction hbaseRel (expToHOL configurationLength)
  have hbaseArray := compileExpExactHOLW_prodCodec_of_contextRel
    context context.toProduction hbaseRel (expToHOL array)
  have hbaseArrayLength := compileExpExactHOLW_prodCodec_of_contextRel
    context context.toProduction hbaseRel (expToHOL arrayLength)
  have hproductionConfiguration := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext (expToHOL configuration)
  have hproductionConfigurationLength := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext (expToHOL configurationLength)
  have hproductionArray := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext (expToHOL array)
  have hproductionArrayLength := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext (expToHOL arrayLength)
  have hbaseConfiguration' :
      ((compileExpExactHOLW context (expToHOL configuration)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL configuration)).2) =
        compileExpHOL context.toProduction configuration := by
    rw [Flapjack.Pancake.PanLang.expOfHOL_expToHOL configuration hconfiguration] at hbaseConfiguration
    exact hbaseConfiguration
  have hbaseConfigurationLength' :
      ((compileExpExactHOLW context (expToHOL configurationLength)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL configurationLength)).2) =
        compileExpHOL context.toProduction configurationLength := by
    rw [Flapjack.Pancake.PanLang.expOfHOL_expToHOL configurationLength hconfigurationLength] at hbaseConfigurationLength
    exact hbaseConfigurationLength
  have hbaseArray' :
      ((compileExpExactHOLW context (expToHOL array)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL array)).2) =
        compileExpHOL context.toProduction array := by
    rw [Flapjack.Pancake.PanLang.expOfHOL_expToHOL array harray] at hbaseArray
    exact hbaseArray
  have hbaseArrayLength' :
      ((compileExpExactHOLW context (expToHOL arrayLength)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL arrayLength)).2) =
        compileExpHOL context.toProduction arrayLength := by
    rw [Flapjack.Pancake.PanLang.expOfHOL_expToHOL arrayLength harrayLength] at hbaseArrayLength
    exact hbaseArrayLength
  have hconfigurationCongr :
      compileExpHOL context.toProduction configuration =
        compileExpHOL productionContext configuration :=
    hbaseConfiguration'.symm.trans (by
      rw [Flapjack.Pancake.PanLang.expOfHOL_expToHOL configuration hconfiguration] at hproductionConfiguration
      exact hproductionConfiguration)
  have hconfigurationLengthCongr :
      compileExpHOL context.toProduction configurationLength =
        compileExpHOL productionContext configurationLength :=
    hbaseConfigurationLength'.symm.trans (by
      rw [Flapjack.Pancake.PanLang.expOfHOL_expToHOL configurationLength hconfigurationLength] at hproductionConfigurationLength
      exact hproductionConfigurationLength)
  have harrayCongr :
      compileExpHOL context.toProduction array =
        compileExpHOL productionContext array :=
    hbaseArray'.symm.trans (by
      rw [Flapjack.Pancake.PanLang.expOfHOL_expToHOL array harray] at hproductionArray
      exact hproductionArray)
  have harrayLengthCongr :
      compileExpHOL context.toProduction arrayLength =
        compileExpHOL productionContext arrayLength :=
    hbaseArrayLength'.symm.trans (by
      rw [Flapjack.Pancake.PanLang.expOfHOL_expToHOL arrayLength harrayLength] at hproductionArrayLength
      exact hproductionArrayLength)
  have hvmax : context.toProduction.vmax = productionContext.vmax := by
    simpa [PanToCrepContextExact.toProduction] using hcontext.2.2.1
  have hbaseToProduction :
      compileProgRiscV context.toProduction
          (.extCall function configuration configurationLength array arrayLength) =
        compileProgHOL productionContext
          (.extCall function configuration configurationLength array arrayLength) := by
    simp [compileProgRiscV, compileProgHOL, hconfigurationCongr,
      hconfigurationLengthCongr, harrayCongr, harrayLengthCongr]
  cases hcfg : compileExpExactHOLW context (expToHOL configuration) with
  | mk cfgVals cfgShape =>
    cases hcfgLen : compileExpExactHOLW context (expToHOL configurationLength) with
    | mk cfgLenVals cfgLenShape =>
      cases harr : compileExpExactHOLW context (expToHOL array) with
      | mk arrVals arrShape =>
        cases harrLen : compileExpExactHOLW context (expToHOL arrayLength) with
        | mk arrLenVals arrLenShape =>
          cases hcfgProd : compileExpHOL context.toProduction configuration with
          | mk cfgProdVals cfgProdShape =>
            cases hcfgLenProd : compileExpHOL context.toProduction
                configurationLength with
            | mk cfgLenProdVals cfgLenProdShape =>
              cases harrProd : compileExpHOL context.toProduction array with
              | mk arrProdVals arrProdShape =>
                cases harrLenProd : compileExpHOL context.toProduction
                    arrayLength with
                | mk arrLenProdVals arrLenProdShape =>
                  have hcfgCodec := hbaseConfiguration'
                  rw [hcfg, hcfgProd] at hcfgCodec
                  rcases Prod.mk.inj hcfgCodec with ⟨hcfgVals, hcfgShape⟩
                  have hcfgLenCodec := hbaseConfigurationLength'
                  rw [hcfgLen, hcfgLenProd] at hcfgLenCodec
                  rcases Prod.mk.inj hcfgLenCodec with ⟨hcfgLenVals, hcfgLenShape⟩
                  have harrCodec := hbaseArray'
                  rw [harr, harrProd] at harrCodec
                  rcases Prod.mk.inj harrCodec with ⟨harrVals, harrShape⟩
                  have harrLenCodec := hbaseArrayLength'
                  rw [harrLen, harrLenProd] at harrLenCodec
                  rcases Prod.mk.inj harrLenCodec with ⟨harrLenVals, harrLenShape⟩
                  by_cases hgood : cfgShape = .one ∧ cfgLenShape = .one ∧
                      arrShape = .one ∧ arrLenShape = .one ∧
                      cfgVals ≠ [] ∧ cfgLenVals ≠ [] ∧ arrVals ≠ [] ∧ arrLenVals ≠ []
                  · rcases hgood with ⟨rfl, rfl, rfl, rfl,
                      hcfgNonempty, hcfgLenNonempty, harrNonempty, harrLenNonempty⟩
                    rcases cfgVals with _ | ⟨cfgHead, cfgTail⟩
                    · contradiction
                    rcases cfgLenVals with _ | ⟨cfgLenHead, cfgLenTail⟩
                    · contradiction
                    rcases arrVals with _ | ⟨arrHead, arrTail⟩
                    · contradiction
                    rcases arrLenVals with _ | ⟨arrLenHead, arrLenTail⟩
                    · contradiction
                    have hcfgProdShape : cfgProdShape = .one := by
                      simpa [Flapjack.Pancake.PanLang.shapeOfHOL] using hcfgShape.symm
                    have hcfgLenProdShape : cfgLenProdShape = .one := by
                      simpa [Flapjack.Pancake.PanLang.shapeOfHOL] using hcfgLenShape.symm
                    have harrProdShape : arrProdShape = .one := by
                      simpa [Flapjack.Pancake.PanLang.shapeOfHOL] using harrShape.symm
                    have harrLenProdShape : arrLenProdShape = .one := by
                      simpa [Flapjack.Pancake.PanLang.shapeOfHOL] using harrLenShape.symm
                    have hcfgValues :
                        List.map crepExpOfHOL (cfgHead :: cfgTail) = cfgProdVals := by
                      simpa using hcfgVals
                    have hcfgLenValues :
                        List.map crepExpOfHOL (cfgLenHead :: cfgLenTail) = cfgLenProdVals := by
                      simpa using hcfgLenVals
                    have harrValues :
                        List.map crepExpOfHOL (arrHead :: arrTail) = arrProdVals := by
                      simpa using harrVals
                    have harrLenValues :
                        List.map crepExpOfHOL (arrLenHead :: arrLenTail) = arrLenProdVals := by
                      simpa using harrLenVals
                    simp only [List.map_cons] at hcfgValues hcfgLenValues harrValues harrLenValues
                    have hcfgProdOut : compileExpHOL context.toProduction configuration =
                        (crepExpOfHOL cfgHead :: List.map crepExpOfHOL cfgTail, .one) := by
                      rw [hcfgProd]
                      exact Prod.ext hcfgValues.symm hcfgProdShape
                    have hcfgLenProdOut :
                        compileExpHOL context.toProduction configurationLength =
                          (crepExpOfHOL cfgLenHead :: List.map crepExpOfHOL cfgLenTail, .one) := by
                      rw [hcfgLenProd]
                      exact Prod.ext hcfgLenValues.symm hcfgLenProdShape
                    have harrProdOut : compileExpHOL context.toProduction array =
                        (crepExpOfHOL arrHead :: List.map crepExpOfHOL arrTail, .one) := by
                      rw [harrProd]
                      exact Prod.ext harrValues.symm harrProdShape
                    have harrLenProdOut : compileExpHOL context.toProduction arrayLength =
                        (crepExpOfHOL arrLenHead :: List.map crepExpOfHOL arrLenTail, .one) := by
                      rw [harrLenProd]
                      exact Prod.ext harrLenValues.symm harrLenProdShape
                    have hbridge := compileProgExactHOLW_extCall_success_bridge
                      context function configuration configurationLength array arrayLength hfunction
                      cfgHead cfgTail cfgLenHead cfgLenTail arrHead arrTail
                      arrLenHead arrLenTail
                      (crepExpOfHOL cfgHead) (List.map crepExpOfHOL cfgTail)
                      (crepExpOfHOL cfgLenHead) (List.map crepExpOfHOL cfgLenTail)
                      (crepExpOfHOL arrHead) (List.map crepExpOfHOL arrTail)
                      (crepExpOfHOL arrLenHead) (List.map crepExpOfHOL arrLenTail)
                      hcfg hcfgLen harr harrLen
                      hcfgProdOut hcfgLenProdOut harrProdOut harrLenProdOut
                      rfl rfl rfl rfl
                    have hbridge' := hbridge.trans (by
                      simpa [compileProgRiscV] using hbaseToProduction)
                    simpa [compileProgRiscV] using hbridge'
                  · have hguard : cfgShape ≠ .one ∨ cfgLenShape ≠ .one ∨
                        arrShape ≠ .one ∨ arrLenShape ≠ .one ∨
                        cfgVals = [] ∨ cfgLenVals = [] ∨ arrVals = [] ∨ arrLenVals = [] := by
                      by_cases hbad : cfgShape ≠ .one ∨ cfgLenShape ≠ .one ∨
                          arrShape ≠ .one ∨ arrLenShape ≠ .one ∨
                          cfgVals = [] ∨ cfgLenVals = [] ∨ arrVals = [] ∨ arrLenVals = []
                      · exact hbad
                      · simp_all
                    have hbridge := compileProgExactHOLW_extCall_skip_bridge
                      context function configuration configurationLength array arrayLength
                      cfgVals cfgShape cfgLenVals cfgLenShape arrVals arrShape
                      arrLenVals arrLenShape cfgProdVals cfgProdShape cfgLenProdVals
                      cfgLenProdShape arrProdVals arrProdShape arrLenProdVals arrLenProdShape
                      hcfg hcfgLen harr harrLen
                      hcfgProd hcfgLenProd harrProd harrLenProd
                      hcfgShape.symm hcfgLenShape.symm harrShape.symm harrLenShape.symm
                      hcfgVals.symm hcfgLenVals.symm harrVals.symm harrLenVals.symm hguard
                    have hbridge' := hbridge.trans (by
                      simpa [compileProgRiscV] using hbaseToProduction)
                    simpa [compileProgRiscV] using hbridge'
/-- Source-reviewed HOL tail-call clause (`pan_to_crepScript.sml:221-225`), the
    `rtyp = NONE` arm of `Call`. HOL compiles every argument, flattens the
    resulting expression lists, and emits a `Call NONE` with no return metadata.
    The exact clause is `compileCallNoReturnExactHOLW`; the production compiler
    emits the same tail call over `compileArgsHOL`, so the two sides agree once
    the argument lists and the (name-ranged) function identifier are decoded. -/
theorem compileProgExactHOLW_call_none_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (function : String)
    (arguments : List (Exp (BitVec width)))
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hcodec : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression) :
    crepProgOfHOL (compileProgExactHOLW context
        (.call none (Flapjack.Basis.Pure.MlString.ofString function)
          (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction (.call none function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  simp only [compileProgExactHOLW, compileCallNoReturnExactHOLW, compileProgRiscV,
    compileProgHOL, crepProgOfHOL]
  rw [hargs, hfunctionDecode]

/-- Source-reviewed HOL Call clause with an assigned result but no handler
    (`pan_to_crepScript.sml:226-232`), the `rtyp = SOME (NONE, NONE)` arm. HOL
    looks up the callee's return shape, allocates result names above `vmax`,
    zero-initializes those names, and emits a call carrying the result metadata.
    The exact clause is `compileCallResultNoHandlerExactHOLW`; the production
    compiler emits the same structure over `functionReturnNamesHOL`. The bridge
    decodes the name-ranged function identifier and relates the exact
    `context.funcs` return shape to the production `functionReturnNamesHOL`
    through `sizeOfShapeHOL_shapeToHOL`. -/
theorem compileProgExactHOLW_call_result_no_handler_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (function : String)
    (arguments : List (Exp (BitVec width)))
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hcodec : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression) :
    crepProgOfHOL (compileProgExactHOLW context
        (.call (some (none, none)) (Flapjack.Basis.Pure.MlString.ofString function)
          (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call (some (none, none)) function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  have hfuncsLookup : context.toProduction.funcs function =
      (context.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString function)).map
        (fun entry =>
          (entry.1.map (fun param =>
              (Flapjack.Basis.Pure.MlString.toStringOfBytes param.1,
                Flapjack.Pancake.PanLang.shapeOfHOL param.2)),
            Flapjack.Pancake.PanLang.shapeOfHOL entry.2)) := by
    simpa only [hfunctionDecode] using
      PanToCrepContextExact.toProduction_funcs_lookup context
        (Flapjack.Basis.Pure.MlString.ofString function)
  have hreturnNames :
      (match Option.map Prod.snd
          (context.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString function)) with
        | none => []
        | some shape => (List.range (sizeOfShapeHOL shape)).map
            (fun index => context.vmax + index + 1)) =
        functionReturnNamesHOL context.toProduction function := by
    unfold functionReturnNamesHOL
    unfold FLOOKUP
    rw [hfuncsLookup]
    cases hfuncs : context.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString function) with
    | none => rfl
    | some entry =>
        obtain ⟨params, resultShape⟩ := entry
        simp only [Option.map_some]
        have hsize : sizeOfShapeHOL resultShape = Shape.shapeSize (shapeOfHOL resultShape) := by
          have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL resultShape)
          simpa only [shapeToHOL_shapeOfHOL] using h
        unfold allocatedNamesHOL
        rw [hsize]
        apply List.map_congr_left
        intro index _hin
        change context.vmax + index + 1 = context.vmax + 1 + index
        omega
  simp only [compileProgExactHOLW, compileCallResultNoHandlerExactHOLW,
    compileProgRiscV, compileProgHOL]
  rw [crepProgOfHOL_nestedDecsHOL]
  conv => rhs; rw [← hreturnNames]
  simp only [List.map_replicate, crepExpOfHOL, List.map_const']
  simp only [crepProgOfHOL]
  rw [hargs, hfunctionDecode]
  rfl

/-- Encoding an option of `(ShapeHOL, List Nat)` through `shapeOfHOL` preserves
    the `wrap_rt` normalization: `wrapRtHOL` drops `some (.one, [])` while
    `wrapRt` drops `some (Shape.one, [])`, and `shapeOfHOL` maps `.one` to
    `Shape.one` and preserves every other shape. Hence the destination-name
    projection of the production `wrapRt` on the encoded map equals that of the
    exact `wrapRtHOL`. Flapjack proof infrastructure. -/
private theorem wrapRt_map_shapeOfHOL_snd (n : Option (ShapeHOL × List Nat)) :
    (wrapRt (n.map (fun pair =>
      (Flapjack.Pancake.PanLang.shapeOfHOL pair.1, pair.2)))).map Prod.snd =
      (wrapRtHOL n).map Prod.snd := by
  cases n with
  | none => rfl
  | some pair =>
      obtain ⟨shape, names⟩ := pair
      cases shape <;> cases names <;>
        simp [wrapRt, wrapRtHOL, Flapjack.Pancake.PanLang.shapeOfHOL]

/-- Exact-to-production bridge for the `rtyp = SOME (SOME (rtk, rt), NONE)`
    Call arm of HOL `compile_def` (`cakeml/pancake/pan_to_crepScript.sml:252-261`):
    the successful `wrap_rt (FLOOKUP ctxt.vars rt)` branch with no exception
    handler. Both compilers emit a call carrying the destination names as result
    metadata, so the proof only has to move `crepProgOfHOL` through the compiled
    argument list, decode the function name, and reconcile the exact
    `wrapRtHOL` lookup with the production `callDestinationNamesHOL`. Flapjack
    proof infrastructure; no HOL-tagged declaration. -/
theorem compileProgExactHOLW_call_wrapped_result_no_handler_bridge
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width)
    (kind : VarKind) (resultName function : String)
    (arguments : List (Exp (BitVec width)))
    (resultShape : Flapjack.Pancake.PanLang.ShapeHOL) (resultNames : List Nat)
    (hwrappedResult :
      wrapRtHOL (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)) =
        some (resultShape, resultNames))
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hcodec :
      ∀ expression ∈ arguments,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
          compileExpHOL context.toProduction expression) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.call (some (some (kind, Flapjack.Basis.Pure.MlString.ofString resultName), none))
            (Flapjack.Basis.Pure.MlString.ofString function) (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call (some (some (kind, resultName), none)) function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  have hvariables : context.toProduction.vars resultName =
      (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)).map
        (fun entry =>
          (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := rfl
  have hproductionNames :
      callDestinationNamesHOL context.toProduction kind resultName = some resultNames := by
    unfold callDestinationNamesHOL FLOOKUP
    rw [hvariables, wrapRt_map_shapeOfHOL_snd, hwrappedResult]
    rfl
  simp only [compileProgExactHOLW]
  split
  · simp_all
  · simp_all only [compileCallWrappedResultNoHandlerExactHOLW, compileProgRiscV, compileProgHOL,
      crepProgOfHOL, Option.some.injEq, Prod.mk.injEq]

/-- Exact-to-production bridge for the `rtyp = SOME (SOME (rtk, rt), NONE)` Call
    arm of HOL `compile_def` (`cakeml/pancake/pan_to_crepScript.sml:252-261`) with
    a failed `wrap_rt (FLOOKUP ctxt.vars rt)` lookup and no handler: both
    compilers emit a flattened tail call with no return metadata. Flapjack proof
    infrastructure; no HOL-tagged declaration. -/
theorem compileProgExactHOLW_call_wrapped_result_fallback_no_handler_bridge
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width)
    (kind : VarKind) (resultName function : String)
    (arguments : List (Exp (BitVec width)))
    (hwrappedResult :
      wrapRtHOL (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)) =
        none)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hcodec :
      ∀ expression ∈ arguments,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
          compileExpHOL context.toProduction expression) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.call (some (some (kind, Flapjack.Basis.Pure.MlString.ofString resultName), none))
            (Flapjack.Basis.Pure.MlString.ofString function) (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call (some (some (kind, resultName), none)) function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  have hvariables : context.toProduction.vars resultName =
      (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)).map
        (fun entry =>
          (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := rfl
  have hproductionNames :
      callDestinationNamesHOL context.toProduction kind resultName = none := by
    unfold callDestinationNamesHOL FLOOKUP
    rw [hvariables, wrapRt_map_shapeOfHOL_snd, hwrappedResult]
    rfl
  simp only [compileProgExactHOLW]
  split
  · simp_all only [compileCallWrappedResultFallbackNoHandlerExactHOLW, compileProgRiscV,
      compileProgHOL, crepProgOfHOL]
    rfl
  · simp_all

/-- Exact-to-production bridge for the `SOME (NONE, SOME handler)` Call arm of
    HOL `compile_def` (`cakeml/pancake/pan_to_crepScript.sml:233-235`) with a
    handler whose `eids` lookup fails: HOL discards the handler and emits the
    zero-initialized result call, exactly as the handler-less result arm. The
    proof follows the result/no-handler bridge and additionally reconciles the
    exact `eids.lookup` with the production `eids` finite map. Flapjack proof
    infrastructure; no HOL-tagged declaration. -/
theorem compileProgExactHOLW_call_handler_missing_eid_bridge
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width)
    (function exceptionName exceptionVariable : String)
    (arguments : List (Exp (BitVec width))) (body : ProgHOL width)
    (hmissing :
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) =
        none)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hexceptionName : Flapjack.Pancake.PanLang.NameRanged exceptionName)
    (hcodec :
      ∀ expression ∈ arguments,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
          compileExpHOL context.toProduction expression) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.call
            (some (none,
              some (Flapjack.Basis.Pure.MlString.ofString exceptionName,
                Flapjack.Basis.Pure.MlString.ofString exceptionVariable, body)))
            (Flapjack.Basis.Pure.MlString.ofString function) (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call (some (none, some (exceptionName, exceptionVariable, progOfHOL body)))
          function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  have hprodEids : context.toProduction.eids exceptionName =
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) := by
    have h := PanToCrepContextExact.toProduction_eids_lookup context
      (Flapjack.Basis.Pure.MlString.ofString exceptionName)
    rwa [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes exceptionName
      hexceptionName] at h
  have hproductionEid :
      FLOOKUP context.toProduction.eids exceptionName = none := by
    rw [FLOOKUP, hprodEids, hmissing]
  have hfuncsLookup : context.toProduction.funcs function =
      (context.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString function)).map
        (fun entry =>
          (entry.1.map (fun param =>
              (Flapjack.Basis.Pure.MlString.toStringOfBytes param.1,
                Flapjack.Pancake.PanLang.shapeOfHOL param.2)),
            Flapjack.Pancake.PanLang.shapeOfHOL entry.2)) := by
    simpa only [hfunctionDecode] using
      PanToCrepContextExact.toProduction_funcs_lookup context
        (Flapjack.Basis.Pure.MlString.ofString function)
  have hreturnNames :
      (match Option.map Prod.snd
          (context.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString function)) with
        | none => []
        | some shape =>
            (List.range (sizeOfShapeHOL shape)).map
              (fun index => context.vmax + index + 1)) =
        functionReturnNamesHOL context.toProduction function := by
    unfold functionReturnNamesHOL
    unfold FLOOKUP
    rw [hfuncsLookup]
    cases hfuncs :
        context.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString function) with
    | none => rfl
    | some entry =>
        obtain ⟨params, resultShape⟩ := entry
        simp only [Option.map_some]
        have hsize : sizeOfShapeHOL resultShape = Shape.shapeSize (shapeOfHOL resultShape) := by
          have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL resultShape)
          simpa only [shapeToHOL_shapeOfHOL] using h
        unfold allocatedNamesHOL
        rw [hsize]
        apply List.map_congr_left
        intro index _hin
        change context.vmax + index + 1 = context.vmax + 1 + index
        omega
  simp only [compileProgExactHOLW]
  split
  · simp only [compileCallHandlerMissingEidExactHOLW, compileCallResultNoHandlerExactHOLW,
      compileProgRiscV, compileProgHOL, hproductionEid]
    rw [crepProgOfHOL_nestedDecsHOL]
    conv => rhs; rw [← hreturnNames]
    simp only [List.map_replicate, crepExpOfHOL, List.map_const', crepProgOfHOL]
    rw [hargs, hfunctionDecode]
    rfl
  · simp_all

private theorem crepProgOfHOL_loadGlobalsHOL {width : Nat} [NeZero width]
    (address : BitVec 5) (count : Nat) :
    (loadGlobalsHOL (width := width) address count).map (crepExpOfHOL (width := width)) =
      loadGlobals (α := BitVec width) address count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih =>
      simp only [loadGlobalsHOL, loadGlobals, List.map_cons, crepExpOfHOL, ih]

private theorem crepProgOfHOL_panMap2_assign {width : Nat} [NeZero width]
    (names : List Nat) (values : List (CrepExpHOL width)) :
    (panMap2 (fun destination source =>
        (CrepProgHOL.assign destination source : CrepProgHOL width)) names values).map
        crepProgOfHOL =
      panMap2 (fun destination source =>
        (CrepProg.assign destination source : CrepProg (BitVec width))) names
        (values.map crepExpOfHOL) := by
  induction names generalizing values with
  | nil => simp [panMap2]
  | cons name names ih =>
      cases values with
      | nil => simp [panMap2]
      | cons value values => simp [panMap2, crepProgOfHOL, ih]

private theorem crepProgOfHOL_expHdlExact {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (v : String) :
    crepProgOfHOL (expHdlExact (width := width) context.vars
        (Flapjack.Basis.Pure.MlString.ofString v)) =
      expHdlFiniteMap (α := BitVec width) context.toProduction.vars v := by
  have hvars : context.toProduction.vars v =
      (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString v)).map
        (fun entry =>
          (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := rfl
  unfold expHdlExact expHdlFiniteMap
  rw [FLOOKUP, hvars]
  cases hlk : context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString v) with
  | none =>
      simp only [Option.map_none, crepProgOfHOL]
  | some entry =>
      obtain ⟨shape, names⟩ := entry
      simp only [Option.map_some]
      rw [crepProgOfHOL_crepNestedSeqHOL, crepProgOfHOL_panMap2_assign,
        crepProgOfHOL_loadGlobalsHOL]

/-- Exact-to-production bridge for the `SOME (NONE, SOME handler)` Call arm of
    HOL `compile_def` (`cakeml/pancake/pan_to_crepScript.sml:233-239`) with a
    handler whose `eids` lookup succeeds: HOL keeps the handler, wrapping the recursively
    compiled body with exact `exp_hdl` and zero-initializing the callee return
    names. The setup bridge `crepProgOfHOL_expHdlExact` reconciles the exact
    `exp_hdl` with the executed production `expHdlFiniteMap`. Flapjack proof
    infrastructure; no HOL-tagged declaration. -/
theorem compileProgExactHOLW_call_handler_present_eid_bridge
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width)
    (function exceptionName exceptionVariable : String)
    (arguments : List (Exp (BitVec width))) (body : ProgHOL width)
    (exceptionCode : BitVec width)
    (hpresent :
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) =
        some exceptionCode)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hexceptionName : Flapjack.Pancake.PanLang.NameRanged exceptionName)
    (hcodec :
      ∀ expression ∈ arguments,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
          compileExpHOL context.toProduction expression)
    (hbody :
      crepProgOfHOL (compileProgExactHOLW context body) =
        compileProgHOL context.toProduction (progOfHOL body)) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.call
            (some (none,
              some (Flapjack.Basis.Pure.MlString.ofString exceptionName,
                Flapjack.Basis.Pure.MlString.ofString exceptionVariable, body)))
            (Flapjack.Basis.Pure.MlString.ofString function) (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call (some (none, some (exceptionName, exceptionVariable, progOfHOL body)))
          function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  have hsetup := crepProgOfHOL_expHdlExact context exceptionVariable
  have hprodEids : context.toProduction.eids exceptionName =
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) := by
    have h := PanToCrepContextExact.toProduction_eids_lookup context
      (Flapjack.Basis.Pure.MlString.ofString exceptionName)
    rwa [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes exceptionName
      hexceptionName] at h
  have hproductionEid :
      FLOOKUP context.toProduction.eids exceptionName = some exceptionCode := by
    rw [FLOOKUP, hprodEids, hpresent]
  have hfuncsLookup : context.toProduction.funcs function =
      (context.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString function)).map
        (fun entry =>
          (entry.1.map (fun param =>
              (Flapjack.Basis.Pure.MlString.toStringOfBytes param.1,
                Flapjack.Pancake.PanLang.shapeOfHOL param.2)),
            Flapjack.Pancake.PanLang.shapeOfHOL entry.2)) := by
    simpa only [hfunctionDecode] using
      PanToCrepContextExact.toProduction_funcs_lookup context
        (Flapjack.Basis.Pure.MlString.ofString function)
  have hreturnNames :
      (match Option.map Prod.snd
          (context.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString function)) with
        | none => []
        | some shape =>
            (List.range (sizeOfShapeHOL shape)).map
              (fun index => context.vmax + index + 1)) =
        functionReturnNamesHOL context.toProduction function := by
    unfold functionReturnNamesHOL
    unfold FLOOKUP
    rw [hfuncsLookup]
    cases hfuncs :
        context.funcs.lookup (Flapjack.Basis.Pure.MlString.ofString function) with
    | none => rfl
    | some entry =>
        obtain ⟨params, resultShape⟩ := entry
        simp only [Option.map_some]
        have hsize : sizeOfShapeHOL resultShape = Shape.shapeSize (shapeOfHOL resultShape) := by
          have h := sizeOfShapeHOL_shapeToHOL (shapeOfHOL resultShape)
          simpa only [shapeToHOL_shapeOfHOL] using h
        unfold allocatedNamesHOL
        rw [hsize]
        apply List.map_congr_left
        intro index _hin
        change context.vmax + index + 1 = context.vmax + 1 + index
        omega
  simp only [compileProgExactHOLW]
  split
  · simp_all
  · rename_i code heqLookup
    simp only [compileCallHandlerPresentEidExactHOLW, compileProgRiscV, compileProgHOL,
      hproductionEid]
    rw [crepProgOfHOL_nestedDecsHOL]
    conv => rhs; rw [← hreturnNames]
    simp only [List.map_replicate, crepExpOfHOL, List.map_const']
    simp only [crepProgOfHOL]
    rw [hargs, hfunctionDecode, hsetup, hbody]
    have hsome : some code = some exceptionCode := heqLookup.symm.trans hpresent
    injection hsome with hcodeEq
    rw [hcodeEq]
    rfl

/-- Exact-to-production bridge for the `SOME (SOME (rtk, rt), SOME handler)`
    Call arm of HOL `compile_def` (`cakeml/pancake/pan_to_crepScript.sml:252-261`)
    with a successful `wrap_rt (FLOOKUP ctxt.vars rt)` lookup and a failing
    `eids` lookup: HOL drops the handler but keeps the destination names as
    result metadata, reducing to the wrapped-result no-handler arm. Flapjack
    proof infrastructure; no HOL-tagged declaration. -/
theorem compileProgExactHOLW_call_wrapped_result_handler_missing_eid_bridge
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width)
    (kind : VarKind) (resultName function exceptionName exceptionVariable : String)
    (arguments : List (Exp (BitVec width))) (body : ProgHOL width)
    (resultShape : Flapjack.Pancake.PanLang.ShapeHOL) (resultNames : List Nat)
    (hwrappedResult :
      wrapRtHOL
          (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)) =
        some (resultShape, resultNames))
    (hmissing :
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) =
        none)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hexceptionName : Flapjack.Pancake.PanLang.NameRanged exceptionName)
    (hcodec :
      ∀ expression ∈ arguments,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
          compileExpHOL context.toProduction expression) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.call
            (some (some (kind,
                Flapjack.Basis.Pure.MlString.ofString resultName),
              some (Flapjack.Basis.Pure.MlString.ofString exceptionName,
                Flapjack.Basis.Pure.MlString.ofString exceptionVariable, body)))
            (Flapjack.Basis.Pure.MlString.ofString function) (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call
          (some (some (kind, resultName),
            some (exceptionName, exceptionVariable, progOfHOL body)))
          function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  have hvariables : context.toProduction.vars resultName =
      (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)).map
        (fun entry =>
          (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := rfl
  have hproductionNames :
      callDestinationNamesHOL context.toProduction kind resultName = some resultNames := by
    unfold callDestinationNamesHOL FLOOKUP
    rw [hvariables, wrapRt_map_shapeOfHOL_snd, hwrappedResult]
    rfl
  have hprodEids : context.toProduction.eids exceptionName =
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) := by
    have h := PanToCrepContextExact.toProduction_eids_lookup context
      (Flapjack.Basis.Pure.MlString.ofString exceptionName)
    rwa [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes exceptionName
      hexceptionName] at h
  have hproductionEid : FLOOKUP context.toProduction.eids exceptionName = none := by
    rw [FLOOKUP, hprodEids, hmissing]
  simp only [compileProgExactHOLW]
  split
  · simp_all
  · split
    · simp_all only [compileCallWrappedResultHandlerMissingEidExactHOLW,
        compileCallWrappedResultNoHandlerExactHOLW, compileProgRiscV, compileProgHOL,
        crepProgOfHOL, Option.some.injEq, Prod.mk.injEq]
    · simp_all

/-- Exact-to-production bridge for the `SOME (SOME (rtk, rt), SOME handler)`
    Call arm of HOL `compile_def` (`cakeml/pancake/pan_to_crepScript.sml:252-261`)
    with a successful `wrap_rt (FLOOKUP ctxt.vars rt)` lookup and a successful
    `eids` lookup: HOL keeps the destination names as result metadata and
    sequences exact `exp_hdl` with the recursively compiled handler body, without
    return-slot declarations. Flapjack proof infrastructure; no HOL-tagged
    declaration. -/
theorem compileProgExactHOLW_call_wrapped_result_handler_present_eid_bridge
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width)
    (kind : VarKind) (resultName function exceptionName exceptionVariable : String)
    (arguments : List (Exp (BitVec width))) (body : ProgHOL width)
    (resultShape : Flapjack.Pancake.PanLang.ShapeHOL) (resultNames : List Nat)
    (exceptionCode : BitVec width)
    (hwrappedResult :
      wrapRtHOL
          (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)) =
        some (resultShape, resultNames))
    (hpresent :
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) =
        some exceptionCode)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hexceptionName : Flapjack.Pancake.PanLang.NameRanged exceptionName)
    (hcodec :
      ∀ expression ∈ arguments,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
          compileExpHOL context.toProduction expression)
    (hbody :
      crepProgOfHOL (compileProgExactHOLW context body) =
        compileProgHOL context.toProduction (progOfHOL body)) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.call
            (some (some (kind,
                Flapjack.Basis.Pure.MlString.ofString resultName),
              some (Flapjack.Basis.Pure.MlString.ofString exceptionName,
                Flapjack.Basis.Pure.MlString.ofString exceptionVariable, body)))
            (Flapjack.Basis.Pure.MlString.ofString function) (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call
          (some (some (kind, resultName),
            some (exceptionName, exceptionVariable, progOfHOL body)))
          function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  have hsetup := crepProgOfHOL_expHdlExact context exceptionVariable
  have hvariables : context.toProduction.vars resultName =
      (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)).map
        (fun entry =>
          (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := rfl
  have hproductionNames :
      callDestinationNamesHOL context.toProduction kind resultName = some resultNames := by
    unfold callDestinationNamesHOL FLOOKUP
    rw [hvariables, wrapRt_map_shapeOfHOL_snd, hwrappedResult]
    rfl
  have hprodEids : context.toProduction.eids exceptionName =
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) := by
    have h := PanToCrepContextExact.toProduction_eids_lookup context
      (Flapjack.Basis.Pure.MlString.ofString exceptionName)
    rwa [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes exceptionName
      hexceptionName] at h
  have hproductionEid :
      FLOOKUP context.toProduction.eids exceptionName = some exceptionCode := by
    rw [FLOOKUP, hprodEids, hpresent]
  simp only [compileProgExactHOLW]
  split
  · simp_all
  · split
    · simp_all
    · rename_i resultShape' resultNames' heqWrap code heqLookup
      simp only [compileCallWrappedResultHandlerPresentEidExactHOLW, compileProgRiscV,
        compileProgHOL, hproductionNames, hproductionEid]
      simp only [crepProgOfHOL]
      rw [hargs, hfunctionDecode, hsetup, hbody]
      have hsome : some code = some exceptionCode := heqLookup.symm.trans hpresent
      injection hsome with hcodeEq
      rw [hcodeEq]
      have hpair : resultShape' = resultShape ∧ resultNames' = resultNames := by
        have h := heqWrap.symm.trans hwrappedResult
        simpa only [Option.some.injEq, Prod.mk.injEq] using h
      rw [hpair.2]

/-- Exact-to-production bridge for the `SOME (SOME (rtk, rt), SOME handler)`
    Call arm of HOL `compile_def` (`cakeml/pancake/pan_to_crepScript.sml:252-261`)
    with a failing `wrap_rt (FLOOKUP ctxt.vars rt)` lookup and a failing `eids`
    lookup: HOL drops both handler and return metadata and emits a flattened tail
    call, reducing to the wrapped-result fallback no-handler arm. Flapjack proof
    infrastructure; no HOL-tagged declaration. -/
theorem compileProgExactHOLW_call_wrapped_result_fallback_handler_missing_eid_bridge
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width)
    (kind : VarKind) (resultName function exceptionName exceptionVariable : String)
    (arguments : List (Exp (BitVec width))) (body : ProgHOL width)
    (hwrappedResult :
      wrapRtHOL
          (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)) =
        none)
    (hmissing :
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) =
        none)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hexceptionName : Flapjack.Pancake.PanLang.NameRanged exceptionName)
    (hcodec :
      ∀ expression ∈ arguments,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
          compileExpHOL context.toProduction expression) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.call
            (some (some (kind,
                Flapjack.Basis.Pure.MlString.ofString resultName),
              some (Flapjack.Basis.Pure.MlString.ofString exceptionName,
                Flapjack.Basis.Pure.MlString.ofString exceptionVariable, body)))
            (Flapjack.Basis.Pure.MlString.ofString function) (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call
          (some (some (kind, resultName),
            some (exceptionName, exceptionVariable, progOfHOL body)))
          function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  have hvariables : context.toProduction.vars resultName =
      (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)).map
        (fun entry =>
          (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := rfl
  have hproductionNames :
      callDestinationNamesHOL context.toProduction kind resultName = none := by
    unfold callDestinationNamesHOL FLOOKUP
    rw [hvariables, wrapRt_map_shapeOfHOL_snd, hwrappedResult]
    rfl
  have hprodEids : context.toProduction.eids exceptionName =
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) := by
    have h := PanToCrepContextExact.toProduction_eids_lookup context
      (Flapjack.Basis.Pure.MlString.ofString exceptionName)
    rwa [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes exceptionName
      hexceptionName] at h
  have hproductionEid : FLOOKUP context.toProduction.eids exceptionName = none := by
    rw [FLOOKUP, hprodEids, hmissing]
  simp only [compileProgExactHOLW]
  split
  · split
    · simp_all only [compileCallWrappedResultFallbackHandlerMissingEidExactHOLW,
        compileCallWrappedResultFallbackNoHandlerExactHOLW, compileProgRiscV,
        compileProgHOL, crepProgOfHOL]
      simp only [Option.elim_none]
    · simp_all
  · simp_all

/-- Exact-to-production bridge for the `SOME (SOME (rtk, rt), SOME handler)`
    Call arm of HOL `compile_def` (`cakeml/pancake/pan_to_crepScript.sml:252-261`)
    with a failing `wrap_rt (FLOOKUP ctxt.vars rt)` lookup and a successful `eids`
    lookup: HOL keeps the handler but supplies an empty return-name list, emitting
    `.call (some ([], some (code, handler)))`. Flapjack proof infrastructure; no
    HOL-tagged declaration. -/
theorem compileProgExactHOLW_call_wrapped_result_fallback_handler_present_eid_bridge
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width)
    (kind : VarKind) (resultName function exceptionName exceptionVariable : String)
    (arguments : List (Exp (BitVec width))) (body : ProgHOL width)
    (exceptionCode : BitVec width)
    (hwrappedResult :
      wrapRtHOL
          (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)) =
        none)
    (hpresent :
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) =
        some exceptionCode)
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hexceptionName : Flapjack.Pancake.PanLang.NameRanged exceptionName)
    (hcodec :
      ∀ expression ∈ arguments,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
          compileExpHOL context.toProduction expression)
    (hbody :
      crepProgOfHOL (compileProgExactHOLW context body) =
        compileProgHOL context.toProduction (progOfHOL body)) :
    crepProgOfHOL
        (compileProgExactHOLW context
          (.call
            (some (some (kind,
                Flapjack.Basis.Pure.MlString.ofString resultName),
              some (Flapjack.Basis.Pure.MlString.ofString exceptionName,
                Flapjack.Basis.Pure.MlString.ofString exceptionVariable, body)))
            (Flapjack.Basis.Pure.MlString.ofString function) (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call
          (some (some (kind, resultName),
            some (exceptionName, exceptionVariable, progOfHOL body)))
          function arguments) := by
  have hfunctionDecode :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction
  have hargs := crepProgOfHOL_compileArgumentList_flatMap context arguments hcodec
  have hsetup := crepProgOfHOL_expHdlExact context exceptionVariable
  have hvariables : context.toProduction.vars resultName =
      (context.vars.lookup (Flapjack.Basis.Pure.MlString.ofString resultName)).map
        (fun entry =>
          (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := rfl
  have hproductionNames :
      callDestinationNamesHOL context.toProduction kind resultName = none := by
    unfold callDestinationNamesHOL FLOOKUP
    rw [hvariables, wrapRt_map_shapeOfHOL_snd, hwrappedResult]
    rfl
  have hprodEids : context.toProduction.eids exceptionName =
      context.eids.lookup (Flapjack.Basis.Pure.MlString.ofString exceptionName) := by
    have h := PanToCrepContextExact.toProduction_eids_lookup context
      (Flapjack.Basis.Pure.MlString.ofString exceptionName)
    rwa [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes exceptionName
      hexceptionName] at h
  have hproductionEid :
      FLOOKUP context.toProduction.eids exceptionName = some exceptionCode := by
    rw [FLOOKUP, hprodEids, hpresent]
  simp only [compileProgExactHOLW]
  split
  · split
    · simp_all
    · rename_i code heqLookup
      unfold compileCallWrappedResultFallbackHandlerPresentEidExactHOLW
      simp only [compileProgRiscV, compileProgHOL, hproductionNames, hproductionEid,
        crepProgOfHOL]
      rw [hargs, hfunctionDecode, hsetup, hbody]
      have hsome : some code = some exceptionCode := heqLookup.symm.trans hpresent
      injection hsome with hcodeEq
      rw [hcodeEq]
      rfl
  · simp_all

/-- Decode an exact `ProgHOL` `Call` metadata record (faithful `MlString`
identifiers, exact `ProgHOL` handler body) into the production
`Option (Option ...)` form consumed by `compileProgHOL`. -/
def callInfoToProduction {width : Nat} [NeZero width]
    (info : Option (Option (VarKind × Flapjack.Basis.Pure.MlString.MlString) ×
      Option (Flapjack.Basis.Pure.MlString.MlString ×
        Flapjack.Basis.Pure.MlString.MlString × ProgHOL width))) :
    Option (Option (VarKind × String) ×
      Option (String × String × Prog (BitVec width))) :=
  info.map fun entry =>
    (entry.1.map fun destination =>
        (destination.1, Flapjack.Basis.Pure.MlString.toStringOfBytes destination.2),
     entry.2.map fun handler =>
        (Flapjack.Basis.Pure.MlString.toStringOfBytes handler.1,
         Flapjack.Basis.Pure.MlString.toStringOfBytes handler.2.1,
         progOfHOL handler.2.2))

/-- The (at most one) exception-handler body carried by an exact `Call`
metadata record, if any.  Used to state the assembled `Call` bridge with a
premise about only the handler program actually present in `info`, rather
than a universally quantified body premise. -/
def callHandlerBody {width : Nat} [NeZero width]
    (info : Option (Option (VarKind × Flapjack.Basis.Pure.MlString.MlString) ×
      Option (Flapjack.Basis.Pure.MlString.MlString ×
        Flapjack.Basis.Pure.MlString.MlString × ProgHOL width))) :
    Option (ProgHOL width) :=
  match info with
  | none => none
  | some entry =>
      match entry.2 with
      | none => none
      | some handler => some handler.2.2

/-- The `toStringOfBytes` image of an `MlString` is `NameRanged`: decoding bytes
to characters yields codes below 256. -/
theorem nameRanged_toStringOfBytes
    (m : Flapjack.Basis.Pure.MlString.MlString) :
    Flapjack.Pancake.PanLang.NameRanged
      (Flapjack.Basis.Pure.MlString.toStringOfBytes m) := by
  intro character hmem
  simp only [Flapjack.Basis.Pure.MlString.toStringOfBytes, String.toList_ofList,
    List.mem_map] at hmem
  obtain ⟨byte, _hbyte, rfl⟩ := hmem
  have hb : byte.toNat < 256 := by simpa using byte.isLt
  rw [Flapjack.Basis.Pure.MlString.ofNat_toNat_char byte]
  exact hb

/-- Relation-polymorphic local Assign case. The existing exact-context bridge
    handles the local overlap/temporary branches; expression-codec congruence,
    ranged destination lookup, and equal `vmax` transport it to any related
    production context. -/
theorem compileProgExactHOLW_local_assign_relation_bridge
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (name : MlS) (expression : ExpHOL width) :
    crepProgOfHOL
        (compileProgExactHOLW context (.assign .local name expression)) =
      compileProgHOL productionContext
        (.assign .local
          (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
          (expOfHOL expression)) := by
  have hbaseRel : PanToCrepContextExactProdRel context context.toProduction := by
    exact panToCrepContextExactProdRel_refl context
  have hprodCodec := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext expression
  have hbaseCodec := compileExpExactHOLW_prodCodec_of_contextRel
    context context.toProduction hbaseRel expression
  have hcompiledContextEq :
      compileExpHOL productionContext (expOfHOL expression) =
        compileExpHOL context.toProduction (expOfHOL expression) := by
    exact hprodCodec.symm.trans hbaseCodec
  have hvarsProd :
      productionContext.vars
          (Flapjack.Basis.Pure.MlString.toStringOfBytes name) =
        (context.vars.lookup name).map
          (fun entry => (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := by
    have hrel := hcontext.2.2.2
      (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
      (nameRanged_toStringOfBytes name)
    rw [PanToCrepContextExact.toProduction_vars_lookup] at hrel
    exact hrel.symm
  have hvarsContexts :
      productionContext.vars
          (Flapjack.Basis.Pure.MlString.toStringOfBytes name) =
        context.toProduction.vars
          (Flapjack.Basis.Pure.MlString.toStringOfBytes name) := by
    rw [hvarsProd, PanToCrepContextExact.toProduction_vars_lookup]
  have hvmax : context.vmax = productionContext.vmax := by
    simpa [PanToCrepContextExact.toProduction] using hcontext.2.2.1
  have hproductionCongr :
      compileProgHOL productionContext
          (.assign .local
            (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
            (expOfHOL expression)) =
        compileProgHOL context.toProduction
          (.assign .local
            (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
            (expOfHOL expression)) := by
    simp [compileProgHOL, FLOOKUP, freshNamesHOL,
      PanToCrepContextExact.toProduction, hcompiledContextEq, hvarsContexts, hvmax]
  have hbaseCodec' :
      ((compileExpExactHOLW context
          (Flapjack.Pancake.PanLang.expToHOL (expOfHOL expression))).1.map
          crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context
          (Flapjack.Pancake.PanLang.expToHOL (expOfHOL expression))).2) =
        compileExpHOL context.toProduction (expOfHOL expression) := by
    simpa using hbaseCodec
  have hbaseBridge := compileProgExactHOLW_local_assign_bridge context
    (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
    (expOfHOL expression) hbaseCodec'
  have hbridge := hbaseBridge.trans
    (by simpa [compileProgRiscV] using hproductionCongr.symm)
  simpa only [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes,
    Flapjack.Pancake.PanLang.expToHOL_expOfHOL] using hbridge

/-- Relation-polymorphic Raise case. The related exception lookup, expression
    codec, and `vmax` equality preserve the missing-id, shape-mismatch, and
    successful temporary/store branches of the exact-context bridge. -/
theorem compileProgExactHOLW_raise_relation_bridge
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (exception : MlS) (expression : ExpHOL width) :
    crepProgOfHOL
        (compileProgExactHOLW context (.raise exception expression)) =
      compileProgHOL productionContext
        (.raise (Flapjack.Basis.Pure.MlString.toStringOfBytes exception)
          (expOfHOL expression)) := by
  have hbaseRel : PanToCrepContextExactProdRel context context.toProduction := by
    exact panToCrepContextExactProdRel_refl context
  have hprodCodec := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext expression
  have hbaseCodec := compileExpExactHOLW_prodCodec_of_contextRel
    context context.toProduction hbaseRel expression
  have hcompiledContextEq :
      compileExpHOL productionContext (expOfHOL expression) =
        compileExpHOL context.toProduction (expOfHOL expression) := by
    exact hprodCodec.symm.trans hbaseCodec
  have hexceptionLookup :
      productionContext.eids
          (Flapjack.Basis.Pure.MlString.toStringOfBytes exception) =
        context.eids.lookup exception := by
    calc
      productionContext.eids
          (Flapjack.Basis.Pure.MlString.toStringOfBytes exception) =
          context.toProduction.eids
            (Flapjack.Basis.Pure.MlString.toStringOfBytes exception) :=
        (hcontext.2.1
          (Flapjack.Basis.Pure.MlString.toStringOfBytes exception)
          (nameRanged_toStringOfBytes exception)).symm
      _ = context.eids.lookup exception :=
        PanToCrepContextExact.toProduction_eids_lookup context exception
  have hvmax : context.vmax = productionContext.vmax := by
    simpa [PanToCrepContextExact.toProduction] using hcontext.2.2.1
  have hproductionCongr :
      compileProgHOL productionContext
          (.raise (Flapjack.Basis.Pure.MlString.toStringOfBytes exception)
            (expOfHOL expression)) =
        compileProgHOL context.toProduction
          (.raise (Flapjack.Basis.Pure.MlString.toStringOfBytes exception)
            (expOfHOL expression)) := by
    simp [compileProgHOL, FLOOKUP, freshNamesHOL,
      PanToCrepContextExact.toProduction, hcompiledContextEq,
      hexceptionLookup, hvmax,
      Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
  have hbaseCodec' :
      ((compileExpExactHOLW context
          (Flapjack.Pancake.PanLang.expToHOL (expOfHOL expression))).1.map
          crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context
          (Flapjack.Pancake.PanLang.expToHOL (expOfHOL expression))).2) =
        compileExpHOL context.toProduction (expOfHOL expression) := by
    simpa using hbaseCodec
  have hbaseBridge := compileProgExactHOLW_raise_bridge context
    (Flapjack.Basis.Pure.MlString.toStringOfBytes exception)
    (expOfHOL expression) hbaseCodec'
  have hbridge := hbaseBridge.trans
    (by simpa [compileProgRiscV] using hproductionCongr.symm)
  simpa only [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes,
    Flapjack.Pancake.PanLang.expToHOL_expOfHOL] using hbridge

/-- Relation-polymorphic Primitive case. The exact-context case theorem covers
    missing destinations and temporary allocation; the ranged context
    relation supplies the destination lookup, argument-list codec, and `vmax`
    equality needed for an arbitrary related production context. -/
theorem compileProgExactHOLW_primitive_relation_bridge
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL width)) :
    crepProgOfHOL
        (compileProgExactHOLW context (.primitive name operator arguments)) =
      compileProgHOL productionContext
        (.primitive (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
          operator (arguments.map expOfHOL)) := by
  have hbaseRel : PanToCrepContextExactProdRel context context.toProduction := by
    exact panToCrepContextExactProdRel_refl context
  have hvarsProd :
      productionContext.vars
          (Flapjack.Basis.Pure.MlString.toStringOfBytes name) =
        (context.vars.lookup name).map
          (fun entry => (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := by
    have hrel := hcontext.2.2.2
      (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
      (nameRanged_toStringOfBytes name)
    rw [PanToCrepContextExact.toProduction_vars_lookup] at hrel
    exact hrel.symm
  have hvarsContexts :
      productionContext.vars
          (Flapjack.Basis.Pure.MlString.toStringOfBytes name) =
        context.toProduction.vars
          (Flapjack.Basis.Pure.MlString.toStringOfBytes name) := by
    rw [hvarsProd, PanToCrepContextExact.toProduction_vars_lookup]
  have hvmax : context.vmax = productionContext.vmax := by
    simpa [PanToCrepContextExact.toProduction] using hcontext.2.2.1
  have hcodecProd : ∀ expression ∈ arguments.map expOfHOL,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL productionContext expression := by
    intro expression hmem
    obtain ⟨sourceExpression, hmem, rfl⟩ := List.mem_map.mp hmem
    simpa using compileExpExactHOLW_prodCodec_of_contextRel
      context productionContext hcontext sourceExpression
  have hcodecBase : ∀ expression ∈ arguments.map expOfHOL,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression := by
    intro expression hmem
    obtain ⟨sourceExpression, hmem, rfl⟩ := List.mem_map.mp hmem
    simpa using compileExpExactHOLW_prodCodec_of_contextRel
      context context.toProduction hbaseRel sourceExpression
  have hflatProd := crepProgOfHOL_compileArgumentList_flatMapAt
    context productionContext (arguments.map expOfHOL) hcodecProd
  have hflatBase := crepProgOfHOL_compileArgumentList_flatMapAt
    context context.toProduction (arguments.map expOfHOL) hcodecBase
  have hargsEq :
      compileArgsHOL productionContext (arguments.map expOfHOL) =
        compileArgsHOL context.toProduction (arguments.map expOfHOL) := by
    exact hflatProd.symm.trans hflatBase
  have hproductionCongr :
      compileProgHOL productionContext
          (.primitive (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
            operator (arguments.map expOfHOL)) =
        compileProgHOL context.toProduction
          (.primitive (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
            operator (arguments.map expOfHOL)) := by
    simp [compileProgHOL, FLOOKUP, freshNamesHOL,
      PanToCrepContextExact.toProduction, hvarsContexts, hargsEq, hvmax]
  have hbaseBridge := compileProgExactHOLW_primitive_bridge context
    (Flapjack.Basis.Pure.MlString.toStringOfBytes name) operator
    (arguments.map expOfHOL) hcodecBase
  have hbridge := hbaseBridge.trans
    (by simpa [compileProgRiscV] using hproductionCongr.symm)
  simpa only [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes,
    Flapjack.Pancake.PanLang.listMap_expToHOL_expOfHOL] using hbridge

/-- Assembly bridge for the complete HOL `compile_def` `Call` arm
(`cakeml/pancake/pan_to_crepScript.sml:222-261`): it covers every `rtyp`
destination shape, `wrap_rt` outcome, handler presence and `eids` lookup by
reusing the nine kernel-checked sub-clause bridges.  The recursive premise
`hbody` is stated only for the handler body actually carried by `info`
(via `callHandlerBody`), not for every `ProgHOL`.  Flapjack-specific,
untagged production-routing infrastructure. -/
theorem compileProgExactHOLW_call_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (info : Option (Option (VarKind × Flapjack.Basis.Pure.MlString.MlString) ×
      Option (Flapjack.Basis.Pure.MlString.MlString ×
        Flapjack.Basis.Pure.MlString.MlString × ProgHOL width)))
    (function : String) (arguments : List (Exp (BitVec width)))
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hcodec :
      ∀ expression ∈ arguments,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
          compileExpHOL context.toProduction expression)
    (hbody :
      ∀ (body : ProgHOL width),
        callHandlerBody info = some body →
        crepProgOfHOL (compileProgExactHOLW context body) =
          compileProgHOL context.toProduction (progOfHOL body)) :
    crepProgOfHOL (compileProgExactHOLW context
        (.call info (Flapjack.Basis.Pure.MlString.ofString function)
          (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call (callInfoToProduction info) function arguments) := by
  cases info with
  | none =>
      exact compileProgExactHOLW_call_none_bridge context function arguments
        hfunction hcodec
  | some entry =>
      obtain ⟨destination, handler⟩ := entry
      cases destination with
      | none =>
          cases handler with
          | none =>
              exact compileProgExactHOLW_call_result_no_handler_bridge context
                function arguments hfunction hcodec
          | some handlerEntry =>
              obtain ⟨exceptionName, exceptionVariable, body⟩ := handlerEntry
              cases heid : context.eids.lookup exceptionName with
              | none =>
                  have heidOf : context.eids.lookup
                        (Flapjack.Basis.Pure.MlString.ofString
                          (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName)) =
                      none := by
                    rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                    exact heid
                  have hsub :=
                    compileProgExactHOLW_call_handler_missing_eid_bridge
                      (context := context) (function := function)
                      (exceptionName :=
                        Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName)
                      (exceptionVariable :=
                        Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionVariable)
                      (arguments := arguments) (body := body)
                      heidOf hfunction (nameRanged_toStringOfBytes exceptionName)
                      hcodec
                  rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes exceptionName,
                    Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes
                      exceptionVariable] at hsub
                  rw [show callInfoToProduction
                        (some (none, some (exceptionName, exceptionVariable, body))) =
                      some (none, some
                        (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName,
                         Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionVariable,
                         progOfHOL body)) from rfl]
                  exact hsub
              | some code =>
                  have hpresentOf : context.eids.lookup
                        (Flapjack.Basis.Pure.MlString.ofString
                          (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName)) =
                      some code := by
                    rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                    exact heid
                  have hsub :=
                    compileProgExactHOLW_call_handler_present_eid_bridge
                      (context := context) (function := function)
                      (exceptionName :=
                        Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName)
                      (exceptionVariable :=
                        Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionVariable)
                      (arguments := arguments) (body := body) (exceptionCode := code)
                      hpresentOf hfunction (nameRanged_toStringOfBytes exceptionName)
                      hcodec (hbody body (by rfl))
                  rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes exceptionName,
                    Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes
                      exceptionVariable] at hsub
                  rw [show callInfoToProduction
                        (some (none, some (exceptionName, exceptionVariable, body))) =
                      some (none, some
                        (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName,
                         Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionVariable,
                         progOfHOL body)) from rfl]
                  exact hsub
      | some destEntry =>
          obtain ⟨kind, resultName⟩ := destEntry
          cases hwrap : wrapRtHOL (context.vars.lookup resultName) with
          | none =>
              cases handler with
              | none =>
                  have hwrapOf : wrapRtHOL (context.vars.lookup
                        (Flapjack.Basis.Pure.MlString.ofString
                          (Flapjack.Basis.Pure.MlString.toStringOfBytes resultName))) =
                      none := by
                    rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                    exact hwrap
                  have hsub :=
                    compileProgExactHOLW_call_wrapped_result_fallback_no_handler_bridge
                      (context := context) (kind := kind)
                      (resultName :=
                        Flapjack.Basis.Pure.MlString.toStringOfBytes resultName)
                      (function := function) (arguments := arguments)
                      hwrapOf hfunction hcodec
                  rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes
                    resultName] at hsub
                  rw [show callInfoToProduction
                        (some (some (kind, resultName), none)) =
                      some (some (kind,
                        Flapjack.Basis.Pure.MlString.toStringOfBytes resultName), none)
                      from rfl]
                  exact hsub
              | some handlerEntry =>
                  obtain ⟨exceptionName, exceptionVariable, body⟩ := handlerEntry
                  cases heid : context.eids.lookup exceptionName with
                  | none =>
                      have hwrapOf : wrapRtHOL (context.vars.lookup
                            (Flapjack.Basis.Pure.MlString.ofString
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes
                                resultName))) = none := by
                        rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                        exact hwrap
                      have heidOf : context.eids.lookup
                            (Flapjack.Basis.Pure.MlString.ofString
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes
                                exceptionName)) = none := by
                        rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                        exact heid
                      have hsub :=
                        compileProgExactHOLW_call_wrapped_result_fallback_handler_missing_eid_bridge
                          (context := context) (kind := kind)
                          (resultName :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes resultName)
                          (function := function)
                          (exceptionName :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName)
                          (exceptionVariable :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes
                              exceptionVariable)
                          (arguments := arguments) (body := body)
                          hwrapOf heidOf hfunction (nameRanged_toStringOfBytes exceptionName)
                          hcodec
                      rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes resultName,
                        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes exceptionName,
                        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes
                          exceptionVariable] at hsub
                      rw [show callInfoToProduction
                            (some (some (kind, resultName),
                              some (exceptionName, exceptionVariable, body))) =
                          some (some (kind,
                              Flapjack.Basis.Pure.MlString.toStringOfBytes resultName),
                            some
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName,
                               Flapjack.Basis.Pure.MlString.toStringOfBytes
                                 exceptionVariable,
                               progOfHOL body)) from rfl]
                      exact hsub
                  | some code =>
                      have hwrapOf : wrapRtHOL (context.vars.lookup
                            (Flapjack.Basis.Pure.MlString.ofString
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes
                                resultName))) = none := by
                        rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                        exact hwrap
                      have hpresentOf : context.eids.lookup
                            (Flapjack.Basis.Pure.MlString.ofString
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes
                                exceptionName)) = some code := by
                        rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                        exact heid
                      have hsub :=
                        compileProgExactHOLW_call_wrapped_result_fallback_handler_present_eid_bridge
                          (context := context) (kind := kind)
                          (resultName :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes resultName)
                          (function := function)
                          (exceptionName :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName)
                          (exceptionVariable :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes
                              exceptionVariable)
                          (arguments := arguments) (body := body)
                          (exceptionCode := code)
                          hwrapOf hpresentOf hfunction
                          (nameRanged_toStringOfBytes exceptionName) hcodec (hbody body (by rfl))
                      rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes resultName,
                        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes exceptionName,
                        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes
                          exceptionVariable] at hsub
                      rw [show callInfoToProduction
                            (some (some (kind, resultName),
                              some (exceptionName, exceptionVariable, body))) =
                          some (some (kind,
                              Flapjack.Basis.Pure.MlString.toStringOfBytes resultName),
                            some
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName,
                               Flapjack.Basis.Pure.MlString.toStringOfBytes
                                 exceptionVariable,
                               progOfHOL body)) from rfl]
                      exact hsub
          | some wrapEntry =>
              obtain ⟨resultShape, resultNames⟩ := wrapEntry
              cases handler with
              | none =>
                  have hwrapOf : wrapRtHOL (context.vars.lookup
                        (Flapjack.Basis.Pure.MlString.ofString
                          (Flapjack.Basis.Pure.MlString.toStringOfBytes resultName))) =
                      some (resultShape, resultNames) := by
                    rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                    exact hwrap
                  have hsub :=
                    compileProgExactHOLW_call_wrapped_result_no_handler_bridge
                      (context := context) (kind := kind)
                      (resultName :=
                        Flapjack.Basis.Pure.MlString.toStringOfBytes resultName)
                      (function := function) (arguments := arguments)
                      (resultShape := resultShape) (resultNames := resultNames)
                      hwrapOf hfunction hcodec
                  rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes
                    resultName] at hsub
                  rw [show callInfoToProduction
                        (some (some (kind, resultName), none)) =
                      some (some (kind,
                        Flapjack.Basis.Pure.MlString.toStringOfBytes resultName), none)
                      from rfl]
                  exact hsub
              | some handlerEntry =>
                  obtain ⟨exceptionName, exceptionVariable, body⟩ := handlerEntry
                  cases heid : context.eids.lookup exceptionName with
                  | none =>
                      have hwrapOf : wrapRtHOL (context.vars.lookup
                            (Flapjack.Basis.Pure.MlString.ofString
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes
                                resultName))) = some (resultShape, resultNames) := by
                        rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                        exact hwrap
                      have heidOf : context.eids.lookup
                            (Flapjack.Basis.Pure.MlString.ofString
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes
                                exceptionName)) = none := by
                        rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                        exact heid
                      have hsub :=
                        compileProgExactHOLW_call_wrapped_result_handler_missing_eid_bridge
                          (context := context) (kind := kind)
                          (resultName :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes resultName)
                          (function := function)
                          (exceptionName :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName)
                          (exceptionVariable :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes
                              exceptionVariable)
                          (arguments := arguments) (body := body)
                          (resultShape := resultShape) (resultNames := resultNames)
                          hwrapOf heidOf hfunction
                          (nameRanged_toStringOfBytes exceptionName) hcodec
                      rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes resultName,
                        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes exceptionName,
                        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes
                          exceptionVariable] at hsub
                      rw [show callInfoToProduction
                            (some (some (kind, resultName),
                              some (exceptionName, exceptionVariable, body))) =
                          some (some (kind,
                              Flapjack.Basis.Pure.MlString.toStringOfBytes resultName),
                            some
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName,
                               Flapjack.Basis.Pure.MlString.toStringOfBytes
                                 exceptionVariable,
                               progOfHOL body)) from rfl]
                      exact hsub
                  | some code =>
                      have hwrapOf : wrapRtHOL (context.vars.lookup
                            (Flapjack.Basis.Pure.MlString.ofString
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes
                                resultName))) = some (resultShape, resultNames) := by
                        rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                        exact hwrap
                      have hpresentOf : context.eids.lookup
                            (Flapjack.Basis.Pure.MlString.ofString
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes
                                exceptionName)) = some code := by
                        rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]
                        exact heid
                      have hsub :=
                        compileProgExactHOLW_call_wrapped_result_handler_present_eid_bridge
                          (context := context) (kind := kind)
                          (resultName :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes resultName)
                          (function := function)
                          (exceptionName :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName)
                          (exceptionVariable :=
                            Flapjack.Basis.Pure.MlString.toStringOfBytes
                              exceptionVariable)
                          (arguments := arguments) (body := body)
                          (resultShape := resultShape) (resultNames := resultNames)
                          (exceptionCode := code)
                          hwrapOf hpresentOf hfunction
                          (nameRanged_toStringOfBytes exceptionName) hcodec (hbody body (by rfl))
                      rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes resultName,
                        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes exceptionName,
                        Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes
                          exceptionVariable] at hsub
                      rw [show callInfoToProduction
                            (some (some (kind, resultName),
                              some (exceptionName, exceptionVariable, body))) =
                          some (some (kind,
                              Flapjack.Basis.Pure.MlString.toStringOfBytes resultName),
                            some
                              (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName,
                               Flapjack.Basis.Pure.MlString.toStringOfBytes
                                 exceptionVariable,
                               progOfHOL body)) from rfl]
                      exact hsub

/-- Context-relation form of the recursive `Call` bridge. `callHandlerBody`
    limits the induction hypothesis to the exact handler body selected by the
    call metadata. The body uses the unchanged context, so its ranged relation
    is the reflexive exact-to-production relation. -/
theorem compileProgExactHOLW_call_contextRel_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (info : Option (Option (VarKind × Flapjack.Basis.Pure.MlString.MlString) ×
      Option (Flapjack.Basis.Pure.MlString.MlString ×
        Flapjack.Basis.Pure.MlString.MlString × ProgHOL width)))
    (function : String) (arguments : List (Exp (BitVec width)))
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hcodec : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression)
    (ih : ∀ body, callHandlerBody info = some body →
      PanToCrepContextExactProdRel context context.toProduction →
      crepProgOfHOL (compileProgExactHOLW context body) =
        compileProgHOL context.toProduction (progOfHOL body)) :
    crepProgOfHOL (compileProgExactHOLW context
        (.call info (Flapjack.Basis.Pure.MlString.ofString function)
          (arguments.map expToHOL))) =
      compileProgRiscV context.toProduction
        (.call (callInfoToProduction info) function arguments) := by
  have hrel : PanToCrepContextExactProdRel context context.toProduction := by
    exact panToCrepContextExactProdRel_refl context
  exact compileProgExactHOLW_call_bridge context info function arguments hfunction hcodec
    (fun body hselected => ih body hselected hrel)

/-- Relation-polymorphic Call case for an arbitrary related production
    context. The exact-context Call assembly supplies all `rtyp` and handler
    branches; the induction hypothesis supplies the selected handler body at
    both the reflexive and incoming context relations. -/
theorem compileProgExactHOLW_call_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (info : Option (Option (VarKind × Flapjack.Basis.Pure.MlString.MlString) ×
      Option (Flapjack.Basis.Pure.MlString.MlString ×
        Flapjack.Basis.Pure.MlString.MlString × ProgHOL width)))
    (function : String) (arguments : List (Exp (BitVec width)))
    (hfunction : Flapjack.Pancake.PanLang.NameRanged function)
    (hcodecBase : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression)
    (hcodecProduction : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL productionContext expression)
    (hbody : ∀ body productionContext, callHandlerBody info = some body →
      PanToCrepContextExactProdRel context productionContext →
      crepProgOfHOL (compileProgExactHOLW context body) =
        compileProgHOL productionContext (progOfHOL body)) :
    crepProgOfHOL (compileProgExactHOLW context
        (.call info (Flapjack.Basis.Pure.MlString.ofString function)
          (arguments.map expToHOL))) =
      compileProgHOL productionContext
        (.call (callInfoToProduction info) function arguments) := by
  have hbaseRel : PanToCrepContextExactProdRel context context.toProduction := by
    exact panToCrepContextExactProdRel_refl context
  have hargsFor : ∀ expressions,
      (∀ expression ∈ expressions,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
            compileExpHOL context.toProduction expression) →
      (∀ expression ∈ expressions,
        ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
          shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
            compileExpHOL productionContext expression) →
        compileArgsHOL context.toProduction expressions =
        compileArgsHOL productionContext expressions := by
    intro expressions hbase hproduction
    induction expressions with
    | nil =>
        rfl
    | cons expression expressions ih =>
        simp only [compileArgsHOL]
        have hbaseHead := hbase expression (by simp)
        have hproductionHead := hproduction expression (by simp)
        have hcompiled : compileExpHOL context.toProduction expression =
            compileExpHOL productionContext expression :=
          hbaseHead.symm.trans hproductionHead
        rw [hcompiled]
        rw [ih
          (by
            intro tail htail
            exact hbase tail (by simp [htail]))
          (by
            intro tail htail
            exact hproduction tail (by simp [htail]))]
  have hargs := hargsFor arguments hcodecBase hcodecProduction
  have hcodecBase' : ∀ expression ∈ arguments,
      ((compileExpExactHOLW context (expToHOL expression)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL expression)).2) =
        compileExpHOL context.toProduction expression := by
    intro expression hmem
    exact hcodecBase expression hmem
  have hexactToBase := compileProgExactHOLW_call_contextRel_bridge context info
    function arguments hfunction hcodecBase'
    (fun body hselected _hrel => hbody body context.toProduction hselected hbaseRel)
  have hbaseFuncs : context.toProduction.funcs function = productionContext.funcs function :=
    hcontext.1 function hfunction
  have hvmax : context.toProduction.vmax = productionContext.vmax := by
    simpa [PanToCrepContextExact.toProduction] using hcontext.2.2.1
  have hbaseVars := hcontext.2.2.2
  have heidsLookup (exceptionName : Flapjack.Basis.Pure.MlString.MlString) :
      context.toProduction.eids
          (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName) =
        productionContext.eids
          (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName) := by
    exact hcontext.2.1
      (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionName)
      (nameRanged_toStringOfBytes exceptionName)
  have hbodyCongr : ∀ body, callHandlerBody info = some body →
      compileProgHOL context.toProduction (progOfHOL body) =
        compileProgHOL productionContext (progOfHOL body) := by
    intro body hselected
    exact (hbody body context.toProduction hselected hbaseRel).symm.trans
      (hbody body productionContext hselected hcontext)
  have hbaseToProduction :
      compileProgRiscV context.toProduction
          (.call (callInfoToProduction info) function arguments) =
        compileProgHOL productionContext
          (.call (callInfoToProduction info) function arguments) := by
    cases info with
    | none =>
        simp [compileProgRiscV, compileProgHOL, callInfoToProduction, hargs]
    | some entry =>
        obtain ⟨destination, handler⟩ := entry
        cases destination with
        | none =>
            cases handler with
            | none =>
                simp [compileProgRiscV, compileProgHOL, callInfoToProduction,
                  functionReturnNamesHOL, allocatedNamesHOL, FLOOKUP,
                  hbaseFuncs, hvmax, hargs]
            | some handlerEntry =>
                obtain ⟨exceptionName, exceptionVariable, body⟩ := handlerEntry
                have hhandlerVars :
                    context.toProduction.vars
                        (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionVariable) =
                      productionContext.vars
                        (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionVariable) :=
                  hbaseVars _ (nameRanged_toStringOfBytes exceptionVariable)
                simp [compileProgRiscV, compileProgHOL, callInfoToProduction,
                  functionReturnNamesHOL, allocatedNamesHOL,
                  expHdlFiniteMap, FLOOKUP, hbaseFuncs, hvmax, hargs,
                  hhandlerVars, heidsLookup,
                  hbodyCongr body (by rfl)]
        | some destinationEntry =>
            obtain ⟨kind, destinationName⟩ := destinationEntry
            have hdestinationVars :
                context.toProduction.vars
                    (Flapjack.Basis.Pure.MlString.toStringOfBytes destinationName) =
                  productionContext.vars
                    (Flapjack.Basis.Pure.MlString.toStringOfBytes destinationName) :=
              hbaseVars _ (nameRanged_toStringOfBytes destinationName)
            cases handler with
            | none =>
                simp [compileProgRiscV, compileProgHOL, callInfoToProduction,
                  callDestinationNamesHOL, FLOOKUP, hargs, hdestinationVars]
            | some handlerEntry =>
                obtain ⟨exceptionName, exceptionVariable, body⟩ := handlerEntry
                have hhandlerVars :
                    context.toProduction.vars
                        (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionVariable) =
                      productionContext.vars
                        (Flapjack.Basis.Pure.MlString.toStringOfBytes exceptionVariable) :=
                  hbaseVars _ (nameRanged_toStringOfBytes exceptionVariable)
                simp [compileProgRiscV, compileProgHOL, callInfoToProduction,
                  callDestinationNamesHOL, expHdlFiniteMap, FLOOKUP,
                  hargs, hdestinationVars, hhandlerVars,
                  hbodyCongr body (by rfl),
                  heidsLookup]
  have hbridge := hexactToBase.trans (by
    simpa [compileProgRiscV] using hbaseToProduction)
  simpa [Flapjack.Pancake.PanLang.progOfHOL] using hbridge

/-- Relation-polymorphic Store case. The existing exact-context Store bridge
    preserves its address-head and value-shape guards; paired expression
    outputs and related `vmax` transport that result to an arbitrary related
    production context. -/
theorem compileProgExactHOLW_store_relation_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (address value : Exp (BitVec width))
    (haddressBase :
      ((compileExpExactHOLW context (expToHOL address)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL address)).2) =
        compileExpHOL context.toProduction address)
    (hvalueBase :
      ((compileExpExactHOLW context (expToHOL value)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL value)).2) =
        compileExpHOL context.toProduction value)
    (haddressProduction :
      ((compileExpExactHOLW context (expToHOL address)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL address)).2) =
        compileExpHOL productionContext address)
    (hvalueProduction :
      ((compileExpExactHOLW context (expToHOL value)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL value)).2) =
        compileExpHOL productionContext value) :
    crepProgOfHOL (compileProgExactHOLW context
        (.store (expToHOL address) (expToHOL value))) =
      compileProgHOL productionContext (.store address value) := by
  have haddressCongr : compileExpHOL context.toProduction address =
      compileExpHOL productionContext address :=
    haddressBase.symm.trans haddressProduction
  have hvalueCongr : compileExpHOL context.toProduction value =
      compileExpHOL productionContext value :=
    hvalueBase.symm.trans hvalueProduction
  have hvmax : context.toProduction.vmax = productionContext.vmax := by
    simpa [PanToCrepContextExact.toProduction] using hcontext.2.2.1
  cases hexactAddress : compileExpExactHOLW context (expToHOL address) with
  | mk exactAddresses exactAddressShape =>
      cases hexactValue : compileExpExactHOLW context (expToHOL value) with
      | mk exactValues exactValueShape =>
          cases hproductionAddress : compileExpHOL context.toProduction address with
          | mk productionAddresses productionAddressShape =>
              cases hproductionValue : compileExpHOL context.toProduction value with
              | mk productionValues productionValueShape =>
                  have haddressCodecPair := haddressBase
                  rw [hexactAddress, hproductionAddress] at haddressCodecPair
                  rcases Prod.mk.inj haddressCodecPair with
                    ⟨haddressCodec, _haddressShapeCodec⟩
                  have hvalueCodecPair := hvalueBase
                  rw [hexactValue, hproductionValue] at hvalueCodecPair
                  rcases Prod.mk.inj hvalueCodecPair with
                    ⟨hvalueCodec, hvalueShapeCodec⟩
                  have hproductionValue' :
                      compileExpHOL context.toProduction value =
                        (productionValues, productionValueShape) := hproductionValue
                  have hproductionAddress' :
                      compileExpHOL context.toProduction address =
                        (productionAddresses, productionAddressShape) := hproductionAddress
                  have hbaseBridge := compileProgExactHOLW_store_output_bridge
                    context address value exactAddresses exactAddressShape exactValues
                    exactValueShape productionAddresses productionAddressShape
                    productionValues productionValueShape hexactAddress hexactValue
                    hproductionAddress' hproductionValue' haddressCodec hvalueCodec
                    hvalueShapeCodec
                  have hcontextCongr :
                      compileProgHOL context.toProduction (.store address value) =
                        compileProgHOL productionContext (.store address value) := by
                    simp [compileProgHOL, freshNamesHOL, haddressCongr,
                      hvalueCongr, hvmax]
                  have hbridge := hbaseBridge.trans (by
                    simpa [compileProgRiscV] using hcontextCongr)
                  simpa [compileProgRiscV] using hbridge

theorem compileProgExactHOLW_shmem_store_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (operator : OpSize)
    (value address : Exp (BitVec width))
    (hvalue :
      ((compileExpExactHOLW context (expToHOL value)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL value)).2) =
        compileExpHOL context.toProduction value)
    (haddress :
      ((compileExpExactHOLW context (expToHOL address)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL address)).2) =
        compileExpHOL context.toProduction address) :
    crepProgOfHOL (compileProgExactHOLW context
        (.shMemStore operator (expToHOL value) (expToHOL address))) =
      compileProgRiscV context.toProduction
        (.shMemStore operator value address) := by
  rw [Prod.mk.injEq] at hvalue haddress
  rcases hvalue with ⟨hvalueList, _⟩
  rcases haddress with ⟨haddressList, _⟩
  cases hExactValue : compileExpExactHOLW context (expToHOL value) with
  | mk exactValues valueShape =>
      cases hExactAddress : compileExpExactHOLW context (expToHOL address) with
      | mk exactAddresses addressShape =>
          cases hProductionValue : compileExpHOL context.toProduction value with
          | mk productionValues productionValueShape =>
              cases hProductionAddress : compileExpHOL context.toProduction address with
              | mk productionAddresses productionAddressShape =>
                  cases exactValues <;> cases exactAddresses <;>
                    cases productionValues <;> cases productionAddresses <;>
                    simp_all [compileProgExactHOLW, compileShMemStoreExactHOLW,
                      compileProgRiscV, compileProgHOL, crepProgOfHOL,
                      firstCompiledExpAnyShapeHOL, maxCrepExpVarHOL,
                      crepExpVarsW, foldr_max_zero_eq_max_getD, nestedDecs,
                      List.flatMap]
                  all_goals
                    rw [List.foldl_max]
                    omega

/-- Relation-polymorphic shared-memory Store case. The four expression
    outputs and the related `vmax` determine the temporary and error paths; no
    equality of the full variable maps is required. -/
theorem compileProgExactHOLW_shmem_store_relation_bridge
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (operator : OpSize) (value address : ExpHOL width) :
    crepProgOfHOL
        (compileProgExactHOLW context (.shMemStore operator value address)) =
      compileProgHOL productionContext
        (.shMemStore operator (expOfHOL value) (expOfHOL address)) := by
  have hvalue := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext value
  have haddress := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext address
  rw [Prod.mk.injEq] at hvalue haddress
  rcases hvalue with ⟨hvalueList, _⟩
  rcases haddress with ⟨haddressList, _⟩
  cases hExactValue : compileExpExactHOLW context value with
  | mk exactValues valueShape =>
      cases hExactAddress : compileExpExactHOLW context address with
      | mk exactAddresses addressShape =>
          cases hProductionValue :
              compileExpHOL productionContext (expOfHOL value) with
          | mk productionValues productionValueShape =>
              cases hProductionAddress :
                  compileExpHOL productionContext (expOfHOL address) with
              | mk productionAddresses productionAddressShape =>
                  cases exactValues <;> cases exactAddresses <;>
                    cases productionValues <;> cases productionAddresses <;>
                    simp_all [compileProgExactHOLW, compileShMemStoreExactHOLW,
                      compileProgHOL, crepProgOfHOL, firstCompiledExpAnyShapeHOL,
                      maxCrepExpVarHOL, crepExpVarsW, foldr_max_zero_eq_max_getD,
                      nestedDecs, List.flatMap]
                  all_goals
                    rw [List.foldl_max]
                    omega

/-- The local `ShMemLoad` equation agrees across the exact and production
    carriers once the address compiler results are decoded. Both sides use the
    same exact finite-map destination lookup; missing address heads and missing
    or empty local destinations remain `Skip` as in HOL. -/
theorem compileProgExactHOLW_local_shmem_load_bridge {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (operator : OpSize) (name : MlS)
    (address : Exp (BitVec width))
    (haddressRanged : ExpByteRanged address)
    (hcodec :
      ((compileExpExactHOLW context (expToHOL address)).1.map crepExpOfHOL,
        shapeOfHOL (compileExpExactHOLW context (expToHOL address)).2) =
        compileExpHOL context.toProduction address) :
    crepProgOfHOL (compileProgExactHOLW context
        (.shMemLoad operator .local name (expToHOL address))) =
      compileProgRiscV context.toProduction
        (progOfHOL (.shMemLoad operator .local name (expToHOL address))) := by
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨haddressList, _⟩
  cases hExactAddress : compileExpExactHOLW context (expToHOL address) with
  | mk exactAddresses addressShape =>
      cases hProductionAddress : compileExpHOL context.toProduction address with
      | mk productionAddresses productionShape =>
          have hdecoded : exactAddresses.map crepExpOfHOL = productionAddresses := by
            simpa [hExactAddress, hProductionAddress] using haddressList
          cases exactAddresses with
          | nil =>
              cases productionAddresses with
              | nil => simp [compileProgExactHOLW, compileShMemLoadExactHOLW,
                  compileProgRiscV, compileProgHOL, crepProgOfHOL,
                  firstCompiledExpAnyShapeHOL, progOfHOL,
                  expOfHOL_expToHOL address haddressRanged, FLOOKUP,
                  hExactAddress, hProductionAddress]
              | cons productionHead productionTail => simp at hdecoded
          | cons exactHead exactTail =>
              cases productionAddresses with
              | nil => simp at hdecoded
              | cons productionHead productionTail =>
                  have hhead : crepExpOfHOL exactHead = productionHead :=
                    (List.cons.inj hdecoded).1
                  cases hlookup : context.vars.lookup name with
                  | none =>
                      simp [compileProgExactHOLW, compileShMemLoadExactHOLW,
                        compileProgRiscV, compileProgHOL, crepProgOfHOL,
                        firstCompiledExpAnyShapeHOL, progOfHOL, FLOOKUP,
                        expOfHOL_expToHOL address haddressRanged,
                        hExactAddress, hProductionAddress, hlookup,
                        PanToCrepContextExact.toProduction_vars_lookup]
                  | some entry =>
                      cases entry with
                      | mk shape names =>
                          cases names with
                          | nil =>
                              simp [compileProgExactHOLW, compileShMemLoadExactHOLW,
                                compileProgRiscV, compileProgHOL, crepProgOfHOL,
                                firstCompiledExpAnyShapeHOL, progOfHOL, FLOOKUP,
                                expOfHOL_expToHOL address haddressRanged,
                                hExactAddress, hProductionAddress, hlookup,
                                PanToCrepContextExact.toProduction_vars_lookup]
                          | cons destination rest =>
                              simp [compileProgExactHOLW, compileShMemLoadExactHOLW,
                                compileProgRiscV, compileProgHOL, crepProgOfHOL,
                                firstCompiledExpAnyShapeHOL, progOfHOL, FLOOKUP,
                                expOfHOL_expToHOL address haddressRanged,
                                hExactAddress, hProductionAddress, hlookup, hhead,
                                PanToCrepContextExact.toProduction_vars_lookup]

/-- Relation-polymorphic local ShMemLoad case. The destination lookup follows
    from the ranged context relation at the byte-decoded HOL name, and the
    address uses the expression codec at the same related contexts. -/
theorem compileProgExactHOLW_local_shmem_load_relation_bridge
    {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (productionContext : PanToCrepHOLContext (BitVec width))
    (hcontext : PanToCrepContextExactProdRel context productionContext)
    (operator : OpSize) (name : MlS) (address : ExpHOL width) :
    crepProgOfHOL
        (compileProgExactHOLW context (.shMemLoad operator .local name address)) =
      compileProgHOL productionContext
        (.shMemLoad operator .local
          (Flapjack.Basis.Pure.MlString.toStringOfBytes name) (expOfHOL address)) := by
  have hcodec := compileExpExactHOLW_prodCodec_of_contextRel
    context productionContext hcontext address
  rw [Prod.mk.injEq] at hcodec
  rcases hcodec with ⟨haddressList, _haddressShape⟩
  have hvars :
      productionContext.vars
          (Flapjack.Basis.Pure.MlString.toStringOfBytes name) =
        (context.vars.lookup name).map
          (fun entry => (Flapjack.Pancake.PanLang.shapeOfHOL entry.1, entry.2)) := by
    have hrel := hcontext.2.2.2
      (Flapjack.Basis.Pure.MlString.toStringOfBytes name)
      (nameRanged_toStringOfBytes name)
    rw [PanToCrepContextExact.toProduction_vars_lookup] at hrel
    exact hrel.symm
  cases hExactAddress : compileExpExactHOLW context address with
  | mk exactAddresses addressShape =>
      cases hProductionAddress :
          compileExpHOL productionContext (expOfHOL address) with
      | mk productionAddresses productionShape =>
          have hdecoded : exactAddresses.map crepExpOfHOL = productionAddresses := by
            simpa [hExactAddress, hProductionAddress] using haddressList
          cases exactAddresses with
          | nil =>
              cases productionAddresses with
              | nil =>
                  simp [compileProgExactHOLW, compileShMemLoadExactHOLW,
                    compileProgHOL, crepProgOfHOL, firstCompiledExpAnyShapeHOL,
                    FLOOKUP, hExactAddress, hProductionAddress]
              | cons productionHead productionTail => simp at hdecoded
          | cons exactHead exactTail =>
              cases productionAddresses with
              | nil => simp at hdecoded
              | cons productionHead productionTail =>
                  have hhead : crepExpOfHOL exactHead = productionHead :=
                    (List.cons.inj hdecoded).1
                  cases hlookup : context.vars.lookup name with
                  | none =>
                      simp [compileProgExactHOLW, compileShMemLoadExactHOLW,
                        compileProgHOL, crepProgOfHOL, firstCompiledExpAnyShapeHOL,
                        FLOOKUP, hExactAddress, hProductionAddress, hlookup, hvars]
                  | some entry =>
                      cases entry with
                      | mk shape names =>
                          cases names with
                          | nil =>
                              simp [compileProgExactHOLW, compileShMemLoadExactHOLW,
                                compileProgHOL, crepProgOfHOL,
                                firstCompiledExpAnyShapeHOL, FLOOKUP,
                                hExactAddress, hProductionAddress, hlookup, hvars]
                          | cons destination rest =>
                              simp [compileProgExactHOLW, compileShMemLoadExactHOLW,
                                compileProgHOL, crepProgOfHOL,
                                firstCompiledExpAnyShapeHOL, FLOOKUP,
                                hExactAddress, hProductionAddress, hlookup, hhead,
                                hvars]

/-- Flapjack-specific assembly theorem for the reviewed exact `compile_def`
    and the source-shaped production compiler. It is not itself a direct port
    of one HOL declaration: it relates two distinct Lean carriers and gathers
    the constructor bridges into one context-polymorphic induction principle.
    The constructor equations and their branch behavior were source-reviewed
    against `cakeml/pancake/pan_to_crepScript.sml:139-307`; recursive Dec,
    DecCall, and Call bodies use only the smaller-program hypothesis at the
    contexts justified by the ranged update relation and selected Call
    handler. -/
theorem compileProgExactHOLW_relation_bridge {width : Nat} [NeZero width]
    (program : ProgHOL width) :
    ∀ (exactContext : PanToCrepContextExact width)
      (productionContext : PanToCrepHOLContext (BitVec width)),
      PanToCrepContextExactProdRel exactContext productionContext →
      crepProgOfHOL (compileProgExactHOLW exactContext program) =
        compileProgHOL productionContext (progOfHOL program) := by
  let motive : ProgHOL width → Prop := fun program =>
    ∀ exactContext productionContext,
      PanToCrepContextExactProdRel exactContext productionContext →
      crepProgOfHOL (compileProgExactHOLW exactContext program) =
        compileProgHOL productionContext (progOfHOL program)
  have hall : ∀ program, motive program :=
    Flapjack.Pancake.PanLang.progHOL_sizeOf_induction motive (by
      intro program ih
      intro exactContext productionContext hcontext
      cases program with
      | skip =>
          exact compileProgExactHOLW_skip_relation_bridge exactContext
            productionContext hcontext
      | dec name shape value body =>
          have hbodySize : sizeOf body < sizeOf (ProgHOL.dec name shape value body) := by
            decreasing_trivial
          let name' := Flapjack.Basis.Pure.MlString.toStringOfBytes name
          let shape' := shapeOfHOL shape
          let value' := expOfHOL value
          let bodyContext : PanToCrepContextExact width :=
            { exactContext with
              vars := exactContext.vars.update (Flapjack.Basis.Pure.MlString.ofString name',
                ((compileExpExactHOLW exactContext (expToHOL value')).2,
                  (List.range (sizeOfShapeHOL
                    (compileExpExactHOLW exactContext (expToHOL value')).2)).map
                    (fun index => exactContext.vmax + index + 1)))
              vmax := exactContext.vmax + sizeOfShapeHOL
                (compileExpExactHOLW exactContext (expToHOL value')).2 }
          let nextContext : PanToCrepHOLContext (BitVec width) :=
            { productionContext with
              vars := FUPDATE productionContext.vars
                (name', ((compileExpHOL productionContext value').2,
                  allocatedNamesHOL productionContext (compileExpHOL productionContext value').2))
              vmax := productionContext.vmax +
                Shape.shapeSize (compileExpHOL productionContext value').2 }
          have hbodyContext : bodyContext =
              { exactContext with
                vars := exactContext.vars.update (Flapjack.Basis.Pure.MlString.ofString name',
                  ((compileExpExactHOLW exactContext (expToHOL value')).2,
                    (List.range (sizeOfShapeHOL
                      (compileExpExactHOLW exactContext (expToHOL value')).2)).map
                      (fun index => exactContext.vmax + index + 1)))
                vmax := exactContext.vmax + sizeOfShapeHOL
                  (compileExpExactHOLW exactContext (expToHOL value')).2 } := rfl
          have hnextContext : nextContext =
              { productionContext with
                vars := FUPDATE productionContext.vars
                  (name', ((compileExpHOL productionContext value').2,
                    allocatedNamesHOL productionContext (compileExpHOL productionContext value').2))
                vmax := productionContext.vmax +
                  Shape.shapeSize (compileExpHOL productionContext value').2 } := rfl
          have hcodec := compileExpExactHOLW_prodCodec_of_contextRel
            exactContext productionContext hcontext value
          have hcodec' :
              ((compileExpExactHOLW exactContext (expToHOL value')).1.map crepExpOfHOL,
                shapeOfHOL (compileExpExactHOLW exactContext (expToHOL value')).2) =
                compileExpHOL productionContext value' := by
            simpa [value'] using hcodec
          have hbridge := compileProgExactHOLW_dec_relation_bridge
            exactContext productionContext hcontext name' shape' value' body
            bodyContext nextContext hbodyContext hnextContext hcodec'
            (nameRanged_toStringOfBytes name)
            (fun ec pc hrel => ih body hbodySize ec pc hrel)
          simpa [motive, compileProgRiscV, progOfHOL, name', shape', value',
            Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes] using hbridge
      | assign kind name value =>
          cases kind with
          | «local» =>
              simpa [progOfHOL] using compileProgExactHOLW_local_assign_relation_bridge
                exactContext productionContext hcontext name value
          | global =>
              simpa [progOfHOL] using compileProgExactHOLW_global_assign_relation_bridge
                exactContext productionContext hcontext name value
      | primitive name operator arguments =>
          simpa [progOfHOL] using compileProgExactHOLW_primitive_relation_bridge
            exactContext productionContext hcontext name operator arguments
      | store address value =>
          have hbaseRel : PanToCrepContextExactProdRel exactContext
              exactContext.toProduction := by
            exact panToCrepContextExactProdRel_refl exactContext
          let address' := expOfHOL address
          let value' := expOfHOL value
          have haddressBase :
              ((compileExpExactHOLW exactContext (expToHOL address')).1.map crepExpOfHOL,
                shapeOfHOL (compileExpExactHOLW exactContext (expToHOL address')).2) =
                compileExpHOL exactContext.toProduction address' := by
            simpa [address'] using compileExpExactHOLW_prodCodec_of_contextRel
              exactContext exactContext.toProduction hbaseRel address
          have hvalueBase :
              ((compileExpExactHOLW exactContext (expToHOL value')).1.map crepExpOfHOL,
                shapeOfHOL (compileExpExactHOLW exactContext (expToHOL value')).2) =
                compileExpHOL exactContext.toProduction value' := by
            simpa [value'] using compileExpExactHOLW_prodCodec_of_contextRel
              exactContext exactContext.toProduction hbaseRel value
          have haddressProduction :
              ((compileExpExactHOLW exactContext (expToHOL address')).1.map crepExpOfHOL,
                shapeOfHOL (compileExpExactHOLW exactContext (expToHOL address')).2) =
                compileExpHOL productionContext address' := by
            simpa [address'] using compileExpExactHOLW_prodCodec_of_contextRel
              exactContext productionContext hcontext address
          have hvalueProduction :
              ((compileExpExactHOLW exactContext (expToHOL value')).1.map crepExpOfHOL,
                shapeOfHOL (compileExpExactHOLW exactContext (expToHOL value')).2) =
                compileExpHOL productionContext value' := by
            simpa [value'] using compileExpExactHOLW_prodCodec_of_contextRel
              exactContext productionContext hcontext value
          have hbridge := compileProgExactHOLW_store_relation_bridge
            exactContext productionContext hcontext address' value'
            haddressBase hvalueBase haddressProduction hvalueProduction
          simpa [address', value', progOfHOL] using hbridge
      | store32 address value =>
          simpa [progOfHOL] using compileProgExactHOLW_store32_relation_bridge
            exactContext productionContext hcontext address value
      | storeByte address value =>
          simpa [progOfHOL] using compileProgExactHOLW_store_byte_relation_bridge
            exactContext productionContext hcontext address value
      | seq first second =>
          have hfirstSize : sizeOf first < sizeOf (ProgHOL.seq first second) := by
            decreasing_trivial
          have hsecondSize : sizeOf second < sizeOf (ProgHOL.seq first second) := by
            decreasing_trivial
          simpa [progOfHOL] using compileProgExactHOLW_seq_relation_bridge exactContext
            productionContext hcontext first second
            (fun ec pc hrel => ih first hfirstSize ec pc hrel)
            (fun ec pc hrel => ih second hsecondSize ec pc hrel)
      | ite condition thenBranch elseBranch =>
          have hthenSize : sizeOf thenBranch < sizeOf (ProgHOL.ite condition thenBranch elseBranch) := by
            decreasing_trivial
          have helseSize : sizeOf elseBranch < sizeOf (ProgHOL.ite condition thenBranch elseBranch) := by
            decreasing_trivial
          simpa [progOfHOL] using compileProgExactHOLW_if_relation_bridge exactContext
            productionContext hcontext condition thenBranch elseBranch
            (ih thenBranch hthenSize exactContext productionContext hcontext)
            (ih elseBranch helseSize exactContext productionContext hcontext)
      | «while» condition body =>
          have hbodySize : sizeOf body < sizeOf (ProgHOL.while condition body) := by
            decreasing_trivial
          simpa [progOfHOL] using compileProgExactHOLW_while_relation_bridge exactContext
            productionContext hcontext condition body
            (fun hrel => ih body hbodySize exactContext productionContext hrel)
      | «break» =>
          exact compileProgExactHOLW_break_relation_bridge exactContext
            productionContext hcontext
      | «continue» =>
          exact compileProgExactHOLW_continue_relation_bridge exactContext
            productionContext hcontext
      | call info function arguments =>
          let function' := Flapjack.Basis.Pure.MlString.toStringOfBytes function
          have hbaseRel : PanToCrepContextExactProdRel exactContext
              exactContext.toProduction := by
            exact panToCrepContextExactProdRel_refl exactContext
          have hcodecBase : ∀ expression ∈ arguments.map expOfHOL,
              ((compileExpExactHOLW exactContext (expToHOL expression)).1.map crepExpOfHOL,
                shapeOfHOL (compileExpExactHOLW exactContext (expToHOL expression)).2) =
                compileExpHOL exactContext.toProduction expression := by
            intro expression hmem
            obtain ⟨sourceExpression, hmem, rfl⟩ := List.mem_map.mp hmem
            simpa using compileExpExactHOLW_prodCodec_of_contextRel
              exactContext exactContext.toProduction hbaseRel sourceExpression
          have hcodecProduction : ∀ expression ∈ arguments.map expOfHOL,
              ((compileExpExactHOLW exactContext (expToHOL expression)).1.map crepExpOfHOL,
                shapeOfHOL (compileExpExactHOLW exactContext (expToHOL expression)).2) =
                compileExpHOL productionContext expression := by
            intro expression hmem
            obtain ⟨sourceExpression, hmem, rfl⟩ := List.mem_map.mp hmem
            simpa using compileExpExactHOLW_prodCodec_of_contextRel
              exactContext productionContext hcontext sourceExpression
          have hbody : ∀ body production, callHandlerBody info = some body →
              PanToCrepContextExactProdRel exactContext production →
              crepProgOfHOL (compileProgExactHOLW exactContext body) =
                compileProgHOL production (progOfHOL body) := by
            intro body production hselected hrel
            cases info with
            | none => simp [callHandlerBody] at hselected
            | some callInfo =>
                rcases callInfo with ⟨result, handler⟩
                cases handler with
                | none => simp [callHandlerBody] at hselected
                | some handlerInfo =>
                    rcases handlerInfo with ⟨exceptionName, varName, handlerBody⟩
                    have hbodyEq : handlerBody = body := by
                      simpa [callHandlerBody] using hselected
                    subst body
                    have hbodySize :
                        sizeOf handlerBody <
                          sizeOf (ProgHOL.call
                            (some (result, some (exceptionName, varName, handlerBody)))
                            function arguments) := by
                      decreasing_trivial
                    exact ih handlerBody hbodySize exactContext production hrel
          have hargs :=
            Flapjack.Pancake.PanLang.listMap_expToHOL_expOfHOL arguments
          have hbridge := compileProgExactHOLW_call_relation_bridge
            exactContext productionContext hcontext info function' (arguments.map expOfHOL)
            (nameRanged_toStringOfBytes function)
            hcodecBase hcodecProduction hbody
          rw [hargs] at hbridge
          rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes function] at hbridge
          have hcallProg :
              progOfHOL (ProgHOL.call info function arguments) =
                Prog.call (callInfoToProduction info) function' (arguments.map expOfHOL) := by
            cases info with
            | none => simp [Flapjack.Pancake.PanLang.progOfHOL,
                callInfoToProduction, function']
            | some entry =>
                rcases entry with ⟨destination, handler⟩
                cases destination with
                | none =>
                    cases handler with
                    | none => simp [Flapjack.Pancake.PanLang.progOfHOL,
                        callInfoToProduction, function']
                    | some handlerEntry =>
                        rcases handlerEntry with ⟨exceptionName, variableName, body⟩
                        simp [Flapjack.Pancake.PanLang.progOfHOL,
                          callInfoToProduction, function']
                | some destinationEntry =>
                    rcases destinationEntry with ⟨kind, resultName⟩
                    cases handler with
                    | none => simp [Flapjack.Pancake.PanLang.progOfHOL,
                        callInfoToProduction, function']
                    | some handlerEntry =>
                        rcases handlerEntry with ⟨exceptionName, variableName, body⟩
                        simp [Flapjack.Pancake.PanLang.progOfHOL,
                          callInfoToProduction, function']
          rw [hcallProg]
          simpa [function', Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes] using hbridge
      | decCall name shape function arguments body =>
          have hbodySize :
              sizeOf body < sizeOf (ProgHOL.decCall name shape function arguments body) := by
            decreasing_trivial
          let name' := Flapjack.Basis.Pure.MlString.toStringOfBytes name
          let function' := Flapjack.Basis.Pure.MlString.toStringOfBytes function
          let shape' := shapeOfHOL shape
          let arguments' := arguments.map expOfHOL
          let bodyContext : PanToCrepContextExact width :=
            { exactContext with
              vars := exactContext.vars.update (Flapjack.Basis.Pure.MlString.ofString name',
                (shapeToHOL shape',
                  (List.range (sizeOfShapeHOL (shapeToHOL shape'))).map
                    (fun index => exactContext.vmax + index + 1)))
              vmax := exactContext.vmax + sizeOfShapeHOL (shapeToHOL shape') }
          let nextContext : PanToCrepHOLContext (BitVec width) :=
            { productionContext with
              vars := FUPDATE productionContext.vars
                (name', (shape',
                  (List.range (Shape.shapeSize shape')).map
                    (fun offset => productionContext.vmax + 1 + offset)))
              vmax := productionContext.vmax + Shape.shapeSize shape' }
          have hbodyContext : bodyContext =
              { exactContext with
                vars := exactContext.vars.update (Flapjack.Basis.Pure.MlString.ofString name',
                  (shapeToHOL shape',
                    (List.range (sizeOfShapeHOL (shapeToHOL shape'))).map
                      (fun index => exactContext.vmax + index + 1)))
                vmax := exactContext.vmax + sizeOfShapeHOL (shapeToHOL shape') } := rfl
          have hnextContext : nextContext =
              { productionContext with
                vars := FUPDATE productionContext.vars
                  (name', (shape',
                    (List.range (Shape.shapeSize shape')).map
                      (fun offset => productionContext.vmax + 1 + offset)))
                vmax := productionContext.vmax + Shape.shapeSize shape' } := rfl
          have hcodec : ∀ expression ∈ arguments',
              ((compileExpExactHOLW exactContext (expToHOL expression)).1.map crepExpOfHOL,
                shapeOfHOL (compileExpExactHOLW exactContext (expToHOL expression)).2) =
                compileExpHOL productionContext expression := by
            intro expression hmem
            obtain ⟨sourceExpression, hmem, rfl⟩ := List.mem_map.mp hmem
            simpa [arguments'] using compileExpExactHOLW_prodCodec_of_contextRel
              exactContext productionContext hcontext sourceExpression
          have hargs :=
            Flapjack.Pancake.PanLang.listMap_expToHOL_expOfHOL arguments
          have hbridge := compileProgExactHOLW_decCall_relation_bridge
            exactContext productionContext hcontext name' function' shape' arguments' body
            bodyContext nextContext hbodyContext hnextContext hcodec
            (nameRanged_toStringOfBytes name)
            (PanToCrepContextExact.toProduction_shapeByteRanged shape)
            (nameRanged_toStringOfBytes function)
            (fun ec pc hrel => ih body hbodySize ec pc hrel)
          rw [show arguments'.map expToHOL = arguments by
            simpa [arguments'] using hargs] at hbridge
          rw [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes name,
            Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes function] at hbridge
          simpa [name', function', shape', arguments', progOfHOL, compileProgRiscV,
            Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes] using hbridge
      | extCall function configuration configurationLength array arrayLength =>
          let function' := Flapjack.Basis.Pure.MlString.toStringOfBytes function
          simpa [function', progOfHOL,
            Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes] using
            compileProgExactHOLW_extCall_relation_bridge exactContext
            productionContext hcontext function' (expOfHOL configuration)
            (expOfHOL configurationLength) (expOfHOL array) (expOfHOL arrayLength)
            (nameRanged_toStringOfBytes function)
            (expOfHOL_byteRanged configuration)
            (expOfHOL_byteRanged configurationLength)
            (expOfHOL_byteRanged array)
            (expOfHOL_byteRanged arrayLength)
      | raise exception value =>
          simpa [progOfHOL] using compileProgExactHOLW_raise_relation_bridge exactContext
            productionContext hcontext exception value
      | «return» value =>
          simpa [progOfHOL] using compileProgExactHOLW_return_relation_bridge exactContext
            productionContext hcontext value
      | shMemLoad operator kind name address =>
          cases kind with
          | «local» =>
              simpa [progOfHOL] using compileProgExactHOLW_local_shmem_load_relation_bridge
                exactContext productionContext hcontext operator name address
          | global =>
              simpa [progOfHOL] using compileProgExactHOLW_global_shmem_load_relation_bridge
                exactContext productionContext hcontext operator name address
      | shMemStore operator first second =>
          simpa [progOfHOL] using compileProgExactHOLW_shmem_store_relation_bridge
            exactContext productionContext hcontext operator first second
      | tick =>
          exact compileProgExactHOLW_tick_relation_bridge exactContext
            productionContext hcontext
      | annot tag text =>
          exact compileProgExactHOLW_annot_relation_bridge exactContext
            productionContext hcontext tag text)
  simpa [motive] using hall program

/-- Flapjack-specific per-function compiler correspondence (no standalone HOL
    declaration): for every function extracted from a byte-ranged declaration
    list, the exact `compile_def` body compiler, decoded to production Crep,
    equals the executed `compFuncHOL` body compiler. The finite-support and
    name-range facts come from the same production context builder used by
    `compileToCrepHOL`; the body codec is discharged by the extracted-entry
    byte-range theorem. -/
theorem compileFunctionExactProductionBridge {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (entry : FunName × List (VarName × Shape) × Prog (BitVec width) × Shape)
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration)
    (hentry : entry ∈ functionEntries declarations) :
    crepProgOfHOL
        (compileProgExactHOLW
          (panToCrepContextExactOfProduction
            (panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
              (functionInfosHOL declarations)
              (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
              (panToCrepGetEidsFromDeclsHOL declarations))
            (panToCrepFunctionContextProductionEvidence declarations entry
              hdecls hentry))
          (progToHOL entry.2.2.1)) =
      compFuncHOL (functionInfosHOL declarations)
        (panToCrepGetEidsFromDeclsHOL declarations) entry.2.1 entry.2.2.1 := by
  let productionContext :=
    panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
      (functionInfosHOL declarations)
      (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
      (panToCrepGetEidsFromDeclsHOL declarations)
  let evidence := panToCrepFunctionContextProductionEvidence declarations entry
    hdecls hentry
  let exactContext := panToCrepContextExactOfProduction productionContext evidence
  have hrelation := panToCrepContextExactOfProduction_relation productionContext evidence
  have hwhole := compileProgExactHOLW_relation_bridge (progToHOL entry.2.2.1)
    exactContext productionContext hrelation
  obtain ⟨_hname, _hparams, _hreturnShape, hbody⟩ :=
    functionEntries_byteRanged declarations hdecls entry hentry
  rw [progOfHOL_progToHOL entry.2.2.1 hbody] at hwhole
  simpa [productionContext, exactContext, evidence, compFuncHOL, compileProgRiscV]
    using hwhole

private theorem compFuncExactHOLW_productionContext_bridge
    {width : Nat} [NeZero width]
    (params : List (VarName × Shape))
    (productionContext : PanToCrepHOLContext (BitVec width))
    (evidence : PanToCrepContextProductionEvidence productionContext)
    (hvarsSource : productionContext.vars = panToCrepMakeVmapHOL params)
    (hvmaxSource : productionContext.vmax =
      Shape.shapeSize (.comb (params.map Prod.snd)) - 1)
    (hparams : ∀ p ∈ params,
      Flapjack.Pancake.PanLang.NameRanged p.1 ∧
        Flapjack.Pancake.PanLang.ShapeByteRanged p.2)
    (body : Flapjack.Pancake.PanLang.ProgHOL width) :
    compFuncExactHOLW
        (panToCrepContextExactOfProduction productionContext evidence).funcs
        (panToCrepContextExactOfProduction productionContext evidence).eids
        (params.map fun (name, shape) =>
          (Flapjack.Basis.Pure.MlString.ofString name,
            Flapjack.Pancake.PanLang.shapeToHOL shape)) body =
      compileProgExactHOLW
        (panToCrepContextExactOfProduction productionContext evidence) body := by
  let exactParams := params.map fun (name, shape) =>
    (Flapjack.Basis.Pure.MlString.ofString name,
      Flapjack.Pancake.PanLang.shapeToHOL shape)
  let exactContext := panToCrepContextExactOfProduction productionContext evidence
  have hvars : exactContext.vars = panToCrepMakeVmapHOLExact exactParams := by
    apply holFiniteMapExact_ext_local
    intro key
    change exactContext.vars.lookup key = _
    rw [panToCrepContextExactOfProduction_vars_lookup]
    rw [hvarsSource]
    exact (panToCrepMakeVmapHOLExactOfProductionParams params hparams key).symm
  have hvmax : sizeOfShapeHOL (.comb (exactParams.map Prod.snd)) - 1 =
      exactContext.vmax := by
    calc
      sizeOfShapeHOL (.comb (exactParams.map Prod.snd)) - 1 =
          Shape.shapeSize (.comb (params.map Prod.snd)) - 1 := by
        have hcombined : .comb (exactParams.map Prod.snd) =
            Flapjack.Pancake.PanLang.shapeToHOL (.comb (params.map Prod.snd)) := by
          simp [exactParams, Flapjack.Pancake.PanLang.shapeToHOL]
        rw [hcombined, sizeOfShapeHOL_shapeToHOL]
      _ = productionContext.vmax := hvmaxSource.symm
      _ = exactContext.vmax := rfl
  have hcontext :
      mkCtxtExactHOL (panToCrepMakeVmapHOLExact exactParams)
        exactContext.funcs (sizeOfShapeHOL (.comb (exactParams.map Prod.snd)) - 1)
        exactContext.eids = exactContext := by
    cases hExact : exactContext with
    | mk vars funcs eids vmax =>
        have hvars' : panToCrepMakeVmapHOLExact exactParams = vars := by
          simpa only [hExact] using hvars.symm
        have hvmax' : sizeOfShapeHOL (.comb (exactParams.map Prod.snd)) - 1 = vmax := by
          simpa only [hExact] using hvmax
        cases hvars'
        cases hvmax'
        rfl
  simp only [compFuncExactHOLW]
  rw [hcontext]

/-- The parser-backed compiler's exactified context and its byte-ranged
    parameter list reduce the tagged HOL-shaped wrapper to the already-proved
    exact `compile` call on that same context. -/
private theorem compileFunctionExactHOLWProductionBridge
    {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (entry : FunName × List (VarName × Shape) × Prog (BitVec width) × Shape)
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration)
    (hentry : entry ∈ functionEntries declarations) :
    crepProgOfHOL
        (compFuncExactHOLW
          (panToCrepContextExactOfProduction
            (panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
              (functionInfosHOL declarations)
              (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
              (panToCrepGetEidsFromDeclsHOL declarations))
            (panToCrepFunctionContextProductionEvidence declarations entry
              hdecls hentry)).funcs
          (panToCrepContextExactOfProduction
            (panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
              (functionInfosHOL declarations)
              (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
              (panToCrepGetEidsFromDeclsHOL declarations))
            (panToCrepFunctionContextProductionEvidence declarations entry
              hdecls hentry)).eids
          (entry.2.1.map fun (name, shape) =>
            (Flapjack.Basis.Pure.MlString.ofString name,
              Flapjack.Pancake.PanLang.shapeToHOL shape))
          (progToHOL entry.2.2.1)) =
      compFuncHOL (functionInfosHOL declarations)
        (panToCrepGetEidsFromDeclsHOL declarations) entry.2.1 entry.2.2.1 := by
  let productionContext :=
    panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
      (functionInfosHOL declarations)
      (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
      (panToCrepGetEidsFromDeclsHOL declarations)
  let evidence := panToCrepFunctionContextProductionEvidence declarations entry
    hdecls hentry
  obtain ⟨_hname, hparams, _hreturnShape, hbody⟩ :=
    functionEntries_byteRanged declarations hdecls entry hentry
  rw [compFuncExactHOLW_productionContext_bridge entry.2.1
    productionContext evidence (by rfl) (by rfl)
    (fun p hp => (hparams p hp))
    (progToHOL entry.2.2.1)]
  exact compileFunctionExactProductionBridge declarations entry hdecls hentry

/-- Flapjack-specific output-preservation theorem for the exact parser-backed
    body route (no HOL original): each entry calls tagged
    `compFuncExactHOLW`; the byte-ranged context/parameter bridge shows that
    decoding its result preserves the corresponding `compileToCrepHOL` triple,
    so the shared source-shaped inlining pass receives the same input. -/
theorem compileProgTopHOLProductionExact_eq {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
  compileProgTopHOLProductionExact declarations hdecls =
      compileProgTopHOL declarations := by
  unfold compileProgTopHOLProductionExact
  unfold compileProgTopHOL
  let functions := functionEntriesOfHOLExact declarations hdecls
  let functionMap := functionInfosHOL declarations
  let exceptionMap := panToCrepGetEidsFromDeclsHOL declarations
  have hmap : exceptionMap = panToCrepGetEidsFromDeclsHOL declarations := rfl
  let inlineNames :=
    (functionEntries (declarations.filter inlinableThroughHOL)).map
      fun (name, _, _, _) => name
  have hvalues :
      functions.attach.map (fun entryWithProof =>
        let entry := entryWithProof.val
        let productionContext :=
          panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
            functionMap
            (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
            exceptionMap
        let evidence := by
          have hentry : entry ∈ functionEntries declarations := by
            rw [← functionEntriesOfHOLExact_eq declarations hdecls]
            exact entryWithProof.property
          simpa [productionContext, hmap] using
            panToCrepFunctionContextProductionEvidence declarations entry
              hdecls hentry
        let exactContext := panToCrepContextExactOfProduction productionContext evidence
        let exactParams := entry.2.1.map fun (name, shape) =>
          (Flapjack.Basis.Pure.MlString.ofString name,
            Flapjack.Pancake.PanLang.shapeToHOL shape)
        (entry.1, panToCrepVars entry.2.1,
          crepProgOfHOL (compFuncExactHOLW exactContext.funcs exactContext.eids exactParams
            (progToHOL entry.2.2.1)))) =
      functions.attach.map (fun entryWithProof =>
        (entryWithProof.val.1, panToCrepVars entryWithProof.val.2.1,
          compFuncHOL functionMap exceptionMap entryWithProof.val.2.1
            entryWithProof.val.2.2.1)) := by
    apply List.map_congr_left
    intro entryWithProof _hmem
    have hentry : entryWithProof.val ∈ functionEntries declarations := by
      rw [← functionEntriesOfHOLExact_eq declarations hdecls]
      exact entryWithProof.property
    simpa [functionMap, exceptionMap,
      panToCrepGetEidsFromDeclsOfExactHOL_eq declarations hdecls] using
      compileFunctionExactHOLWProductionBridge declarations entryWithProof.val
        hdecls hentry
  have hcompiled :
      functions.attach.map (fun entryWithProof =>
        (entryWithProof.val.1, panToCrepVars entryWithProof.val.2.1,
          compFuncHOL functionMap exceptionMap entryWithProof.val.2.1
            entryWithProof.val.2.2.1)) = compileToCrepHOL declarations := by
    have hattach :
        functions.attach.map (fun entryWithProof =>
          (entryWithProof.val.1, panToCrepVars entryWithProof.val.2.1,
            compFuncHOL functionMap exceptionMap entryWithProof.val.2.1
              entryWithProof.val.2.2.1)) =
          functions.map (fun entry =>
            (entry.1, panToCrepVars entry.2.1,
              compFuncHOL functionMap exceptionMap entry.2.1 entry.2.2.1)) := by
      exact List.attach_map_val (l := functions) (f := fun entry =>
        (entry.1, panToCrepVars entry.2.1,
          compFuncHOL functionMap exceptionMap entry.2.1 entry.2.2.1))
    have hproductionMap :
        functions.map (fun entry =>
          (entry.1, panToCrepVars entry.2.1,
          compFuncHOL functionMap exceptionMap entry.2.1 entry.2.2.1)) =
          compileToCrepHOL declarations := by
      change (functionEntriesOfHOLExact declarations hdecls).map _ = _
      rw [functionEntriesOfHOLExact_eq declarations hdecls]
      rw [hmap]
      simp [compileToCrepHOL, functionMap,
        functionInfosHOL_eq_makeFuncsHOL]
    exact hattach.trans hproductionMap
  change compileInlTopHOL inlineNames
      (functions.attach.map (fun entryWithProof =>
        let entry := entryWithProof.val
        let productionContext :=
          panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
            functionMap
            (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
            exceptionMap
          have hmap : exceptionMap = panToCrepGetEidsFromDeclsHOL declarations := rfl
          let evidence := by
            have hentry : entry ∈ functionEntries declarations := by
              rw [← functionEntriesOfHOLExact_eq declarations hdecls]
              exact entryWithProof.property
            simpa [productionContext, hmap] using
              panToCrepFunctionContextProductionEvidence declarations entry
                hdecls hentry
        let exactContext := panToCrepContextExactOfProduction productionContext evidence
        let exactParams := entry.2.1.map fun (name, shape) =>
          (Flapjack.Basis.Pure.MlString.ofString name,
            Flapjack.Pancake.PanLang.shapeToHOL shape)
        (entry.1, panToCrepVars entry.2.1,
          crepProgOfHOL (compFuncExactHOLW exactContext.funcs exactContext.eids exactParams
            (progToHOL entry.2.2.1))))) =
    compileInlTopHOL inlineNames (compileToCrepHOL declarations)
  rw [hvalues, hcompiled]

/-- Metadata adapter whose compiler input crosses the exact `DeclHOL` carrier
    boundary.  Its side condition is the byte-range premise used by the
    production-to-HOL declaration codec; it is preserved by the executed
    entry transforms before this adapter is called. -/
def compileProgTopHOLWithMetadataOfExact {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    List (CompiledFunction (BitVec width)) :=
  (compileToCrepHOLWithMetadata declarations).zipWith
    (fun original (_, _, body) => { original with body })
    (compileProgTopHOLProductionExact declarations h)

/-- The exact-carrier `compile_prog` boundary agrees with the production
    compiler on every byte-ranged declaration list. -/
theorem compileProgTopHOLOfExact_declToHOL {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Flapjack.Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    compileProgTopHOLOfExact (declarations.map declToHOL) =
      compileProgTopHOL declarations := by
  unfold compileProgTopHOLOfExact
  rw [map_declOfHOL_declToHOL declarations h]

/-- The exact-carrier metadata adapter preserves the current pipeline result
    for every declaration list satisfying the codec's byte-range premise. -/
theorem compileProgTopHOLWithMetadataOfExact_eq {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    compileProgTopHOLWithMetadataOfExact declarations h =
      compileProgTopHOLWithMetadata declarations := by
  unfold compileProgTopHOLWithMetadataOfExact compileProgTopHOLWithMetadata
  rw [compileProgTopHOLProductionExact_eq declarations h]

end Flapjack
