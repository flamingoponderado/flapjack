import Flapjack.HolRef
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.PanToCrep.CompileExpBridge
import Flapjack.FiniteMap
import Flapjack.Pancake.PanToCrep.ContextBridge
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanLang.ProgHOLInduction

/-!
HOL-shaped top-level Pancake-to-Crep compiler boundary. The per-function
exact adapter here retains the production inliner and is proved equal to
the compatibility route.
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
-- `compile_prog` (`pan_to_crepScript.sml:393-397`) is `compile_inl_top (MAP
-- FST (functions (FILTER inlinable prog)))    (compile_to_crep prog)` over a
-- word-indexed `'a prog`; its result is `(mlstring # num list # 'a
-- crepLang$prog) list`, with no additional hypotheses or side conditions. This
-- definition differs on carriers, not just names: (1) declarations and inline
-- names use `FunName` = `String` vs HOL `funname` = `mlstring`; (2) the source
-- is a production `Decl (BitVec width)` with production `Shape` vs HOL's
-- word-indexed `decl` carrying `mlstring`/`shape`; (3) the target is
-- production `CrepProg (BitVec width)` (whose `Call`/`ExtCall` funnames are
-- `String`) via a decode of exact `compileProgExactHOLW` bodies in the
-- parser-backed entry path vs HOL `'a crepLang$prog` via `compile_to_crep`;
-- (4) `compileInlTopHOL` is the source-shaped pass over generic `CrepProg α`
-- vs HOL `compile_inl_top`. The `[BEq FunName] [LawfulBEq FunName]
-- [LawfulHashable FunName] [OfNat (BitVec width) 0/1]` arguments are
-- executable artifacts HOL does not have. `names_as_string` cannot authorize
-- the `Decl`/`Shape`/`CrepProg` carriers and no `NameRanged` witness exists
-- (the output is a triple list, not a name). Direct HOL-EVAL rows `empty`,
-- `duplicate_first`, `nested_inline` in
-- `scripts/hol-probes/compile_prog_probe.out` are reproduced by
-- `Flapjack/Test/CompileProgParity.lean`; the `params_two_words` row is
-- reproduced by `Flapjack/Test/CompileProgParamsParity.lean`. Faithful-port
-- dependency `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`; exact
-- `compile` by `.18.3.5.8.13`, exact `compile_inl_top` by `flapjack-e7w.1`;
-- the exact-carrier inliner is a tested, non-executed alternative until proved
-- equal. The full compile_prog adapter and end-to-end carrier bridge remain
-- tracked by open epic `flapjack-e7w.2`). The `compile_prog_def` inventory
-- remains open for the full exact-carrier declaration and end-to-end bridge.
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

/-!
Exact-carrier input adapter for the `compile_prog` boundary (bead
flapjack-pxn.18.3.5.8.6). It consumes the MLString-keyed declaration
carrier `DeclHOL` and converts byte-ranged names at the boundary via
`declOfHOL`, so the exact HOL carriers are the interface type of the
declaration-level compiler boundary. This standalone adapter is retained
for callers that need the production projection. Remaining full
compile_prog carrier gaps are documented above.
-/
def compileProgTopHOLOfExact {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (DeclHOL width)) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  compileProgTopHOL (declarations.map declOfHOL)

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

/-- `compile_param_vars` emits only name-ranged entries when every
parameter name is ranged. Untagged Flapjack infrastructure. -/
theorem compileParamVars_entries_nameRanged
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

end Flapjack
