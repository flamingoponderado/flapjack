import Flapjack.HolRef
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.PanLang.Decl

/-!
HOL-shaped top-level Pancake-to-Crep compiler boundary. The compilation
produces HOL's function-triple shape and passes it through Flapjack's
source-shaped inline traversal; the exact `compile_inl_top` carrier port is
tracked by `flapjack-e7w.1`. Its executed selection filter calls the reviewed
`inlinableHOL` through the total `inlinableThroughHOL` declaration adapter.
Metadata is attached only in a downstream adapter for Flapjack's existing
pipeline representation.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

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
-- `String`) via untagged `compileToCrepHOL` vs HOL `'a crepLang$prog` via
-- `compile_to_crep`; (4) `compileInlTopHOL` is the source-shaped pass over
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
-- `compile` by `.18.3.5.8.13`, exact `compile_inl_top` carrier by
-- `flapjack-e7w.1`; the full exact `compile_inl_top` and production inliner
-- are tracked by open epic `flapjack-e7w.2`). In `compileFlapjackEntryCake`
-- (Pipeline.lean), the
-- parser-proved branch invokes `compileProgTopHOLWithMetadataOfExact`, which
-- crosses the `DeclHOL` input boundary and then calls this source-shaped
-- implementation; it does not make the emitted Crep bodies exact
-- `CrepProgHOL` values. This is a carrier gap, not a measured performance
-- exception. Keep the `compile_prog_def` inventory bead open until the exact
-- `compile_to_crep` and `compile_inl_top` dependencies are routed through the
-- executed path.
def compileProgTopHOL [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width))) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  let inlineNames :=
    (functionEntries (declarations.filter inlinableThroughHOL)).map
      fun (name, _, _, _) => name
  compileInlTopHOL inlineNames (compileToCrepHOL declarations)

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

/-! Exact-carrier interface for the `compile_prog` boundary (bead
    flapjack-pxn.18.3.5.8.6). It consumes the MLString-keyed declaration
carrier `DeclHOL` and converts byte-ranged names at the boundary via
`declOfHOL`, so the exact HOL carriers are the interface type of the
declaration-level compiler boundary. The parser-backed source entrypoints pass
their proved byte-range invariant into `compileProgTopHOLWithMetadataOfExact`,
which routes the compiler body through this interface. Its result still uses
Flapjack's source-shaped Crep carrier; the explicit carrier mismatch and
unported HOL `compile`/`compile_inl_top` dependencies remain documented above. -/
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
    crepProgOfHOL (expHdlExact (width := width) ⟨context.vars⟩
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

/-- Metadata adapter whose compiler input crosses the exact `DeclHOL` carrier
    boundary.  Its side condition is the byte-range premise used by the
    production-to-HOL declaration codec; it is preserved by the executed
    entry transforms before this adapter is called. -/
def compileProgTopHOLWithMetadataOfExact {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (_h : ∀ d ∈ declarations, DeclByteRanged d) :
    List (CompiledFunction (BitVec width)) :=
  (compileToCrepHOLWithMetadata declarations).zipWith
    (fun original (_, _, body) => { original with body })
    (compileProgTopHOLOfExact (declarations.map declToHOL))

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
  rw [compileProgTopHOLOfExact_declToHOL declarations h]

end Flapjack
