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
