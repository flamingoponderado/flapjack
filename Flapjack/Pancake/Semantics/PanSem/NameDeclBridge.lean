import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.EvalFinite
import Flapjack.Pancake.PanLang.Decl

/-!
This module records constructor-level production/exact congruence for the HOL
`Name`, `Function`, and `ExnDecl` clauses without claiming the still-missing relation
between the full production and exact state carriers.

HOL source review: `cakeml/pancake/semantics/panSemScript.sml:814-837`
defines `evaluate_decls s (Name nm flds::ds) = evaluate_decls s ds`; production
`Flapjack.evaluateDecls` and tagged
`PanSemStateFiniteExact.evaluateDeclsHOLFinite` each recurse on the tail and
do not inspect the state, field names, memory, or memory domain in this case.
The `NameRanged`/shape byte-range premise below is needed only to recover a
production declaration after encoding it through exact `DeclHOL`; it is not
needed for the no-op evaluator clause itself. There is no memory-domain
operation in this constructor. The congruence below nevertheless carries an
explicit production/exact memory-domain relation unchanged, so it can serve as
the Name case of a later context relation without claiming that relation is
already complete.

The original HOL EVAL row `name_noop` is recorded in
`scripts/hol-probes/pan_evaluate_decls_probe.out` and checked for both the
executed production evaluator (`PanEvaluateDeclsParity`) and the tagged
finite-support evaluator (`PanSemEvaluateDeclsFiniteParity`).

For `Function`, HOL's `panSemScript.sml:829-832` checks every parameter shape
and the return shape, then updates only `code` with the semantic
`(params, body, return)` payload. Production stores the same payload in
`PanSemFunctionEntry`; its inline/export fields are not in the code-map value.
`PanSemDeclarationCodeMapRel` compares that payload at byte-ranged keys. The
Function prefix theorem assumes exact equality of both carrier-specific shape
checks and a recursive-tail relation after the code-map update. The direct
original `function_code_update`, `function_code_replacement`,
`function_bad_param_shape`, and `function_bad_return_shape` EVAL rows are
checked by `PanSemEvaluateDeclsExactParity` and `PanEvaluateDeclsParity`.

For `ExnDecl`, HOL checks absence in `s.eshapes` and exact `is_wf_shape`, then
updates only `eshapes` before recursing. The relational lemma below compares
the production `InfoMap` lookup/update with the canonical finite-map lookup/
update on byte-ranged identifiers and carries the memory-domain component
unchanged. It assumes equality of the production and exact shape-well-formed
checks and a recursive-tail induction hypothesis; the full struct/state
relation remains unproved. The original HOL `exn_decl_ok` and failure rows in
the same probe file are exercised by `PanSemEvaluateDeclsExactParity`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
  (DeclHOL declOfHOL declToHOL DeclByteRanged NameRanged ShapeByteRanged MlS
    ShapeHOL isWfShapeExactHOL shapeToHOL FunDeclOf funDeclToHOL paramToHOL
    progToHOL ProgHOL ExpHOL expToHOL)

/-- Relate evaluator results by relating successful states and requiring both
    evaluators to agree on failure. -/
def PanSemDeclarationOutputRel {width : Nat} {σ : Type}
    [NeZero width]
    (R : PanSemDeclarationState (BitVec width) σ →
      PanSemStateFiniteExact width σ → Prop) :
    Option (PanSemDeclarationState (BitVec width) σ) →
      Option (PanSemStateFiniteExact width σ) → Prop
  | none, none => True
  | some production, some exact => R production exact
  | _, _ => False

/-- The memory-domain component of a production/exact declaration context
    relation. Production records domain membership as a Boolean; HOL's state
    records `memaddrs` as a proposition. -/
def PanSemDeclarationDomainRel {width : Nat} {σ : Type}
    [NeZero width]
    (production : PanSemDeclarationState (BitVec width) σ)
    (exact : PanSemStateFiniteExact width σ) : Prop :=
  ∀ address, production.memoryAccess.domain address = true ↔ exact.memaddrs address

/-- The exception-shape component of an exact-to-production declaration-state
    relation. Queries are restricted to byte-ranged names because production
    `String` is not a lossless carrier for arbitrary HOL `mlstring` keys. -/
def PanSemDeclarationEshapeMapRel (production : InfoMap Shape)
    (exact : HolFiniteMapExact MlS ShapeHOL) : Prop :=
  ∀ name, NameRanged name →
    (lookupInfo name production).map shapeToHOL =
      exact.lookup (Flapjack.Basis.Pure.MlString.ofString name)

/-- Domain and exception-map components carried by the `ExnDecl` slice. This
    is deliberately not the complete state relation required by the parent. -/
def PanSemDeclarationExnContextRel {width : Nat} {σ : Type} [NeZero width]
    (production : PanSemDeclarationState (BitVec width) σ)
    (exact : PanSemStateFiniteExact width σ) : Prop :=
  PanSemDeclarationDomainRel production exact ∧
    PanSemDeclarationEshapeMapRel production.eshapes exact.eshapes

/-- `panSemDeclUpdateInfo` and HOL finite-map update preserve the ranged
    exception-map relation, including the updated key. -/
theorem panSemDeclarationEshapeMapRel_update
    (production : InfoMap Shape) (exact : HolFiniteMapExact MlS ShapeHOL)
    (name : String) (shape : Shape)
    (hname : NameRanged name)
    (hrel : PanSemDeclarationEshapeMapRel production exact) :
    PanSemDeclarationEshapeMapRel
      (panSemDeclUpdateInfo production name shape)
      (HolFiniteMapExact.update exact
        (Flapjack.Basis.Pure.MlString.ofString name, shapeToHOL shape)) := by
  intro key hkey
  by_cases heq : key = name
  · subst key
    simp [panSemDeclUpdateInfo, lookupInfo, HolFiniteMapExact.update, FUPDATE]
  · have hkeyNe : Flapjack.Basis.Pure.MlString.ofString key ≠
        Flapjack.Basis.Pure.MlString.ofString name := by
      intro h
      apply heq
      have hk := congrArg Flapjack.Basis.Pure.MlString.toStringOfBytes h
      simpa only [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes
        key hkey, Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes
        name hname] using hk
    have hprod := lookupInfo_panSemDeclUpdateInfo production name shape key
    have hne : name ≠ key := fun h => heq h.symm
    calc
      Option.map shapeToHOL
          (lookupInfo key (panSemDeclUpdateInfo production name shape)) =
          Option.map shapeToHOL
            (FLOOKUP (FUPDATE (fun k => lookupInfo k production)
              (name, shape)) key) := by rw [hprod]
      _ = (HolFiniteMapExact.update exact
          (Flapjack.Basis.Pure.MlString.ofString name, shapeToHOL shape)).lookup
            (Flapjack.Basis.Pure.MlString.ofString key) := by
        simpa [FLOOKUP, FLOOKUP_update, FUPDATE, HolFiniteMapExact.lookup_update,
          hne, hkeyNe, hkeyNe.symm] using
          hrel key hkey

/-- Relational `ExnDecl` case of HOL `evaluate_decls_def`. The lookup and
    shape-well-formedness facts are the exact cross-carrier premises for its
    branch test. The only recursive premise is the tail relation after the
    matching map updates; the production Boolean memory domain is carried
    unchanged. This proves one constructor case, not the complete evaluator
    bridge or a relation for the other state fields. -/
theorem evaluateDecls_exnDecl_prefix_congr {width : Nat} {σ : Type}
    [NeZero width]
    (productionState : PanSemDeclarationState (BitVec width) σ)
    (exactState : PanSemStateFiniteExact width σ)
    [hmem : DecidablePred exactState.memaddrs]
    (exceptionName : String) (shape : Shape)
    (hbytes : DeclByteRanged
      (.exnDecl exceptionName shape : Decl (BitVec width)))
    (declarations : List (DeclHOL width))
    (hcontext : PanSemDeclarationExnContextRel productionState exactState)
    (hshapeWf : isWfShape productionState.runtime.structs shape =
      isWfShapeExactHOL exactState.structs (shapeToHOL shape))
    (htail : ∀ (production : PanSemDeclarationState (BitVec width) σ)
        (exact : PanSemStateFiniteExact width σ)
        [DecidablePred exact.memaddrs],
      PanSemDeclarationExnContextRel production exact →
      PanSemDeclarationOutputRel PanSemDeclarationExnContextRel
        (evaluateDecls production (declarations.map declOfHOL))
        (PanSemStateFiniteExact.evaluateDeclsHOLFinite exact declarations)) :
    PanSemDeclarationOutputRel PanSemDeclarationExnContextRel
      (evaluateDecls productionState
        (declOfHOL (declToHOL
          (.exnDecl exceptionName shape : Decl (BitVec width))) ::
          declarations.map declOfHOL))
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite exactState
        (declToHOL (.exnDecl exceptionName shape : Decl (BitVec width)) ::
          declarations)) := by
  have hproductionCodec :
      declOfHOL (declToHOL
        (.exnDecl exceptionName shape : Decl (BitVec width))) =
        .exnDecl exceptionName shape :=
    Flapjack.Pancake.PanLang.declOfHOL_declToHOL _ hbytes
  rcases hbytes with ⟨hname, hshape⟩
  have hlookup := hcontext.2 exceptionName hname
  rw [hproductionCodec]
  simp only [evaluateDecls,
    PanSemStateFiniteExact.evaluateDeclsHOLFinite, declToHOL]
  cases hprod : lookupInfo exceptionName productionState.eshapes with
  | none =>
      have hexact : exactState.eshapes.lookup
          (Flapjack.Basis.Pure.MlString.ofString exceptionName) = none := by
        simpa [hprod] using hlookup.symm
      by_cases hwf : isWfShape productionState.runtime.structs shape
      · have hwfExact : isWfShapeExactHOL exactState.structs (shapeToHOL shape) := by
          rw [← hshapeWf]
          exact hwf
        let productionUpdated : PanSemDeclarationState (BitVec width) σ :=
          { productionState with eshapes :=
              panSemDeclUpdateInfo productionState.eshapes exceptionName shape }
        let exactMapUpdated : HolFiniteMapExact MlS ShapeHOL :=
          exactState.eshapes.update
          (Flapjack.Basis.Pure.MlString.ofString exceptionName, shapeToHOL shape)
        let exactUpdated : PanSemStateFiniteExact width σ :=
          { exactState with eshapes := exactMapUpdated }
        letI : DecidablePred exactUpdated.memaddrs := hmem
        have hupdated : PanSemDeclarationExnContextRel
            productionUpdated exactUpdated := by
          constructor
          · exact hcontext.1
          · exact panSemDeclarationEshapeMapRel_update productionState.eshapes
              exactState.eshapes exceptionName shape hname hcontext.2
        have htail' := htail productionUpdated exactUpdated hupdated
        simpa [productionUpdated, exactUpdated, hprod, hexact, hwf, hwfExact,
          PanSemDeclarationOutputRel] using htail'
      · have hwfExact : isWfShapeExactHOL exactState.structs
            (shapeToHOL shape) = false := by
          rw [← hshapeWf]
          exact Bool.eq_false_iff.mpr hwf
        simp [hexact, hwf, hwfExact, PanSemDeclarationOutputRel]
  | some oldShape =>
      have hexact : exactState.eshapes.lookup
        (Flapjack.Basis.Pure.MlString.ofString exceptionName) =
            some (shapeToHOL oldShape) := by
        simpa [hprod] using hlookup.symm
      simp [hexact, PanSemDeclarationOutputRel]

/-- Flapjack-specific clause equation: production `Name` evaluation is the
    identity on a singleton declaration. There is no HOL tag here because the
    HOL declaration is `evaluate_decls_def`; this equation specializes its
    already-reviewed `Name` clause to the executed production evaluator. -/
theorem evaluateDecls_name_production_eq {width : Nat} {σ : Type}
    [NeZero width]
    (state : PanSemDeclarationState (BitVec width) σ)
    (structureName : String) (fields : List (String × Shape)) :
    evaluateDecls state [.name structureName fields] = some state := by
  simp [evaluateDecls]

/-- The corresponding exact finite-support evaluator also returns its input
    unchanged for one `Name`; this is the exact HOL clause specialization. -/
theorem evaluateDecls_name_finite_eq {width : Nat} {σ : Type}
    [NeZero width]
    (state : PanSemStateFiniteExact width σ) [_h : DecidablePred state.memaddrs]
    (structureName : MlS) (fields : List (MlS × ShapeHOL)) :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite state
      [.name structureName fields] = some state := by
  simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite]

/-- Prefixing related evaluator continuations with one production `Name`
    declaration and its exact `DeclHOL` encoding preserves the supplied state
    relation on every result (including `none`). The premise is the induction
    hypothesis for the tail; this lemma supplies only HOL's `Name` case. -/
theorem evaluateDecls_name_prefix_congr {width : Nat} {σ : Type}
    [NeZero width]
    (productionState : PanSemDeclarationState (BitVec width) σ)
    (exactState : PanSemStateFiniteExact width σ)
    [h : DecidablePred exactState.memaddrs]
    (structureName : String) (fields : List (String × Shape))
    (hbytes : DeclByteRanged
      (.name structureName fields : Decl (BitVec width)))
    (declarations : List (DeclHOL width))
    (R : PanSemDeclarationState (BitVec width) σ →
      PanSemStateFiniteExact width σ → Prop)
    (htail : PanSemDeclarationOutputRel R
      (evaluateDecls productionState (declarations.map declOfHOL))
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite exactState declarations)) :
    PanSemDeclarationOutputRel R
      (evaluateDecls productionState
        (declOfHOL (declToHOL
          (.name structureName fields : Decl (BitVec width))) ::
          declarations.map declOfHOL))
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite exactState
        (declToHOL (.name structureName fields : Decl (BitVec width)) ::
          declarations)) := by
  rw [Flapjack.Pancake.PanLang.declOfHOL_declToHOL _ hbytes]
  simpa only [evaluateDecls, PanSemStateFiniteExact.evaluateDeclsHOLFinite,
    declToHOL] using htail

/-- For the direct `name_noop` row, a byte-ranged production `Name` and its
    exact encoding leave related production/exact contexts related. This
    records the old/new complete `Option` output relation for the constructor;
    it does not assume or establish the production/exact context relation. -/
theorem evaluateDecls_name_singleton_rel {width : Nat} {σ : Type}
    [NeZero width]
    (productionState : PanSemDeclarationState (BitVec width) σ)
    (exactState : PanSemStateFiniteExact width σ)
    [h : DecidablePred exactState.memaddrs]
    (structureName : String) (fields : List (String × Shape))
    (hbytes : DeclByteRanged
      (.name structureName fields : Decl (BitVec width)))
    (R : PanSemDeclarationState (BitVec width) σ →
      PanSemStateFiniteExact width σ → Prop)
    (hcontext : R productionState exactState) :
    PanSemDeclarationOutputRel R
      (evaluateDecls productionState
        [declOfHOL (declToHOL
          (.name structureName fields : Decl (BitVec width)))] )
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite exactState
        [declToHOL (.name structureName fields : Decl (BitVec width))]) := by
  have htail : PanSemDeclarationOutputRel R
      (evaluateDecls productionState ([] : List (Decl (BitVec width))))
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite exactState
        ([] : List (DeclHOL width))) := by
    simpa [PanSemDeclarationOutputRel, evaluateDecls,
      PanSemStateFiniteExact.evaluateDeclsHOLFinite] using hcontext
  simpa using evaluateDecls_name_prefix_congr productionState exactState
    structureName fields hbytes [] R htail

/-- The singleton `Name` case preserves an explicit memory-domain context
    relation. The premise is included because the overall evaluator bridge
    must relate production's Boolean domain to HOL's proposition-valued
    `memaddrs`; this no-op clause preserves it without consulting it. -/
theorem evaluateDecls_name_singleton_domain_rel {width : Nat} {σ : Type}
    [NeZero width]
    (productionState : PanSemDeclarationState (BitVec width) σ)
    (exactState : PanSemStateFiniteExact width σ)
    [_h : DecidablePred exactState.memaddrs]
    (structureName : String) (fields : List (String × Shape))
    (hbytes : DeclByteRanged
      (.name structureName fields : Decl (BitVec width)))
    (hdomain : PanSemDeclarationDomainRel productionState exactState) :
    PanSemDeclarationOutputRel PanSemDeclarationDomainRel
      (evaluateDecls productionState
        [declOfHOL (declToHOL
          (.name structureName fields : Decl (BitVec width)))])
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite exactState
        [declToHOL (.name structureName fields : Decl (BitVec width))]) := by
  have hproduction : evaluateDecls productionState
      [declOfHOL (declToHOL
        (.name structureName fields : Decl (BitVec width)))] =
      some productionState := by
    rw [Flapjack.Pancake.PanLang.declOfHOL_declToHOL _ hbytes]
    exact evaluateDecls_name_production_eq productionState structureName fields
  have hexact : PanSemStateFiniteExact.evaluateDeclsHOLFinite exactState
      [declToHOL (.name structureName fields : Decl (BitVec width))] =
      some exactState := by
    simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite, declToHOL]
  rw [hproduction, hexact]
  exact hdomain

/-- Map a production source-code entry to the exact code-map payload stored by
    HOL `evaluate_decls`: parameter shapes, body, and return shape. The
    function's inline/export flags are syntax metadata, not fields of the
    semantic `(params, (body, return))` code entry. -/
def panSemFunctionEntryToHOL {width : Nat} [NeZero width]
    (entry : PanSemFunctionEntry (BitVec width)) :
    List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL :=
  (entry.params.map paramToHOL, progToHOL entry.body, shapeToHOL entry.returnShape)

/-- The semantic code-map entry carried by a production function declaration.
    This intentionally drops the source-only inline/export flags, matching
    HOL's `(fi.params, (fi.body, fi.return))` payload. -/
def panSemFunctionEntryOfDecl {width : Nat} [NeZero width]
    (declaration : FunDeclOf width) : PanSemFunctionEntry (BitVec width) :=
  { params := declaration.params
    body := declaration.body
    returnShape := declaration.returnShape }

/-- Relate the production association-list code map to HOL's exact finite
    code map on byte-ranged queried keys. Values are compared after encoding
    each production entry as the exact HOL `(params, body, return)` payload. -/
def PanSemDeclarationCodeMapRel {width : Nat} [NeZero width]
    (production : InfoMap (PanSemFunctionEntry (BitVec width)))
    (exact : HolFiniteMapExact MlS
      (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) : Prop :=
  ∀ name, NameRanged name →
    (lookupInfo name production).map panSemFunctionEntryToHOL =
      exact.lookup (Flapjack.Basis.Pure.MlString.ofString name)

/-- The Function-prefix context relation retains the explicit memory-domain
    and exception-map components and adds only the ranged code-map relation
    touched by the HOL Function clause. -/
def PanSemDeclarationFunctionContextRel {width : Nat} {σ : Type}
    [NeZero width]
    (production : PanSemDeclarationState (BitVec width) σ)
    (exact : PanSemStateFiniteExact width σ) : Prop :=
  PanSemDeclarationDomainRel production exact ∧
    PanSemDeclarationEshapeMapRel production.eshapes exact.eshapes ∧
    PanSemDeclarationCodeMapRel production.code exact.code

/-- The production `InfoMap` update and exact HOL finite-map update preserve
    the code-map relation at ranged keys. At the updated key, both payloads are
    encodings of the same production declaration; other ranged keys cannot
    alias the updated key after `MlString.ofString`. -/
theorem panSemDeclarationCodeMapRel_update {width : Nat} [NeZero width]
    (production : InfoMap (PanSemFunctionEntry (BitVec width)))
    (exact : HolFiniteMapExact MlS
      (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (declaration : FunDeclOf width)
    (hname : NameRanged declaration.name)
    (hrel : PanSemDeclarationCodeMapRel production exact) :
    PanSemDeclarationCodeMapRel
      (panSemDeclUpdateInfo production declaration.name
        (panSemFunctionEntryOfDecl declaration))
      (exact.update ((funDeclToHOL declaration).name,
        ((funDeclToHOL declaration).params, (funDeclToHOL declaration).body,
          (funDeclToHOL declaration).returnShape))) := by
  intro name hnameQuery
  rw [lookupInfo_panSemDeclUpdateInfo]
  by_cases heq : name = declaration.name
  · subst name
    rw [HolFiniteMapExact.lookup_update_pointwise]
    simp [FLOOKUP, FUPDATE, panSemFunctionEntryToHOL,
      panSemFunctionEntryOfDecl, funDeclToHOL]
  · have hkeyNe : Flapjack.Basis.Pure.MlString.ofString name ≠
        (funDeclToHOL declaration).name := by
      intro h
      apply heq
      have hk := congrArg Flapjack.Basis.Pure.MlString.toStringOfBytes h
      simpa only [funDeclToHOL, Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes
        name hnameQuery, Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes
        declaration.name hname] using hk
    have hne : declaration.name ≠ name := fun h => heq h.symm
    rw [HolFiniteMapExact.lookup_update_pointwise]
    simp [FLOOKUP, FUPDATE, hne, hkeyNe,
      hrel name hnameQuery]

/-- Relational `Function` case of HOL `evaluate_decls_def`. The exact
    well-formedness equality is precisely the cross-carrier premise needed to
    align the clause's branch test. On success only the code-map component is
    updated; on failure both evaluators return `none`. The recursive premise
    is restricted to the explicit domain/exception/code relation, so this is
    one constructor case rather than a whole-state or complete evaluator
    equivalence. -/
theorem evaluateDecls_function_prefix_congr {width : Nat} {σ : Type}
    [NeZero width]
    (productionState : PanSemDeclarationState (BitVec width) σ)
    (exactState : PanSemStateFiniteExact width σ)
    [hmem : DecidablePred exactState.memaddrs]
    (declaration : FunDeclOf width)
    (hbytes : DeclByteRanged (.function declaration : Decl (BitVec width)))
    (declarations : List (DeclHOL width))
    (hcontext : PanSemDeclarationFunctionContextRel productionState exactState)
    (hwf :
      (declaration.params.all (fun parameter =>
        isWfShape productionState.runtime.structs parameter.2) &&
        isWfShape productionState.runtime.structs declaration.returnShape) =
      ((funDeclToHOL declaration).params.all (fun parameter =>
        isWfShapeExactHOL exactState.structs parameter.2) &&
        isWfShapeExactHOL exactState.structs
          (funDeclToHOL declaration).returnShape))
    (htail : ∀ (production : PanSemDeclarationState (BitVec width) σ)
        (exact : PanSemStateFiniteExact width σ)
        [DecidablePred exact.memaddrs],
      PanSemDeclarationFunctionContextRel production exact →
      PanSemDeclarationOutputRel PanSemDeclarationFunctionContextRel
        (evaluateDecls production (declarations.map declOfHOL))
        (PanSemStateFiniteExact.evaluateDeclsHOLFinite exact declarations)) :
    PanSemDeclarationOutputRel PanSemDeclarationFunctionContextRel
      (evaluateDecls productionState
        (declOfHOL (declToHOL (.function declaration : Decl (BitVec width))) ::
          declarations.map declOfHOL))
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite exactState
        (declToHOL (.function declaration : Decl (BitVec width)) ::
          declarations)) := by
  have hproductionCodec :
      declOfHOL (declToHOL (.function declaration : Decl (BitVec width))) =
        .function declaration :=
    Flapjack.Pancake.PanLang.declOfHOL_declToHOL _ hbytes
  rw [hproductionCodec]
  simp only [evaluateDecls,
    PanSemStateFiniteExact.evaluateDeclsHOLFinite, declToHOL]
  cases hprod : (declaration.params.all (fun parameter =>
      isWfShape productionState.runtime.structs parameter.2) &&
      isWfShape productionState.runtime.structs declaration.returnShape) with
  | false =>
      have hexact :
          ((funDeclToHOL declaration).params.all (fun parameter =>
            isWfShapeExactHOL exactState.structs parameter.2) &&
            isWfShapeExactHOL exactState.structs
              (funDeclToHOL declaration).returnShape) = false := by
        rw [← hwf]
        exact hprod
      simp [hexact, PanSemDeclarationOutputRel]
  | true =>
      have hexact :
          ((funDeclToHOL declaration).params.all (fun parameter =>
            isWfShapeExactHOL exactState.structs parameter.2) &&
            isWfShapeExactHOL exactState.structs
              (funDeclToHOL declaration).returnShape) = true := by
        rw [← hwf]
        exact hprod
      let productionUpdated : PanSemDeclarationState (BitVec width) σ :=
        { productionState with code := (panSemDeclUpdateInfo productionState.code
          declaration.name (panSemFunctionEntryOfDecl declaration)) }
      let exactUpdated : PanSemStateFiniteExact width σ :=
        { exactState with code := (exactState.code.update
          ((funDeclToHOL declaration).name,
            ((funDeclToHOL declaration).params, (funDeclToHOL declaration).body,
              (funDeclToHOL declaration).returnShape))) }
      letI : DecidablePred exactUpdated.memaddrs := hmem
      have hupdated : PanSemDeclarationFunctionContextRel
          productionUpdated exactUpdated := by
        refine ⟨hcontext.1, hcontext.2.1, ?_⟩
        rcases hbytes with ⟨hfun⟩
        exact panSemDeclarationCodeMapRel_update productionState.code
          exactState.code declaration hfun hcontext.2.2
      have htail' := htail productionUpdated exactUpdated hupdated
      simpa [productionUpdated, exactUpdated, panSemFunctionEntryOfDecl, hexact,
      PanSemDeclarationOutputRel] using htail'

/-- Relate the successful values of the production `String`-backed evaluator
    and the exact `ValueHOL` evaluator. This relation deliberately leaves the
    cross-carrier value translation to the caller. -/
def PanSemStateFiniteExact.evalDeclExpressionHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [hmem : DecidablePred state.memaddrs] (expression : ExpHOL width) :
    Option (ValueHOL width) := by
  let emptyState := PanSemStateFiniteExact.emptyLocalsHOLFinite state
  letI : DecidablePred emptyState.memaddrs := hmem
  exact PanSemStateFiniteExact.evalHOLFinite emptyState expression

/-- Exact `Decl` equation with its cleared-locals evaluator result named. This
    preserves the exact evaluator's own locally installed memory-domain
    decision procedure, avoiding any transport assumption about the
    state-indexed `DecidablePred` instance. -/
theorem PanSemStateFiniteExact.evaluateDeclsHOLFinite_decl_clause
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [hmem : DecidablePred state.memaddrs]
    (shape : ShapeHOL) (name : MlS) (expression : ExpHOL width)
    (declarations : List (DeclHOL width)) :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite state
      (.decl shape name expression :: declarations) =
      match PanSemStateFiniteExact.evalDeclExpressionHOLFinite state expression with
      | some value =>
          if shapeEqHOL shape (shapeOfHOLExact value) then
            letI : DecidablePred
                (PanSemStateFiniteExact.setGlobalHOLFinite name value state).memaddrs := hmem
            PanSemStateFiniteExact.evaluateDeclsHOLFinite
              (PanSemStateFiniteExact.setGlobalHOLFinite name value state) declarations
          else none
      | none => none := by
  rfl

def PanSemDeclarationValueOptionRel {width : Nat} [NeZero width]
    (valueRel : PanValue (BitVec width) → ValueHOL width → Prop) :
    Option (PanValue (BitVec width)) → Option (ValueHOL width) → Prop
  | none, none => True
  | some production, some exact => valueRel production exact
  | _, _ => False

/-- Compare the global maps at byte-ranged String/MlString keys. This is the
    global component needed by the value `Decl` case; it does not identify the
    production String carrier with arbitrary HOL `mlstring` keys. -/
def PanSemDeclarationGlobalMapRel {width : Nat} [NeZero width]
    (valueRel : PanValue (BitVec width) → ValueHOL width → Prop)
    (production : VarName → Option (PanValue (BitVec width)))
    (exact : HolFiniteMapExact MlS (ValueHOL width)) : Prop :=
  ∀ name, NameRanged name →
    PanSemDeclarationValueOptionRel valueRel (production name)
      (exact.lookup (Flapjack.Basis.Pure.MlString.ofString name))

/-- The `Decl` context retains domain, exception, and function-code relations,
    adding only the ranged global-map relation that this constructor updates. -/
def PanSemDeclarationDeclContextRel {width : Nat} {σ : Type}
    [NeZero width]
    (valueRel : PanValue (BitVec width) → ValueHOL width → Prop)
    (production : PanSemDeclarationState (BitVec width) σ)
    (exact : PanSemStateFiniteExact width σ) : Prop :=
  PanSemDeclarationDomainRel production exact ∧
    PanSemDeclarationEshapeMapRel production.eshapes exact.eshapes ∧
    PanSemDeclarationCodeMapRel production.code exact.code ∧
    PanSemDeclarationGlobalMapRel valueRel production.runtime.globals exact.globals

/-- Production's executable global update and HOL's exact `FUPDATE` preserve
    the ranged global-map relation at the updated key and all other ranged
    queries. The successful values are related explicitly by `hvalue`. -/
theorem panSemDeclarationGlobalMapRel_update {width : Nat}
    [NeZero width]
    [BEq String] [LawfulBEq String]
    (valueRel : PanValue (BitVec width) → ValueHOL width → Prop)
    (production : VarName → Option (PanValue (BitVec width)))
    (exact : HolFiniteMapExact MlS (ValueHOL width))
    (name : String) (productionValue : PanValue (BitVec width))
    (exactValue : ValueHOL width)
    (hname : NameRanged name)
    (hvalue : valueRel productionValue exactValue)
    (hrel : PanSemDeclarationGlobalMapRel valueRel production exact) :
    PanSemDeclarationGlobalMapRel valueRel
      (panSemDeclUpdateGlobal production name productionValue)
      (exact.update
        (Flapjack.Basis.Pure.MlString.ofString name, exactValue)) := by
  intro query hquery
  by_cases heq : query = name
  · subst query
    rw [HolFiniteMapExact.lookup_update_pointwise]
    simp [PanSemDeclarationValueOptionRel, panSemDeclUpdateGlobal, hvalue]
  · have hkeyNe : Flapjack.Basis.Pure.MlString.ofString query ≠
        Flapjack.Basis.Pure.MlString.ofString name := by
      intro h
      apply heq
      have hk := congrArg Flapjack.Basis.Pure.MlString.toStringOfBytes h
      simpa only [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes
        query hquery, Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes
        name hname] using hk
    have hprod : panSemDeclUpdateGlobal production name productionValue query =
        production query := by
      simp [panSemDeclUpdateGlobal, heq]
    rw [hprod, HolFiniteMapExact.lookup_update_pointwise]
    simp only [if_neg hkeyNe]
    exact hrel query hquery

/-- The `Decl` constructor case of production/exact `evaluateDecls`.

    Source review: `cakeml/pancake/semantics/panSemScript.sml:817-828` clears
    locals before evaluating the expression, returns `NONE` on expression
    failure, requires `shape_of res = sh`, updates only globals on success,
    and recurses. The premises below state (rather than prove) that this
    production/exact expression pair has related optional results and that
    their carrier-specific shape tests agree. Thus this is a constructor
    congruence conditional on those facts, not an expression-evaluator
    equivalence or a complete `evaluate_decls` bridge. -/
theorem evaluateDecls_decl_prefix_congr {width : Nat} {σ : Type}
    [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)]
    [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)]
    [PanCmp (BitVec width)] [BEq String] [LawfulBEq String]
    (productionState : PanSemDeclarationState (BitVec width) σ)
    (exactState : PanSemStateFiniteExact width σ)
    [hmem : DecidablePred exactState.memaddrs]
    (shape : Shape) (name : String) (expression : Exp (BitVec width))
    (hbytes : DeclByteRanged (.decl shape name expression : Decl (BitVec width)))
    (declarations : List (DeclHOL width))
    (valueRel : PanValue (BitVec width) → ValueHOL width → Prop)
    (hcontext : PanSemDeclarationDeclContextRel valueRel productionState exactState)
    (hEval : PanSemDeclarationValueOptionRel valueRel
      (evalPanValueExp productionState.runtime.structs (fun _ => none)
        productionState.runtime.globals productionState.runtime.memory
        productionState.runtime.baseAddress productionState.runtime.topAddress
        productionState.runtime.bytesInWord expression
        (memoryAccess := some productionState.memoryAccess))
      (PanSemStateFiniteExact.evalDeclExpressionHOLFinite exactState
        (expToHOL expression)))
    (hshape : ∀ productionValue exactValue,
      valueRel productionValue exactValue →
      panShapeMatches (panValueShape productionState.runtime.structs productionValue)
        shape =
      shapeEqHOL (shapeToHOL shape) (shapeOfHOLExact exactValue))
    (htail : ∀ (production : PanSemDeclarationState (BitVec width) σ)
        (exact : PanSemStateFiniteExact width σ)
        [DecidablePred exact.memaddrs],
      PanSemDeclarationDeclContextRel valueRel production exact →
      PanSemDeclarationOutputRel (PanSemDeclarationDeclContextRel valueRel)
        (evaluateDecls production (declarations.map declOfHOL))
        (PanSemStateFiniteExact.evaluateDeclsHOLFinite exact declarations)) :
    PanSemDeclarationOutputRel (PanSemDeclarationDeclContextRel valueRel)
      (evaluateDecls productionState
        (declOfHOL (declToHOL (.decl shape name expression : Decl (BitVec width))) ::
          declarations.map declOfHOL))
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite exactState
        (declToHOL (.decl shape name expression : Decl (BitVec width)) ::
          declarations)) := by
  have hproductionCodec :
      declOfHOL (declToHOL (.decl shape name expression : Decl (BitVec width))) =
        .decl shape name expression :=
    Flapjack.Pancake.PanLang.declOfHOL_declToHOL _ hbytes
  rw [hproductionCodec]
  simp only [evaluateDecls, declToHOL]
  rw [PanSemStateFiniteExact.evaluateDeclsHOLFinite_decl_clause]
  let productionResult :=
    evalPanValueExp productionState.runtime.structs (fun _ => none)
      productionState.runtime.globals productionState.runtime.memory
      productionState.runtime.baseAddress productionState.runtime.topAddress
      productionState.runtime.bytesInWord expression
      (memoryAccess := some productionState.memoryAccess)
  let exactResult := PanSemStateFiniteExact.evalDeclExpressionHOLFinite exactState
    (expToHOL expression)
  have hresults : PanSemDeclarationValueOptionRel valueRel productionResult exactResult := by
    simpa only [productionResult] using hEval
  have hproductionEval :
      evalPanValueExp productionState.runtime.structs (fun _ => none)
        productionState.runtime.globals productionState.runtime.memory
        productionState.runtime.baseAddress productionState.runtime.topAddress
        productionState.runtime.bytesInWord expression
        (memoryAccess := some productionState.memoryAccess) = productionResult := rfl
  rw [hproductionEval]
  cases hp : productionResult with
  | none =>
      cases he : exactResult with
      | none => simp [exactResult, he,
          PanSemDeclarationOutputRel]
      | some exactValue => simp [PanSemDeclarationValueOptionRel, hp, he] at hresults
  | some productionValue =>
      cases he : exactResult with
      | none => simp [PanSemDeclarationValueOptionRel, hp, he] at hresults
      | some exactValue =>
          have hvalue : valueRel productionValue exactValue := by
            simpa [PanSemDeclarationValueOptionRel, hp, he] using hresults
          by_cases hmatch : panShapeMatches
              (panValueShape productionState.runtime.structs productionValue) shape
          · have hmatchExact : shapeEqHOL (shapeToHOL shape)
                (shapeOfHOLExact exactValue) = true := by
              rw [← hshape productionValue exactValue hvalue]
              exact hmatch
            let productionUpdated : PanSemDeclarationState (BitVec width) σ :=
              { productionState with runtime :=
                  { productionState.runtime with globals :=
                      (panSemDeclUpdateGlobal productionState.runtime.globals name
                        productionValue) } }
            let exactUpdated : PanSemStateFiniteExact width σ :=
              PanSemStateFiniteExact.setGlobalHOLFinite
                (Flapjack.Basis.Pure.MlString.ofString name) exactValue exactState
            letI : DecidablePred exactUpdated.memaddrs := hmem
            have hupdated : PanSemDeclarationDeclContextRel valueRel
                productionUpdated exactUpdated := by
              refine ⟨hcontext.1, hcontext.2.1, hcontext.2.2.1, ?_⟩
              exact panSemDeclarationGlobalMapRel_update valueRel
                productionState.runtime.globals exactState.globals name
                productionValue exactValue hbytes.2.1 hvalue hcontext.2.2.2
            have htail' := htail productionUpdated exactUpdated hupdated
            simpa [productionResult, exactResult, productionUpdated, exactUpdated,
              hp, he, hmatch, hmatchExact, PanSemDeclarationOutputRel] using htail'
          · have hmatchExact : shapeEqHOL (shapeToHOL shape)
                (shapeOfHOLExact exactValue) = false := by
              rw [← hshape productionValue exactValue hvalue]
              exact Bool.eq_false_iff.mpr hmatch
            simp [exactResult, he, hmatch, hmatchExact,
              PanSemDeclarationOutputRel]


/-! ## Executable codec relation and word/state expression arms (flapjack-rdc.1)

The production executable evaluator `evalPanValueExp` and the tagged exact
finite-support evaluator `evalHOLFinite` (tag `eval_def`) are related here for
the memory-free, map-free arms whose HOL clauses read no state beyond scalars:
`Const`, `BaseAddr`, `TopAddr`, `BytesInWord`.  The relation is the
Flapjack-specific one-way codec from exact word values to executable
`PanValue.word` values (the fragment needed to discharge the `hEval` premise of
`evaluateDecls_decl_prefix_congr` for these arms).  Memory- and map-reading arms
(`Load`/`Load32`/`LoadByte`/record/`Op` arms) are excluded and tracked
separately. -/

/-- Flapjack-specific one-way codec relation for the word-valued fragment: an
    exact `ValueHOL` word value corresponds to the executable `PanValue.word`.
    The record cases are deliberately not related here (they need the full
    `ValueHOL.toPanValue` codec and are tracked by follow-up work). -/
def PanValueCodecRel {width : Nat} [NeZero width]
    (production : PanValue (BitVec width)) (exact : ValueHOL width) : Prop :=
  match exact with
  | .val (.word word) => production = .word word
  | _ => False

@[simp] theorem panValueCodecRel_word {width : Nat} [NeZero width]
    (word : BitVec width) :
    PanValueCodecRel (.word word) (.val (.word word)) := rfl

theorem evalPanValueExp_const_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (value : BitVec width) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.const value))
      (PanSemStateFiniteExact.evalHOLFinite state (.const value) : Option (ValueHOL width)) := by
  simp only [PanSemDeclarationValueOptionRel, evalPanValueExp,
    PanSemStateFiniteExact.evalHOLFinite_const, panValueCodecRel_word]

theorem evalPanValueExp_baseAddr_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (hbase : baseAddress = state.baseAddr) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        .baseAddr)
      (PanSemStateFiniteExact.evalHOLFinite state .baseAddr : Option (ValueHOL width)) := by
  subst hbase
  simp only [PanSemDeclarationValueOptionRel, evalPanValueExp,
    PanSemStateFiniteExact.evalHOLFinite_baseAddr, panValueCodecRel_word]

theorem evalPanValueExp_topAddr_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (htop : topAddress = state.topAddr) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        .topAddr)
      (PanSemStateFiniteExact.evalHOLFinite state .topAddr : Option (ValueHOL width)) := by
  subst htop
  simp only [PanSemDeclarationValueOptionRel, evalPanValueExp,
    PanSemStateFiniteExact.evalHOLFinite_topAddr, panValueCodecRel_word]

theorem evalPanValueExp_bytesInWord_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (hbytes : bytesInWord = bytesInWordHOL width) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        .bytesInWord)
      (PanSemStateFiniteExact.evalHOLFinite state .bytesInWord : Option (ValueHOL width)) := by
  subst hbytes
  simp only [PanSemDeclarationValueOptionRel, evalPanValueExp,
    PanSemStateFiniteExact.evalHOLFinite_bytesInWord, panValueCodecRel_word]


/-- Var `Local` arm: production reads `locals name`; the exact evaluator reads
    `state.locals.lookup (ofString name)`.  The per-name relation is the
    premise, matching the ranged-key discipline of
    `PanSemDeclarationGlobalMapRel`. -/
theorem evalPanValueExp_var_local_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (name : String)
    (hlocals : PanSemDeclarationValueOptionRel PanValueCodecRel (locals name)
      (state.locals.lookup (Flapjack.Basis.Pure.MlString.ofString name))) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.var .local name))
      (PanSemStateFiniteExact.evalHOLFinite state
        (.var .local (Flapjack.Basis.Pure.MlString.ofString name))
        : Option (ValueHOL width)) := by
  simpa only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_var_local] using hlocals

/-- Var `Global` arm: production reads `globals name`; the exact evaluator reads
    `state.globals.lookup (ofString name)`.  The per-name relation is the
    premise. -/
theorem evalPanValueExp_var_global_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (name : String)
    (hglobals : PanSemDeclarationValueOptionRel PanValueCodecRel (globals name)
      (state.globals.lookup (Flapjack.Basis.Pure.MlString.ofString name))) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
        (.var .global name))
      (PanSemStateFiniteExact.evalHOLFinite state
        (.var .global (Flapjack.Basis.Pure.MlString.ofString name))
        : Option (ValueHOL width)) := by
  simpa only [evalPanValueExp, PanSemStateFiniteExact.evalHOLFinite_var_global] using hglobals

/-! ### Concrete `hEval` discharges for the `Decl` clause

`evaluateDecls_decl_prefix_congr` clears locals before evaluating the
declaration expression (production passes `fun _ => none`, the exact evaluator
uses `evalDeclExpressionHOLFinite`).  The lemmas below discharge its `hEval`
premise for the memory-free scalar and Var arms of this fragment. -/

/-- `hEval` for a `.const` declaration expression. -/
theorem evalDeclExpression_const_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width) (value : BitVec width) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs (fun _ => none) globals memory baseAddress topAddress
        bytesInWord (.const value))
      (PanSemStateFiniteExact.evalDeclExpressionHOLFinite state (.const value)) := by
  have hprod : evalPanValueExp structs (fun _ => none) globals memory baseAddress
      topAddress bytesInWord (.const value) = some (.word value) := by
    simp only [evalPanValueExp]
  have hexact : PanSemStateFiniteExact.evalDeclExpressionHOLFinite state (.const value)
      = some (.val (.word value)) := rfl
  rw [hprod, hexact]
  change PanValueCodecRel (.word value) (.val (.word value))
  exact panValueCodecRel_word value

/-- `hEval` for a `.var .local` declaration expression: the cleared locals make
    both sides `none`. -/
theorem evalDeclExpression_var_local_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width) (name : String) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs (fun _ => none) globals memory baseAddress topAddress
        bytesInWord (.var .local name))
      (PanSemStateFiniteExact.evalDeclExpressionHOLFinite state
        (.var .local (Flapjack.Basis.Pure.MlString.ofString name))) := by
  have hprod : evalPanValueExp structs (fun _ => none) globals memory baseAddress
      topAddress bytesInWord (.var .local name) = none := by
    simp only [evalPanValueExp]
  have hexact : PanSemStateFiniteExact.evalDeclExpressionHOLFinite state
      (.var .local (Flapjack.Basis.Pure.MlString.ofString name)) = none := rfl
  rw [hprod, hexact]
  trivial

/-- `hEval` for a `.var .global` declaration expression, from the ranged global
    map relation. -/
theorem evalDeclExpression_var_global_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width) (name : String)
    (hglobals : PanSemDeclarationGlobalMapRel PanValueCodecRel globals state.globals)
    (hname : NameRanged name) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs (fun _ => none) globals memory baseAddress topAddress
        bytesInWord (.var .global name))
      (PanSemStateFiniteExact.evalDeclExpressionHOLFinite state
        (.var .global (Flapjack.Basis.Pure.MlString.ofString name))) := by
  have hprod : evalPanValueExp structs (fun _ => none) globals memory baseAddress
      topAddress bytesInWord (.var .global name) = globals name := by
    simp only [evalPanValueExp]
  have hexact : PanSemStateFiniteExact.evalDeclExpressionHOLFinite state
      (.var .global (Flapjack.Basis.Pure.MlString.ofString name))
      = state.globals.lookup (Flapjack.Basis.Pure.MlString.ofString name) := rfl
  rw [hprod, hexact]
  exact hglobals name hname

/-- `hEval` for a `.baseAddr` declaration expression.  The state-address arm
    does not read locals, so clearing locals leaves both sides unchanged. -/
theorem evalDeclExpression_baseAddr_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (hbase : baseAddress = state.baseAddr) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs (fun _ => none) globals memory baseAddress topAddress
        bytesInWord (.baseAddr))
      (PanSemStateFiniteExact.evalDeclExpressionHOLFinite state (.baseAddr)) := by
  subst hbase
  have hprod : evalPanValueExp structs (fun _ => none) globals memory state.baseAddr
      topAddress bytesInWord (.baseAddr) = some (.word state.baseAddr) := by
    simp only [evalPanValueExp]
  have hexact : PanSemStateFiniteExact.evalDeclExpressionHOLFinite state (.baseAddr)
      = some (.val (.word state.baseAddr)) := rfl
  rw [hprod, hexact]
  exact panValueCodecRel_word state.baseAddr

/-- `hEval` for a `.topAddr` declaration expression (locals-independent). -/
theorem evalDeclExpression_topAddr_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (htop : topAddress = state.topAddr) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs (fun _ => none) globals memory baseAddress topAddress
        bytesInWord (.topAddr))
      (PanSemStateFiniteExact.evalDeclExpressionHOLFinite state (.topAddr)) := by
  subst htop
  have hprod : evalPanValueExp structs (fun _ => none) globals memory baseAddress
      state.topAddr bytesInWord (.topAddr) = some (.word state.topAddr) := by
    simp only [evalPanValueExp]
  have hexact : PanSemStateFiniteExact.evalDeclExpressionHOLFinite state (.topAddr)
      = some (.val (.word state.topAddr)) := rfl
  rw [hprod, hexact]
  exact panValueCodecRel_word state.topAddr

/-- `hEval` for a `.bytesInWord` declaration expression (locals-independent;
    the exact evaluator returns the canonical `bytesInWordHOL` word). -/
theorem evalDeclExpression_bytesInWord_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (hbytes : bytesInWord = bytesInWordHOL width) :
    PanSemDeclarationValueOptionRel PanValueCodecRel
      (evalPanValueExp structs (fun _ => none) globals memory baseAddress topAddress
        bytesInWord (.bytesInWord))
      (PanSemStateFiniteExact.evalDeclExpressionHOLFinite state (.bytesInWord)) := by
  subst hbytes
  have hprod : evalPanValueExp structs (fun _ => none) globals memory baseAddress
      topAddress (bytesInWordHOL width) (.bytesInWord)
      = some (.word (bytesInWordHOL width)) := by
    simp only [evalPanValueExp]
  have hexact : PanSemStateFiniteExact.evalDeclExpressionHOLFinite state (.bytesInWord)
      = some (.val (.word (bytesInWordHOL width))) := rfl
  rw [hprod, hexact]
  exact panValueCodecRel_word (bytesInWordHOL width)

/-! ## List-level correspondence for the memory-free fragment (flapjack-rdc.3)

Shared prerequisite for the `.op`/`.panOp` arms: if every argument of a
production expression list is related to its exact `expToHOL` image by
`PanSemDeclarationValueOptionRel PanValueCodecRel`, then the whole list
evaluation is related.  Untagged Flapjack-specific infrastructure. -/

/-- List-level value correspondence between the production and exact evaluators. -/
def PanSemDeclarationValueListRel {width : Nat} [NeZero width]
    (valueRel : PanValue (BitVec width) → ValueHOL width → Prop) :
    List (PanValue (BitVec width)) → List (ValueHOL width) → Prop
  | [], [] => True
  | production :: productions, exact :: exacts =>
      valueRel production exact ∧
        PanSemDeclarationValueListRel valueRel productions exacts
  | _, _ => False

theorem evalPanValueExps_list_correspondence {width : Nat} [NeZero width]
    [BEq (BitVec width)] [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    [Add (BitVec width)] [Mul (BitVec width)] [Sub (BitVec width)]
    [AndOp (BitVec width)] [OrOp (BitVec width)] [HXor (BitVec width) (BitVec width) (BitVec width)]
    [ShiftLeft (BitVec width)] [ShiftRight (BitVec width)] [LT (BitVec width)]
    [DecidableRel (fun left right : BitVec width => left < right)] [PanCmp (BitVec width)]
    (state : PanSemStateFiniteExact width Unit) [_hmem : DecidablePred state.memaddrs]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue (BitVec width)))
    (memory : BitVec width → Option (PanValue (BitVec width)))
    (baseAddress topAddress bytesInWord : BitVec width)
    (access : Option (PanValueMemoryAccess (BitVec width)))
    (expressions : List (Exp (BitVec width)))
    (values : List (PanValue (BitVec width)))
    (hprod : evalPanValueExp.evalPanValueExps structs locals globals memory baseAddress
        topAddress bytesInWord expressions (memoryAccess := access) = some values)
    (hexp : ∀ e ∈ expressions,
      PanSemDeclarationValueOptionRel PanValueCodecRel
        (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord e
          (memoryAccess := access))
        (state.evalHOLFinite (expToHOL e))) :
    ∃ exacts : List (ValueHOL width),
      state.evalListHOLFinite (expressions.map expToHOL) = some exacts ∧
        PanSemDeclarationValueListRel PanValueCodecRel values exacts := by
  induction expressions generalizing values with
  | nil =>
      simp only [evalPanValueExp.evalPanValueExps, Option.some.injEq] at hprod
      subst hprod
      refine ⟨[], ?_, ?_⟩
      · simp only [List.map_nil, PanSemStateFiniteExact.evalListHOLFinite, evalListHOLExact]
      · exact trivial
  | cons expression expressions ih =>
      have hhead := hexp expression List.mem_cons_self
      have htail : ∀ e ∈ expressions,
          PanSemDeclarationValueOptionRel PanValueCodecRel
            (evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord e
              (memoryAccess := access))
            (state.evalHOLFinite (expToHOL e)) :=
        fun e he => hexp e (List.mem_cons_of_mem expression he)
      simp only [evalPanValueExp.evalPanValueExps] at hprod
      cases h1 : evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
          expression (memoryAccess := access) with
      | none => rw [h1] at hprod; exact absurd hprod (by simp)
      | some pv =>
          cases h2 : evalPanValueExp.evalPanValueExps structs locals globals memory baseAddress
              topAddress bytesInWord expressions (memoryAccess := access) with
          | none => rw [h1, h2] at hprod; exact absurd hprod (by simp)
          | some rest =>
              rw [h1, h2] at hprod
              simp at hprod
              subst hprod
              cases h3 : state.evalHOLFinite (expToHOL expression) with
              | none =>
                  rw [h1, h3] at hhead
                  simp only [PanSemDeclarationValueOptionRel] at hhead
              | some ev =>
                  rw [h1, h3] at hhead
                  simp only [PanSemDeclarationValueOptionRel] at hhead
                  obtain ⟨exacts, hexactList, hrelList⟩ := ih rest h2 htail
                  refine ⟨ev :: exacts, ?_, ⟨hhead, hrelList⟩⟩
                  rw [List.map_cons]
                  rw [PanSemStateFiniteExact.evalHOLFinite_eq_toExact] at h3
                  rw [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact] at hexactList
                  simp only [PanSemStateFiniteExact.evalListHOLFinite, evalListHOLExact, h3,
                    hexactList]

/-! ### Word-projection helpers for the Op arm (flapjack-rdc.3.2) -/

/-- The executable/exact value codec holds only for word payloads (forward
    direction). -/
theorem panValueCodecRel_exists_word {width : Nat} [NeZero width]
    (production : PanValue (BitVec width)) (exact : ValueHOL width)
    (h : PanValueCodecRel production exact) :
    ∃ word : BitVec width, production = .word word ∧ exact = .val (.word word) := by
  cases exact with
  | val wrapper =>
      cases wrapper with
      | word word => exact ⟨word, h, rfl⟩
  | rStruct fields => change False at h; exact h.elim
  | nStruct name fields => change False at h; exact h.elim

/-- Every exact value related to an executable value is a word. -/
theorem panSemDeclarationValueListRel_all_valueIsWord {width : Nat} [NeZero width] :
    ∀ (productions : List (PanValue (BitVec width))) (exacts : List (ValueHOL width)),
      PanSemDeclarationValueListRel PanValueCodecRel productions exacts →
      exacts.all valueIsWord = true := by
  intro productions
  induction productions with
  | nil =>
      intro exacts h
      cases exacts with
      | nil => rfl
      | cons exact restE => change False at h; exact h.elim
  | cons production rest ih =>
      intro exacts h
      cases exacts with
      | nil => change False at h; exact h.elim
      | cons exact restE =>
          simp only [PanSemDeclarationValueListRel] at h
          obtain ⟨hhead, htail⟩ := h
          obtain ⟨word, hpw, hexw⟩ := panValueCodecRel_exists_word production exact hhead
          subst hpw
          subst hexw
          simp only [List.all_cons, valueIsWord, Bool.true_and]
          exact ih restE htail

/-- Projecting the executable values to words agrees with the exact `valueWord`
    list. -/
theorem panSemDeclarationValueListRel_mapM_projection {width : Nat} [NeZero width] :
    ∀ (productions : List (PanValue (BitVec width))) (exacts : List (ValueHOL width)),
      PanSemDeclarationValueListRel PanValueCodecRel productions exacts →
      productions.mapM panValueWordProjection = some (exacts.map valueWord) := by
  intro productions
  induction productions with
  | nil =>
      intro exacts h
      cases exacts with
      | nil => rfl
      | cons exact restE => change False at h; exact h.elim
  | cons production rest ih =>
      intro exacts h
      cases exacts with
      | nil => change False at h; exact h.elim
      | cons exact restE =>
          simp only [PanSemDeclarationValueListRel] at h
          obtain ⟨hhead, htail⟩ := h
          obtain ⟨word, hpw, hexw⟩ := panValueCodecRel_exists_word production exact hhead
          subst hpw
          subst hexw
          simp only [List.mapM_cons, panValueWordProjection, valueWord, List.map_cons]
          rw [ih restE htail]
          rfl

end Flapjack
