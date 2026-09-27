import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.PanLang.Decl

/-!
This module records constructor-level production/exact congruence for the HOL
`Name` and `ExnDecl` clauses without claiming the still-missing relation
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
    ShapeHOL isWfShapeExactHOL shapeToHOL)

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

end Flapjack
