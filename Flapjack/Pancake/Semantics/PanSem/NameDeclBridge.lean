import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
The production and exact finite-support clauses for HOL `Name` declarations
are both no-ops. This module records that constructor-level congruence without
claiming the still-missing relation between the full production and exact
state carriers.

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
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
  (DeclHOL declOfHOL declToHOL DeclByteRanged MlS ShapeHOL)

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
