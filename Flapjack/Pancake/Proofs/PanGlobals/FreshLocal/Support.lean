module

public import Flapjack.Pancake.Proofs.PanGlobals
public import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

@[expose] public section

/-!
# Shared finite-map and expression helpers for the `evaluate_fresh_local` cases

The per-constructor `FreshLocal` case modules (and `CompileCorrect/ShMemGlobal`)
used verbatim private copies of these helpers. They are Flapjack-specific
infrastructure over the canonical finite-map carriers, with no HOL original.
-/

namespace Flapjack.PanGlobalsFreshLocalSupport

open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Flapjack-only equality of the two canonical update interfaces. -/
theorem updateEq_eq_update {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (entry : MlS × ValueHOL width) :
    locals.updateEq entry = locals.update entry := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_update,
    FUPDATE_HOL_eq_FUPDATE]

/-- Flapjack-only transport of the reviewed local update to literal HOL equality. -/
theorem setVarEq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width) :
    setVarHOLFinite name value state = {state with locals := state.locals.updateEq (name,value)} := by
  simp only [setVarHOLFinite, updateEq_eq_update]

/-- Flapjack-specific transport of existing broad expression freshness through
the canonical state codec. The domain decision is internal, not a premise. -/
theorem evalFreshUpdate {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width)
    (expression : ExpHOL width) (h : name ∉ varExpHOL expression) :
    @evalHOLExact width σ _
      ({state with locals := state.locals.updateEq (name, value)} :
        PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
    @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression := by
  classical
  have hlookup : (state.locals.updateEq (name, value)).lookup =
      FUPDATE_HOL state.locals.lookup (name, value) := by
    funext key
    exact HolFiniteMapExact.lookup_updateEq _ _ _
  simpa only [toExact_setLocals, hlookup] using
    (@evalHOLExact_updLocals_not_mem width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) name value expression h)

/-- Flapjack-specific transport of existing broad expression-list freshness
through the canonical state codec, for the list-valued evaluator. -/
theorem evalFreshUpdateList {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width)
    (expression : List (ExpHOL width)) (h : name ∉ (expression.map varExpHOL).flatten) :
    @evalListHOLExact width σ _
      ({state with locals := state.locals.updateEq (name, value)} :
        PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
    @evalListHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression := by
  classical
  have hlookup : (state.locals.updateEq (name, value)).lookup =
      FUPDATE_HOL state.locals.lookup (name, value) := by
    funext key
    exact HolFiniteMapExact.lookup_updateEq _ _ _
  simpa only [toExact_setLocals, hlookup] using
    (@evalListHOLExact_updLocals_not_mem width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) name value expression h)

/-- Flapjack-only pointwise map algebra: independent updates commute. -/
theorem updateCommute {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (a b : MlS)
    (x y : ValueHOL width) (hne : a ≠ b) :
    (locals.updateEq (a,x)).updateEq (b,y) =
      (locals.updateEq (b,y)).updateEq (a,x) := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases ha : key = a <;> by_cases hb : key = b <;>
    simp_all [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- Flapjack-only pointwise map algebra for restoring a distinct binding. -/
theorem restoreCommute {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (a b : MlS)
    (x : ValueHOL width) (old : Option (ValueHOL width)) (hne : a ≠ b) :
    HolFiniteMapExact.resVarEq (locals.updateEq (a,x)) (b,old) =
      (HolFiniteMapExact.resVarEq locals (b,old)).updateEq (a,x) := by
  apply HolFiniteMapExact.ext
  funext key
  cases old <;> by_cases ha : key = a <;> by_cases hb : key = b <;>
    simp_all [HolFiniteMapExact.lookup_resVarEq_none, HolFiniteMapExact.lookup_resVarEq_some,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, FDOMSUB_HOL]

/-- Canonical Boolean/equality update commutation; local infrastructure. -/
theorem updateMixed {width : Nat} [NeZero width] (map : HolFiniteMapExact MlS (ValueHOL width))
    (a b : MlS) (x y : ValueHOL width) (hne : a ≠ b) :
    (map.updateEq (a, x)).update (b, y) = (map.update (b, y)).updateEq (a, x) := by
  have he := FUPDATE_comm map.lookup a x b y hne
  cases map
  simp only [HolFiniteMapExact.update, HolFiniteMapExact.updateEq, FUPDATE_HOL_eq_FUPDATE]
  congr 1

end Flapjack.PanGlobalsFreshLocalSupport
