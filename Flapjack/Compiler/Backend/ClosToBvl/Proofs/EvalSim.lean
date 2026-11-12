module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Semantics

@[expose] public section

/-! Representation infrastructure for the closure-to-BVL evaluation simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

private abbrev SimulationTail (C₁ C₂ : Type) := ClosSem.CompileOracle C₁ →
  ClosSem.Compiler C₁ → List ClosLang.Exp → Spt (Nat × Bvl.Exp) →
  BvlSem.CompileOracle C₂ → BvlSem.Compiler C₂ → Nat → Prop

private abbrev RawCode := Nat → Option (Nat × ClosLang.Exp)

private abbrev RawCodeSupport (lookup : RawCode) :=
  ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys

private def toBroad (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : RawCode :=
  code.lookup

private def ofBroad (lookup : RawCode) (support : RawCodeSupport lookup) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, support⟩

private def toBroadPredicate {C₁ C₂ : Type}
    (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → SimulationTail C₁ C₂)
    (lookup : RawCode) (support : RawCodeSupport lookup) : SimulationTail C₁ C₂ :=
  rel (ofBroad lookup support)

private def fromBroadPredicate {C₁ C₂ : Type}
    (rel : (lookup : RawCode) → RawCodeSupport lookup → SimulationTail C₁ C₂)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : SimulationTail C₁ C₂ :=
  rel (toBroad code) code.finiteSupport

/-- The two views transport an arbitrary simulation relation in both directions.
This is Flapjack representation infrastructure for the higher-order map argument
of `eval_sim`, rather than a separate HOL declaration. -/
theorem simulationPredicateRoundtrips {C₁ C₂ : Type} :
    (∀ (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → SimulationTail C₁ C₂)
      (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)),
      fromBroadPredicate (toBroadPredicate rel) code = rel code) ∧
    (∀ (rel : (lookup : RawCode) → RawCodeSupport lookup → SimulationTail C₁ C₂)
      (lookup : RawCode) (support : RawCodeSupport lookup),
      toBroadPredicate (fromBroadPredicate rel) lookup support = rel lookup support) := by
  constructor
  · intro rel code
    cases code
    rfl
  · intro rel lookup support
    rfl

/-- The canonical source-code map roundtrips through its lookup view. -/
theorem holFmapAsFiniteSupportParamWitness_evalSim_code1
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code1) code1.finiteSupport).lookup key = code1.lookup key ∧
    (ofBroad (toBroad code1) code1.finiteSupport).finiteSupport = code1.finiteSupport ∧
    ofBroad (toBroad code1) code1.finiteSupport = code1 := by
  cases code1
  exact ⟨rfl, rfl, rfl⟩

/-- The original parameterized forward simulation of closure evaluation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "eval_sim_def"
  (fmap_as_finite_support_parameter_predicate_domain := [code1, rel])]
def evalSim {C₁ C₂ F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (co1 : ClosSem.CompileOracle C₁)
    (cc1 : ClosSem.Compiler C₁) (es1 : List ClosLang.Exp) (code2 : Spt (Nat × Bvl.Exp))
    (co2 : BvlSem.CompileOracle C₂) (cc2 : BvlSem.Compiler C₂) (start : Nat)
    (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → ClosSem.CompileOracle C₁ →
      ClosSem.Compiler C₁ → List ClosLang.Exp → Spt (Nat × Bvl.Exp) →
      BvlSem.CompileOracle C₂ → BvlSem.Compiler C₂ → Nat → Prop) : Prop :=
  ∀ (k : Nat) (res1 : Result (List ClosSem.Value) ClosSem.Value) (s2 : ClosSem.State C₁ F),
    ClosSem.evaluate es1 [] (ClosSem.initialState ffi maxApp code1 co1 cc1 k) = (res1, s2) ∧
    res1 ≠ .err (.abort .typeError) ∧ rel code1 co1 cc1 es1 code2 co2 cc2 start →
    ∃ (ck : Nat) (res2 : Result (List BvlSem.Value) BvlSem.Value) (t2 : BvlSem.State C₂ F),
      BvlSem.evaluate [.call 0 (some start) []] []
        (BvlSem.initialState ffi code2 co2 cc2 (k + ck)) = (res2, t2) ∧
      resultRel (fun _ _ => True) (fun _ _ => True) res1 res2 ∧ s2.ffi = t2.ffi

/-- The source-code map roundtrip also witnesses the semantics theorem parameter. -/
theorem holFmapAsFiniteSupportParamWitness_impSemanticsEq_code1
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code1) code1.finiteSupport).lookup key = code1.lookup key ∧
    (ofBroad (toBroad code1) code1.finiteSupport).finiteSupport = code1.finiteSupport ∧
    ofBroad (toBroad code1) code1.finiteSupport = code1 :=
  holFmapAsFiniteSupportParamWitness_evalSim_code1 code1 key

/-- A nonfailing source and an applicable forward simulation have equal behavior. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "IMP_semantics_eq"
  (fmap_as_finite_support_parameter_predicate_domain := [code1, rel])]
theorem impSemanticsEq {C₁ C₂ F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (co1 : ClosSem.CompileOracle C₁)
    (cc1 : ClosSem.Compiler C₁) (es1 : List ClosLang.Exp) (code2 : Spt (Nat × Bvl.Exp))
    (co2 : BvlSem.CompileOracle C₂) (cc2 : BvlSem.Compiler C₂) (start : Nat)
    (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → ClosSem.CompileOracle C₁ →
      ClosSem.Compiler C₁ → List ClosLang.Exp → Spt (Nat × Bvl.Exp) →
      BvlSem.CompileOracle C₂ → BvlSem.Compiler C₂ → Nat → Prop)
    (h : evalSim ffi maxApp code1 co1 cc1 es1 code2 co2 cc2 start rel ∧
      ClosSem.semantics ffi maxApp code1 co1 cc1 es1 ≠ .fail)
    (relation : rel code1 co1 cc1 es1 code2 co2 cc2 start) :
    BvlSem.semantics ffi code2 co2 cc2 start = ClosSem.semantics ffi maxApp code1 co1 cc1 es1 := by
  apply semantics_eq_of_initialSimulation ffi maxApp code1 co1 cc1 es1 code2 co2 cc2 start h.2
  intro clock result final run safe
  exact h.1 clock result final ⟨run, safe, relation⟩

end Flapjack.Compiler.Backend.ClosToBvl
