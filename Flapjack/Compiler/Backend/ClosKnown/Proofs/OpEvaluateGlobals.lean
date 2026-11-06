import Flapjack.Compiler.Backend.ClosKnown.Proofs.UniqueGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.OpGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateGlobalsApprox

/-! Global approximations after evaluating primitive-operation arguments. -/
namespace Flapjack.Compiler.Backend.ClosKnown.OpEvaluateGlobals
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Changes to the approximation tree are restricted to a set of indices. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "gapprox_extend_def"]
def gapproxExtend {α : Type} (g1 : Spt α) (gd : Set Nat) (g2 : Spt α) : Prop :=
  ∀ i, sptMem i g2 ∧ (sptMem i g1 → sptLookup i g2 ≠ sptLookup i g1) → i ∈ gd

/-- Disjoint concrete and abstract extensions preserve a global approximation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_disjoint_extends"
  (fmap_as_finite_support := [refs, code])]
theorem stateGlobalsApproxDisjointExtends {C₁ F₁ C₂ F₂ : Type}
    (s1 : State C₁ F₁) (mgx : Set Nat) (s2 : State C₂ F₂)
    (g1 : Spt ValApprox) (gax : Set Nat) (g2 : Spt ValApprox)
    (h : mglobalsExtend s1.globals mgx s2.globals ∧ gapproxExtend g1 gax g2 ∧
      Disjoint (mappedGlobals s1.globals) gax ∧ Disjoint gax mgx ∧
      stateGlobalsApprox s2 g1) : stateGlobalsApprox s2 g2 := by
  rcases h with ⟨extension, approxExtension, oldDisjoint, newDisjoint, approx⟩
  intro key value a ⟨found, lookup⟩
  by_cases same : sptLookup key g2 = sptLookup key g1
  · exact approx key value a ⟨found, same.symm.trans lookup⟩
  · have member : sptMem key g2 := (sptMem_iff_lookup key g2).2 ⟨a, lookup⟩
    have abstractWrite : key ∈ gax := approxExtension key ⟨member, fun _ => same⟩
    have concrete : key ∈ mappedGlobals s2.globals := ⟨value, found⟩
    rcases extension.1 concrete with old | new
    · exact False.elim ((Set.disjoint_left.mp oldDisjoint) old abstractWrite)
    · exact False.elim ((Set.disjoint_left.mp newDisjoint) abstractWrite new)

/-- Evaluation of an operation's arguments preserves the resulting global
approximation when operation writes are unique and initially disjoint. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_known_op_evaluate"
  (fmap_as_finite_support := [refs, code])]
theorem stateGlobalsApproxKnownOpEvaluate {C F : Type}
    (xs : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : State C F) (opn : ClosLang.Op)
    (aargs : List ValApprox) (g0 : Spt ValApprox) (ea : ValApprox) (g : Spt ValApprox)
    (tr : BackendCommon.Tra)
    (h : evaluate xs env s0 = (res, s) ∧ knownOpHOL opn aargs g0 = (ea, g) ∧
      ssgcFree s0 ∧ (∀ v ∈ env, vsgcFree v) ∧ (∀ e ∈ xs, esgcFree e) ∧
      Disjoint (mappedGlobals s0.globals) {k | opGlobalBag opn k ≠ 0} ∧
      uniqueSetGlobals [.op tr opn xs] s0.compileOracle ∧ stateGlobalsApprox s g0) :
    stateGlobalsApprox s g := by
  rcases h with ⟨run, known, safe, envSafe, expSafe, disjoint, unique, approx⟩
  obtain ⟨_, _, n, _, frame⟩ :=
    EvaluateGlobalsPort.Total.evaluateChangedGlobals xs env s0 res s ⟨run, safe, expSafe, envSafe⟩
  intro key value a ⟨found, lookup⟩
  rcases knownOpChangedGlobalsCases opn aargs g0 ea g known key a lookup with old | written
  · exact approx key value a ⟨found, old⟩
  · have count := unique n key
    simp only [elistGlobals_append, elistGlobals, setGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero] at count
    have outside : key ∉ ({k | elistGlobals xs k ≠ 0} ∪
        {k | elistGlobals (List.flatten (firstNExps s0.compileOracle n)) k ≠ 0}) := by
      intro member
      rcases member with member | member
      · change elistGlobals xs key ≠ 0 at member
        omega
      · change elistGlobals (List.flatten (firstNExps s0.compileOracle n)) key ≠ 0 at member
        omega
    have before := frame.2 key value ⟨found, outside⟩
    exact False.elim ((Set.disjoint_left.mp disjoint) ⟨value, before⟩ written)

end Flapjack.Compiler.Backend.ClosKnown.OpEvaluateGlobals
