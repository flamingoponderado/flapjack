import Mathlib.Data.Set.Disjoint
import Flapjack.Compiler.Backend.ClosKnown.Proofs.EvaluateGlobalsTotal

/-! Uniqueness and preservation of global writes across oracle programs. -/
namespace Flapjack.Compiler.Backend.ClosKnown.UniqueGlobalsPort
open ClosSem ClosProps ClosProps.StateGlobalSafety
open Flapjack.SemanticPrimitivesHOL
open FlatProps (emptyGlobalBag)

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Program writes and all finite prefixes of oracle-program writes are
unique, with arbitrary oracle configuration and auxiliary carriers. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "unique_set_globals_def"]
def uniqueSetGlobals {α β : Type} (es : List ClosLang.Exp)
    (co : Nat → α × List ClosLang.Exp × β) : Prop :=
  ∀ n k, elistGlobals (es ++ (firstNExps co n).flatten) k ≤ 1

/-- Shifting an oracle preserves uniqueness of program and oracle writes. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "unique_set_globals_shift_seq"]
theorem uniqueSetGlobalsShift {α β : Type} (es : List ClosLang.Exp)
    (co : Nat → α × List ClosLang.Exp × β) (unique : uniqueSetGlobals es co) :
    ∀ k, uniqueSetGlobals es (Flapjack.holShiftSeq k co) := by
  intro k n index
  have bound := unique (n + k) index
  rw [firstNExpsShiftSeq] at bound
  simp only [List.flatten_append, elistGlobals_append] at bound ⊢
  omega

/-- Uniqueness includes the original program's own write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "unique_set_globals_IMP_es_distinct_elist_globals"]
theorem uniqueSetGlobalsDistinct {α β : Type} (es : List ClosLang.Exp)
    (co : Nat → α × List ClosLang.Exp × β) (unique : uniqueSetGlobals es co) :
    ∀ k, elistGlobals es k ≤ 1 := by
  intro k
  have bound := unique 0 k
  simpa [firstNExps] using bound

/-- Removing the initial program preserves uniqueness of future oracle writes. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "nil_unique_set_globals"]
theorem nilUniqueSetGlobals {α β : Type} (es : List ClosLang.Exp)
    (co : Nat → α × List ClosLang.Exp × β) (unique : uniqueSetGlobals es co) :
    uniqueSetGlobals [] co := by
  intro n k
  have bound := unique n k
  simp only [elistGlobals_append] at bound
  simpa using Nat.le_trans (Nat.le_add_left _ _) bound

/-- Initialized globals do not intersect the expressions' write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "mglobals_disjoint_def"]
def mglobalsDisjoint {α : Type} (globals : List (Option α)) (xs : List ClosLang.Exp) : Prop :=
  Disjoint (mappedGlobals globals) {k | elistGlobals xs k ≠ 0}

/-- Safe evaluation preserves disjointness from another expression list when
the expressions and future oracle programs have unique global writes. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "mglobals_disjoint_evaluate"
  (fmap_as_finite_support := [refs, code])]
theorem mglobalsDisjointEvaluate {C F : Type} (s0 : ClosSem.State C F)
    (xs ys : List ClosLang.Exp) (env : List ClosSem.Value)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State C F)
    (h : evaluate ys env s0 = (res, s) ∧ ssgcFree s0 ∧
      (∀ v ∈ env, vsgcFree v) ∧ (∀ e ∈ ys, esgcFree e) ∧
      uniqueSetGlobals (xs ++ ys) s0.compileOracle ∧ mglobalsDisjoint s0.globals xs) :
    mglobalsDisjoint s.globals xs := by
  rcases h with ⟨run, safe, envSafe, expressionsSafe, unique, disjoint⟩
  have ⟨_, _, n, _, frame⟩ :=
    EvaluateGlobalsPort.Total.evaluateChangedGlobals ys env s0 res s ⟨run, safe, expressionsSafe, envSafe⟩
  apply Set.disjoint_left.mpr
  intro key mapped written
  rcases frame.1 mapped with old | new
  · exact (Set.disjoint_left.mp disjoint) old written
  · have count := unique n key
    simp only [elistGlobals_append] at count
    change elistGlobals xs key ≠ 0 at written
    rcases new with new | new
    · change elistGlobals ys key ≠ 0 at new
      omega
    · change elistGlobals (List.flatten (firstNExps s0.compileOracle n)) key ≠ 0 at new
      omega

end Flapjack.Compiler.Backend.ClosKnown.UniqueGlobalsPort
