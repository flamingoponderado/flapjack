module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.OracleGlobals
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Relations
public import Flapjack.Misc.Sptree.Subspt

@[expose] public section


/-! Monotonic approximation trees carried by compiler oracles. -/
namespace Flapjack.Compiler.Backend.ClosKnown.OracleMonotonic
open ClosSem OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- Each oracle approximation is a subtree of its successor. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_subspt_def"]
def oracleGapproxSubspt {A B C : Type} (co : Nat → (Spt A × B) × C) : Prop :=
  ∀ n, sptSubspt (co n).1.1 (co (n + 1)).1.1

/-- Sparse-tree inclusion is reflexive. This is Flapjack infrastructure. -/
private theorem subsptRefl {A : Type} (s : Spt A) : sptSubspt s s := by
  intro k member
  exact ⟨member, rfl⟩

/-- Successor monotonicity is equivalent to monotonicity over arbitrary
nonnegative offsets. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_subspt_add"]
theorem oracleGapproxSubsptAdd {A B C : Type} (co : Nat → (Spt A × B) × C) :
    oracleGapproxSubspt co ↔ ∀ n k, sptSubspt (co n).1.1 (co (n + k)).1.1 := by
  constructor
  · intro mono n k
    induction k with
    | zero => simpa using subsptRefl (co n).1.1
    | succ k ih =>
      have step := mono (n + k)
      exact sptSubsptTrans _ _ _ ⟨ih, by simpa [Nat.add_assoc] using step⟩
  · intro all n
    exact all n 1

/-- An earlier oracle approximation is included in any later one. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_subspt_alt"]
theorem oracleGapproxSubsptAlt {A B C : Type} (co : Nat → (Spt A × B) × C) (n k : Nat)
    (h : oracleGapproxSubspt co ∧ n ≤ k) : sptSubspt (co n).1.1 (co k).1.1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.2
  exact (oracleGapproxSubsptAdd co).1 h.1 n d

/-- Shifting preserves monotonic oracle approximations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_subspt_shift_seq"]
theorem oracleGapproxSubsptShift {A B C : Type} (co : Nat → (Spt A × B) × C)
    (h : oracleGapproxSubspt co) : ∀ k, oracleGapproxSubspt (Flapjack.holShiftSeq k co) := by
  intro k n
  simpa [Flapjack.holShiftSeq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (n + k)

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Evaluation preserves monotonic oracle approximations. The original typed
statement includes an independent, unused first quantified variable. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_gapprox_subspt_evaluate"
  (fmap_as_finite_support := [refs, code])]
theorem oracleGapproxSubsptEvaluate {U A C F : Type} (_unused : U)
    (xs : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : State (Spt A × C) F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : State (Spt A × C) F)
    (h : oracleGapproxSubspt s0.compileOracle ∧ evaluate xs env s0 = (res, s)) :
    oracleGapproxSubspt s.compileOracle := by
  obtain ⟨n, shift⟩ := evaluateImpShiftSeq xs env s0 res s h.2
  rw [shift]
  exact oracleGapproxSubsptShift s0.compileOracle h.1 n

/-- Evaluation advances the current approximation tree within a monotonic
oracle. This is Flapjack infrastructure for the semantic simulation. -/
theorem nextGEvaluateSubspt {C F : Type} (xs : List ClosLang.Exp) (env : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : oracleGapproxSubspt s0.compileOracle ∧ evaluate xs env s0 = (res, s)) :
    sptSubspt (Relations.nextG s0) (Relations.nextG s) := by
  obtain ⟨n, shift⟩ := evaluateImpShiftSeq xs env s0 res s h.2
  have sub := oracleGapproxSubsptAlt s0.compileOracle 0 n ⟨h.1, Nat.zero_le n⟩
  simpa [Relations.nextG, shift, Flapjack.holShiftSeq] using sub

/-- Every oracle program and auxiliary body has no closure-capture
annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "co_every_Fn_vs_NONE_def"]
def coEveryFnVarsNone {Index A B C : Type}
    (co : Index → A × List ClosLang.Exp × List (B × C × ClosLang.Exp)) : Prop :=
  ∀ n es aux, (co n).2 = (es, aux) →
    ClosProps.everyFnVarsNone es ∧ ClosProps.everyFnVarsNone (aux.map (fun entry => entry.2.2))

/-- Shifting an oracle preserves the closure-annotation condition. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "co_every_Fn_vs_NONE_shift_seq"]
theorem coEveryFnVarsNoneShift {A B C : Type}
    (co : Nat → A × List ClosLang.Exp × List (B × C × ClosLang.Exp))
    (h : coEveryFnVarsNone co) : ∀ n, coEveryFnVarsNone (Flapjack.holShiftSeq n co) := by
  intro n i es aux eq
  exact h (i + n) es aux eq

end Flapjack.Compiler.Backend.ClosKnown.OracleMonotonic
