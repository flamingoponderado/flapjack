module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeInvariant
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateOracleAdvance
@[expose] public section

/-! Preservation of included compiler-oracle states by closure evaluation. -/
namespace Flapjack.Compiler.Backend.ClosCall.OracleIncludes
open Flapjack ClosSem ClosCall

/-- Canonical finite-map roundtrip for the closure state carrier. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- An oracle state present after evaluation was already present before it. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "evaluate_includes_state"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_includesState {A B C D : Type} (xs : List ClosLang.Exp) (env : List Value)
    (s : ClosSem.State (A × B) C) (res : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (s1 : ClosSem.State (A × B) C) (g1 : A × D)
    (h : includesState g1 s1.compileOracle ∧ evaluate xs env s = (res, s1)) :
    includesState g1 s.compileOracle := by
  obtain ⟨n, shifted⟩ := evaluate_oracle_advance.1 xs env s s1 res h.2
  obtain ⟨k, found⟩ := h.1
  refine ⟨k + n, ?_⟩
  simpa [shifted, holShiftSeq] using found

/-- An oracle state present after application was already present before it.
The original two unused quantified parameters retain independent types. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "evaluate_app_includes_state"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApp_includesState {A B C D X Y : Type} (loco : Option Nat) (x : Value) (vs : List Value)
    (_xs : X) (_env : Y) (s : ClosSem.State (A × B) C)
    (res : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (s1 : ClosSem.State (A × B) C) (g1 : A × D)
    (h : includesState g1 s1.compileOracle ∧ evaluateApp loco x vs s = (res, s1)) :
    includesState g1 s.compileOracle := by
  obtain ⟨n, shifted⟩ := evaluate_oracle_advance.2 (s.clock + 1) loco x vs s s1 res (Nat.lt_succ_self _) h.2
  obtain ⟨k, found⟩ := h.1
  refine ⟨k + n, ?_⟩
  simpa [shifted, holShiftSeq] using found
end Flapjack.Compiler.Backend.ClosCall.OracleIncludes
