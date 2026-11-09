module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateRelation
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.PreserveSafetyTotal

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section


/-! Oracle invariants of known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation.Oracle
open ClosSem ClosProps ClosProps.StateGlobalSafety BackendProps UniqueGlobalsPort
open Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation

/-- Each oracle entry carries a globally safe approximation tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_state_sgc_free_def"]
def oracleStateSgcFree {Index C P : Type} (co : Index → (Spt ValApprox × C) × P) : Prop :=
  ∀ n, globalsApproxSgcFree (co n).1.1

/-- Shifting an oracle retains global approximation safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "oracle_state_sgc_free_shift_seq"]
theorem oracleStateSgcFreeShift {C P : Type} (co : Nat → (Spt ValApprox × C) × P)
    (safe : oracleStateSgcFree co) : ∀ n, oracleStateSgcFree (Flapjack.holShiftSeq n co) := by
  intro n i
  exact safe (i + n)

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Related states' oracle programs do not gain global writes under the
optimizer, when the source state and oracle approximations are safe. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_rel_co_elist_globals"
  (fmap_as_finite_support := [refs, code])]
theorem stateRelCoElistGlobals {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (n : Nat)
    (h : StateRel c g s t ∧ ssgcFree s ∧ oracleStateSgcFree s.compileOracle) :
    ∀ i, elistGlobals (t.compileOracle n).2.1 i ≤ elistGlobals (s.compileOracle n).2.1 i := by
  obtain ⟨related, safe, oracleSafe⟩ := h
  have equation := related.2.2.2.2.2.2.2.2.2.2
  have expressionSafe := (safe.2.2.2.2 n (s.compileOracle n).2.1 (s.compileOracle n).2.2 rfl).1
  cases hk : knownListTotal (resetInlineFactor c) (s.compileOracle n).2.1 []
      (s.compileOracle n).1.1 with
  | mk eas next =>
    have bound := PreserveSafety.knownElglobalsDontGrow (resetInlineFactor c)
      (s.compileOracle n).2.1 [] (s.compileOracle n).1.1 eas next
      ⟨hk, expressionSafe, by simp, oracleSafe n⟩
    simpa [equation, stateCo, compileInc, hk] using bound

/-- An oracle prefix of optimized programs does not gain global writes. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_rel_first_n_exps"
  (fmap_as_finite_support := [refs, code])]
theorem stateRelFirstNExps {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (n : Nat)
    (h : StateRel c g s t ∧ ssgcFree s ∧ oracleStateSgcFree s.compileOracle) :
    ∀ i, elistGlobals (List.flatten (firstNExps t.compileOracle n)) i ≤
      elistGlobals (List.flatten (firstNExps s.compileOracle n)) i := by
  induction n with
  | zero => simp [firstNExps, elistGlobals, FlatProps.emptyGlobalBag, Flapjack.emptyBag]
  | succ n ih =>
    have step := stateRelCoElistGlobals c g s t n h
    have ts := firstNExpsShiftSeq t.compileOracle 1 n
    have ss := firstNExpsShiftSeq s.compileOracle 1 n
    simp only [Nat.add_comm 1 n] at ts ss
    rw [ts, ss]
    simp [firstNExps, Flapjack.holShiftSeq, elistGlobals_append] at ih step ⊢
    intro i
    exact Nat.add_le_add (ih i) (step i)

/-- Unique global writes transfer to the optimized oracle. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_rel_unique_set_globals"
  (fmap_as_finite_support := [refs, code])]
theorem stateRelUniqueSetGlobals {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (xs : List ClosLang.Exp)
    (h : StateRel c g s t ∧ ssgcFree s ∧ oracleStateSgcFree s.compileOracle ∧
      uniqueSetGlobals xs s.compileOracle) : uniqueSetGlobals xs t.compileOracle := by
  obtain ⟨related, safe, oracleSafe, unique⟩ := h
  intro n i
  have bound := stateRelFirstNExps c g s t n ⟨related, safe, oracleSafe⟩ i
  have source := unique n i
  simp only [elistGlobals_append] at source ⊢
  omega

end Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation.Oracle
