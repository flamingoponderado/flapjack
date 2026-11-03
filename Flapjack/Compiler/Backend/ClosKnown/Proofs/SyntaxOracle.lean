import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateOracle
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Syntax
import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
import Flapjack.Compiler.Backend.BackendProps.Pure
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Syntax

/-! Source syntax and oracle preconditions for the known-function pass. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps BackendProps
open Relations.StateRelation.Oracle PreserveSafety

/-- The source optimizer's assumptions on its future compilation oracle. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "syntax_oracle_ok_def"]
def syntaxOracleOk {C : Type} (c : Config) (xs : List ClosLang.Exp)
    (co : Nat → (Spt ValApprox × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (conf : Spt ValApprox) : Prop :=
  syntaxOk xs ∧
  isStateOracle (compileInc (α := List (Nat × Nat × ClosLang.Exp)) c)
    (pureCo (ClosFvs.compileInc (β := Nat × Nat × ClosLang.Exp)) ∘ co) ∧
  conf = (co 0).1.1 ∧
  oracleMonotonic (fun entry => {i | elistGlobals entry.2.1 i ≠ 0}) (· < ·)
    {i | elistGlobals xs i ≠ 0} co ∧
  ∀ n, syntaxOk (co n).2.1 ∧ (co n).2.2 = []

/-- The initial traversal and oracle recurrence preserve safety of every
future global approximation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "syntax_oracle_ok_state_sgc_free"]
theorem syntaxOracleOk_stateSgcFree {C : Type} (c : Config) (xs : List ClosLang.Exp)
    (co : Nat → (Spt ValApprox × C) × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)))
    (g : Spt ValApprox) (ys : List (ClosLang.Exp × ValApprox))
    (oracle : syntaxOracleOk c xs co g)
    (known : knownListTotal c (ClosFvs.compile xs) [] .ln = (ys, g)) :
    oracleStateSgcFree co := by
  obtain ⟨initial, recurrence, first, _, programs⟩ := oracle
  intro n
  induction n with
  | zero =>
    have safe := knownPreservesEsgcFree c (ClosFvs.compile xs) [] .ln ys g
      ⟨known, ?_, by simp, ?_⟩
    · simpa [first] using safe.2.2
    · simpa [ClosFvs.compile, esgcFreeList_iff] using
        (ClosFvs.removeList_esgcFree xs 0).mpr (by simpa [esgcFreeList_iff] using initial.2.2)
    · simp [globalsApproxSgcFree]
  | succ n ih =>
    have safeInput : ∀ e ∈ ClosFvs.compile (co n).2.1, esgcFree e := by
      simpa [ClosFvs.compile, esgcFreeList_iff] using
        (ClosFvs.removeList_esgcFree (co n).2.1 0).mpr
          (by simpa [esgcFreeList_iff] using (programs n).1.2.2)
    cases hk : knownListTotal (resetInlineFactor c) (ClosFvs.compile (co n).2.1) []
        (co n).1.1 with
    | mk eas next =>
      have safe := knownPreservesEsgcFree (resetInlineFactor c) (ClosFvs.compile (co n).2.1)
        [] (co n).1.1 eas next ⟨hk, safeInput, by simp, ih⟩
      have eq := recurrence n
      simp [pureCo, ClosFvs.compileInc, compileInc, hk] at eq
      simpa [eq] using safe.2.2

end Flapjack.Compiler.Backend.ClosKnown
