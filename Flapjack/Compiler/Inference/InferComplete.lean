module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.NamespaceProps

@[expose] public section

/-! Type-identifier bounds for inference environment extension. -/
namespace Flapjack.Compiler.Inference.InferComplete
open Flapjack Flapjack.NamespaceHOL Flapjack.Compiler.Inference.InferProps

/-- Widen an identifier bound through all three inference namespaces. -/
private theorem countMono (m n : Nat) (old : Infer.Env) (bound : m ≤ n)
    (ok : infSetTidsIenv (fun id => id < m) old) : infSetTidsIenv (fun id => id < n) old := by
  rcases ok with ⟨ot, oc, ov⟩
  refine ⟨?_, ?_, ?_⟩
  · intro key entry found id present
    exact Nat.lt_of_lt_of_le (ot key entry found id present) bound
  · intro key entry found
    obtain ⟨all, allowed⟩ := oc key entry found
    exact ⟨fun t mem id present => Nat.lt_of_lt_of_le (all t mem id present) bound,
      Nat.lt_of_lt_of_le allowed bound⟩
  · intro key entry found id present
    exact Nat.lt_of_lt_of_le (ov key entry found id present) bound

/-- Extending inference environments preserves their type-identifier bound. -/
@[hol "cakeml/compiler/inference/proofs/inferCompleteScript.sml" "inf_set_tids_extend_dec_ienv"]
theorem infSetTidsExtendDecIenv (n : Nat) (ienv2 : Infer.Env) (m : Nat) (ienv : Infer.Env) :
    infSetTidsIenv (fun id => id < n) ienv2 ∧
    infSetTidsIenv (fun id => id < m) ienv ∧ m ≤ n →
    infSetTidsIenv (fun id => id < n) (Infer.extendDecIenv ienv2 ienv) := by
  rintro ⟨new, old, bound⟩
  have wider := countMono m n ienv bound old
  have eqDec : (Classical.typeDecidableEq Basis.Pure.MlString.MlString) =
      inferInstanceAs (DecidableEq Basis.Pure.MlString.MlString) := Subsingleton.elim _ _
  unfold infSetTidsIenv at new wider ⊢
  simp only [Infer.extendDecIenv]
  rw [← eqDec] at new wider ⊢
  exact ⟨nsAll_nsAppend _ _ _ ⟨new.1, wider.1⟩,
    nsAll_nsAppend _ _ _ ⟨new.2.1, wider.2.1⟩,
    nsAll_nsAppend _ _ _ ⟨new.2.2, wider.2.2⟩⟩
end Flapjack.Compiler.Inference.InferComplete
