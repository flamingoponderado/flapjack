module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Depth.Size
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueEquality
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers

@[expose] public section

/-! Equality helper termination resource bounds. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- Successful equality comparisons fit the termination clock. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_limit"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_limit {width : Nat} [NeZero width] {β γ : Type} (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v1 v2 : Value) (w1 w2 : WordLocW width) (vars : List (Value × WordLocW width))
    (n : Nat) (b : Bool) (_v : β) (_w : γ) :
    memoryRel conf be next refs space store memory domain ((v1,w1) :: (v2,w2) :: vars) ∧
      vbEqSize refs v1 v2 = some (n,b) ∧ goodDimindex width →
    n * (2 ^ width) < wordSemMustTerminateLimit width - (2 ^ width) := by
  rintro ⟨rel, sized, good⟩
  let d := 2 ^ width
  have depthBound := memoryRel_depthWordBound conf be next refs space store memory domain
    v1 w1 ((v2,w2) :: vars) rel good
  have sizeBound := memoryRel_depthSizeLimit conf be next refs space store memory domain
    v1 w1 ((v2,w2) :: vars) ⟨rel, good⟩
  have nBound := vbEqSize_imp_vbSize.1 refs v1 v2 n b sized
  have dLarge : 4 ≤ d := by
    dsimp [d]
    rcases good with h | h <;> subst width <;> norm_num
  have expBound : vDepth v1 + 2 ≤ d ^ d := by
    have sq : d ^ 2 ≤ d ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    have quadratic : d + 2 ≤ d ^ 2 := by nlinarith
    omega
  have nScaled : n * d ≤ d ^ (vDepth v1 + 2) := by
    have base : n ≤ d ^ (vDepth v1 + 1) := Nat.le_trans nBound sizeBound
    calc
      n * d ≤ d ^ (vDepth v1 + 1) * d := Nat.mul_le_mul_right d base
      _ = d ^ (vDepth v1 + 2) := by simp only [pow_succ]
  have limitBound : n * d ≤ d ^ (d ^ d) := Nat.le_trans nScaled
    (Nat.pow_le_pow_right (by omega) expBound)
  change n * d < wordSemMustTerminateLimit width - d
  unfold wordSemMustTerminateLimit
  change n * d < 2 * d + d * d + d ^ d + d ^ (d ^ d) - d
  omega

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
