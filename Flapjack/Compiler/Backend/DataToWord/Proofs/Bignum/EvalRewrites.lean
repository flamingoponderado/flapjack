module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

@[expose] public section

/-! Evaluation rewrites stated in the data-to-word bignum proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend

namespace EvalRewritesWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvalRewritesWitness

/-- Assigning a constant inserts it into the locals. HOL derives this equation
from `evaluate_def`, `word_exp_def` and `set_var_def`. The evaluator inherits
the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "evaluate_Assign_Const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateAssignConst {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (w : BitVec width) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.assign n (.const w)) s =
      (none, { s with locals := sptInsert n (.word w) s.locals }) := by
  simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
    WordSemStateFiniteExact.setVar]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
