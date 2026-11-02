import Flapjack.Compiler.Backend.ClosMti
import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMti

/-! Source-shaped function collection relations for the multi-argument pass. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang Flapjack.Basis.Pure.MlString

/-- Reconstruct nested unary functions with their original names. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "mk_Fns_def"]
def mkFns : List MlString → Exp → Exp
  | [], e => e
  | t :: ts, e => .fn t none none 1 (mkFns ts e)

/-- Function argument collection respects the configured maximum. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_args_IMP"]
theorem collectArgsBounds (maxApp k : Nat) (e : Exp) (numArgs : Nat) (rest : Exp)
    (run : collectArgs maxApp k e = (numArgs, rest)) (bound : k ≤ maxApp) :
    k ≤ numArgs ∧ numArgs ≤ maxApp := by
  fun_induction collectArgs maxApp k e <;> simp_all <;> omega

/-- On pre-multi-argument syntax, collection removes exactly a prefix of
unary functions and preserves the remaining syntax invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_args_ok_IMP"]
theorem collectArgsUnary (maxApp k : Nat) (e : Exp) (numArgs : Nat) (rest : Exp)
    (run : collectArgs maxApp k e = (numArgs, rest)) (safe : ClosProps.noMti e) :
    ∃ ts, e = mkFns ts rest ∧ numArgs = k + ts.length ∧ ClosProps.noMti rest := by
  fun_induction collectArgs maxApp k e <;> simp_all [ClosProps.noMti, mkFns]
  case case1 =>
    rename_i current name arity body step ih
    obtain ⟨ts, bodyEq, countEq, valid⟩ := ih
    refine ⟨name :: ts, ?_, ?_, valid⟩
    · simp [mkFns, bodyEq]
    · simp only [List.length_cons]
      omega

end Flapjack.Compiler.Backend.ClosMti
