import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateGrowth

/-! Wrapper decomposition and preservation of optimized code. -/
namespace Flapjack.Compiler.Backend.BviTmc.WrapperCases
open BviTmc BviSem BvlSem

/-- A rewritten conditional retains either the rewritten or original then branch. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "wrapper_strip_if_then"]
theorem wrapper_strip_if_then (loc locOpt n : Nat) (condition yes no wrapper : Bvi.Exp)
    (run : rewriteWrapperSource loc locOpt n (.ifThenElse condition yes no) = some wrapper) :
    ∃ yes' no', wrapper = .ifThenElse condition yes' no' ∧
      (rewriteWrapperSource loc locOpt n yes = some yes' ∨ yes' = yes) := by
  rw [rewriteWrapperSource.eq_def] at run
  cases hy : rewriteWrapperSource loc locOpt n yes <;>
    cases hn : rewriteWrapperSource loc locOpt n no <;> simp_all
  all_goals (subst wrapper; simp_all)

/-- A rewritten conditional retains either the rewritten or original else branch. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "wrapper_strip_if_else"]
theorem wrapper_strip_if_else (loc locOpt n : Nat) (condition yes no wrapper : Bvi.Exp)
    (run : rewriteWrapperSource loc locOpt n (.ifThenElse condition yes no) = some wrapper) :
    ∃ yes' no', wrapper = .ifThenElse condition yes' no' ∧
      (rewriteWrapperSource loc locOpt n no = some no' ∨ no' = no) := by
  rw [rewriteWrapperSource.eq_def] at run
  cases hy : rewriteWrapperSource loc locOpt n yes <;>
    cases hn : rewriteWrapperSource loc locOpt n no <;> simp_all
  all_goals (subst wrapper; simp_all)

/-- Rewriting a let preserves its bindings and rewrites its body. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "wrapper_strip_let"]
theorem wrapper_strip_let (n loc locOpt : Nat) (xs : List Bvi.Exp) (body wrapper : Bvi.Exp)
    (run : rewriteWrapperSource loc locOpt n (.let xs body) = some wrapper) :
    ∃ body', wrapper = .let xs body' ∧
      rewriteWrapperSource loc locOpt (n + xs.length) body = some body' := by
  simp only [rewriteWrapperSource] at run
  cases h : rewriteWrapperSource loc locOpt (n + xs.length) body <;> simp_all

/-- Rewriting a tick rewrites its body. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "wrapper_strip_tick"]
theorem wrapper_strip_tick (n loc locOpt : Nat) (body wrapper : Bvi.Exp)
    (run : rewriteWrapperSource loc locOpt n (.tick body) = some wrapper) :
    ∃ body', wrapper = .tick body' ∧ rewriteWrapperSource loc locOpt n body = some body' := by
  simp only [rewriteWrapperSource] at run
  cases h : rewriteWrapperSource loc locOpt n body <;> simp_all

/-- Flapjack infrastructure: optimized code survives both evaluations. This
is untagged until the underlying BVI evaluator is source-reviewed. -/
theorem evaluate_pres_opt_code {C D F G : Type} (loc locOpt : Nat)
    (s1 u1 : BviState C F) (s2 u2 : BviState D G)
    (xs : List Bvi.Exp) (env1 env2 : List Value) (r1 r2 : BviResult)
    (code : optimisedCode loc locOpt s1.code s2.code)
    (run1 : evaluate xs env1 s1 = (r1, u1))
    (run2 : evaluate xs env2 s2 = (r2, u2)) :
    optimisedCode loc locOpt u1.code u2.code := by
  obtain ⟨arity, body, wrapper, worker, sourceFound, targetFound, workerFound, wrap, work⟩ := code
  have sourceGrowth := BviProps.evaluate_code_mono xs env1 s1 u1 r1 run1
  have targetGrowth := BviProps.evaluate_code_mono xs env2 s2 u2 r2 run2
  refine ⟨arity, body, wrapper, worker, ?_, ?_, ?_, wrap, work⟩
  · exact (sptSubsptLookup _ _).mp sourceGrowth loc _ sourceFound
  · exact (sptSubsptLookup _ _).mp targetGrowth loc _ targetFound
  · exact (sptSubsptLookup _ _).mp targetGrowth locOpt _ workerFound

end Flapjack.Compiler.Backend.BviTmc.WrapperCases
