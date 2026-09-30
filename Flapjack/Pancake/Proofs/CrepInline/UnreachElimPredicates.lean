import Flapjack.Pancake.CrepInline.Pass

namespace Flapjack.CrepInlineUnreachElimPredicates

/-- Internal induction factoring for the source no-return preservation theorem. -/
private theorem noReturnOutput {width : Nat} [NeZero width] (program : CrepProgHOL width) :
    hasReturnHOLExact program = false →
      hasReturnHOLExact (unreachElimHOLExact program).1 = false := by
  induction program using hasReturnHOLExact.induct <;> intro h
  all_goals simp_all [hasReturnHOLExact, unreachElimHOLExact, Bool.or_eq_false_iff]
  all_goals try (split <;> simp_all [hasReturnHOLExact])
  case case9 =>
    rename_i program _ _ _ _ _ _ _ _
    cases program <;> simp_all [hasReturnHOLExact, unreachElimHOLExact]

/-- Internal induction factoring; no separate HOL original is claimed. -/
private theorem notBranchOutput {width : Nat} [NeZero width] (program : CrepProgHOL width) :
    notBranchRetHOLExact program = true →
      notBranchRetHOLExact (unreachElimHOLExact program).1 = true := by
  induction program using notBranchRetHOLExact.induct <;> intro h
  all_goals simp_all [notBranchRetHOLExact, unreachElimHOLExact,
    Bool.and_eq_true, noReturnOutput]
  all_goals try (split <;> simp_all [notBranchRetHOLExact])
  case case8 =>
    rename_i program _ _ _ _ _ _ _
    cases program <;> simp_all [notBranchRetHOLExact, unreachElimHOLExact]

/-- Same source conjunction and output pair; HOL Bool negation is = false. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_preserve_has_return"
  (words_as_type_indexed_bitvec)]
theorem unreachElimPreserveHasReturn {width : Nat} [NeZero width]
    (program output : CrepProgHOL width) (result : Option CrepEarlyExitHOL)
    (h : hasReturnHOLExact program = false ∧ unreachElimHOLExact program = (output, result)) :
    hasReturnHOLExact output = false := by
  have preserved := noReturnOutput program h.1
  rw [h.2] at preserved
  exact preserved

/-- Same source conjunction; HOL's Boolean predicate as a proposition is = true. -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_preserve_not_branch_ret"
  (words_as_type_indexed_bitvec)]
theorem unreachElimPreserveNotBranchRet {width : Nat} [NeZero width]
    (program output : CrepProgHOL width) (result : Option CrepEarlyExitHOL)
    (h : notBranchRetHOLExact program = true ∧ unreachElimHOLExact program = (output, result)) :
    notBranchRetHOLExact output = true := by
  have preserved := notBranchOutput program h.1
  rw [h.2] at preserved
  exact preserved

end Flapjack.CrepInlineUnreachElimPredicates
