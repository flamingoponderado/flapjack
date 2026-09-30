import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.Proofs.CrepInline

/-!
# crep_inline: syntactic `unreach_elim` lemmas

Exact counterparts of `cakeml/pancake/proofs/crep_inlineProofScript.sml:1663-1729`
(`unreach_elim_converge`, `unreach_elim_fix_point`,
`unreach_elim_nested_decs`, `unreach_elim_arg_load`,
`unreach_elim_arg_load_perm`) and `:1758` (`not_has_return_imp_not_branch_ret`),
bead `flapjack-pxn.18.5.5.46.1`.  They are purely syntactic statements over
the tagged exact `unreachElimHOLExact` (`unreach_elim_def`),
`nestedDecsHOL` (`nested_decs_def`), `argLoadHOLExact` (`arg_load_def`),
`hasReturnHOLExact` (`has_return_def`) and `notBranchRetHOLExact`
(`not_branch_ret_def`) on the word-indexed `CrepProgHOL` carrier.  HOL's
Bool-valued `has_return`/`not_branch_ret` used as propositions are `_ = true`.
-/

namespace Flapjack


namespace CrepInlineUnreachElim

/-- Exact HOL `unreach_elim_converge` (`crep_inlineProofScript.sml:1663-1666`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_converge"
  (words_as_type_indexed_bitvec)]
theorem unreachElimConverge {width : Nat} [NeZero width] :
    ∀ (p q : CrepProgHOL width) (r : Option CrepEarlyExitHOL),
      unreachElimHOLExact p = (q, r) → unreachElimHOLExact q = (q, r) := by
  intro p
  fun_induction unreachElimHOLExact p <;> intro q r h <;>
    simp only [Prod.mk.injEq] at h <;>
    (try obtain ⟨rfl, rfl⟩ := h) <;> simp_all [unreachElimHOLExact]

/-- Exact HOL `unreach_elim_fix_point` (`crep_inlineProofScript.sml:1686-1689`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_fix_point"
  (words_as_type_indexed_bitvec)]
theorem unreachElimFixPoint {width : Nat} [NeZero width] :
    ∀ (q : CrepProgHOL width) (r : Option CrepEarlyExitHOL),
      (∃ p, unreachElimHOLExact p = (q, r)) ↔ unreachElimHOLExact q = (q, r) := by
  intro q r
  constructor
  · rintro ⟨p, hp⟩
    exact unreachElimConverge p q r hp
  · intro hq
    exact ⟨q, hq⟩

/-- Exact HOL `unreach_elim_nested_decs` (`crep_inlineProofScript.sml:1697-1700`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_nested_decs"
  (words_as_type_indexed_bitvec)]
theorem unreachElimNestedDecs {width : Nat} [NeZero width] :
    ∀ (vs : List Nat) (es : List (CrepExpHOL width)) (p : CrepProgHOL width)
      (r : Option CrepEarlyExitHOL),
      vs.length = es.length ∧ unreachElimHOLExact p = (p, r) →
      unreachElimHOLExact (nestedDecsHOL vs es p) = (nestedDecsHOL vs es p, r) := by
  intro vs
  induction vs with
  | nil =>
      intro es p r ⟨hlen, hp⟩
      cases es with
      | nil => simpa [nestedDecsHOL] using hp
      | cons e es => simp at hlen
  | cons v vs ih =>
      intro es p r ⟨hlen, hp⟩
      cases es with
      | nil => simp at hlen
      | cons e es =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have h := ih es p r ⟨hlen, hp⟩
          simp [nestedDecsHOL, unreachElimHOLExact, h]

/-- Exact HOL `unreach_elim_arg_load` (`crep_inlineProofScript.sml:1709-1714`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_arg_load"
  (words_as_type_indexed_bitvec)]
theorem unreachElimArgLoad {width : Nat} [NeZero width] :
    ∀ (p : CrepProgHOL width) (tmpVars : List Nat) (args : List (CrepExpHOL width))
      (argsVname : List Nat) (r : Option CrepEarlyExitHOL),
      tmpVars.length = args.length ∧ args.length = argsVname.length ∧
        unreachElimHOLExact p = (p, r) →
      unreachElimHOLExact (argLoadHOLExact tmpVars args argsVname p) =
        (argLoadHOLExact tmpVars args argsVname p, r) := by
  intro p tmpVars args argsVname r ⟨h1, h2, hp⟩
  unfold argLoadHOLExact
  apply unreachElimNestedDecs _ _ _ _ ⟨h1, ?_⟩
  exact unreachElimNestedDecs _ _ _ _ ⟨by simp [h1, h2], hp⟩

/-- Exact HOL `unreach_elim_arg_load_perm` (`crep_inlineProofScript.sml:1720-1725`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "unreach_elim_arg_load_perm"
  (words_as_type_indexed_bitvec)]
theorem unreachElimArgLoadPerm {width : Nat} [NeZero width] :
    ∀ (p : CrepProgHOL width) (tmpVars : List Nat) (args : List (CrepExpHOL width))
      (argsVname : List Nat) (r : Option CrepEarlyExitHOL),
      tmpVars.length = argsVname.length ∧ args.length = argsVname.length ∧
        unreachElimHOLExact p = (p, r) →
      unreachElimHOLExact (argLoadHOLExact tmpVars args argsVname p) =
        (argLoadHOLExact tmpVars args argsVname p, r) := by
  intro p tmpVars args argsVname r ⟨h1, h2, hp⟩
  exact unreachElimArgLoad p tmpVars args argsVname r ⟨by omega, h2, hp⟩

/-- Exact HOL `not_has_return_imp_not_branch_ret`
    (`crep_inlineProofScript.sml:1758-1759`). -/
@[hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "not_has_return_imp_not_branch_ret"
  (words_as_type_indexed_bitvec)]
theorem notHasReturnImpNotBranchRet {width : Nat} [NeZero width] :
    ∀ p : CrepProgHOL width, ¬ hasReturnHOLExact p = true → notBranchRetHOLExact p = true := by
  intro p
  induction p using notBranchRetHOLExact.induct <;> intro h <;>
    simp_all [hasReturnHOLExact, notBranchRetHOLExact]

end CrepInlineUnreachElim

end Flapjack
