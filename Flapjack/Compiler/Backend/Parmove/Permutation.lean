import Flapjack.Compiler.Backend.Parmove.UpdateLemmas

namespace Flapjack.Compiler.Backend.Parmove

/-- Exact permutation invariance for parallel moves with distinct destinations.
The equality is between the full environment transformers, not just a selected
register or a successful execution. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_perm"]
theorem parsem_perm {α β : Type} [DecidableEq α]
    (first second : List (α × α)) :
    windmill first ∧ first.Perm second →
    parsem (β := β) first = parsem second := by
  rintro ⟨valid, perm⟩
  revert valid
  induction perm with
  | nil => intro _; rfl
  | @cons head before after perm ih =>
      intro valid
      rcases head with ⟨destination, source⟩
      have parts : destination ∉ before.map Prod.fst ∧ windmill before := by
        simpa [windmill] using valid
      have fresh : destination ∉ after.map Prod.fst := by
        exact fun member => parts.1 ((perm.map Prod.fst).mem_iff.mpr member)
      funext env
      rw [parsem_cons destination source before env parts.1,
        parsem_cons destination source after env fresh, ih parts.2]
  | @swap a b tail =>
      intro valid
      rcases a with ⟨ad, av⟩
      rcases b with ⟨bd, bv⟩
      have parts : bd ≠ ad ∧ bd ∉ tail.map Prod.fst ∧
          ad ∉ tail.map Prod.fst ∧ windmill tail := by
        simpa [windmill, and_assoc] using valid
      funext env
      rw [parsem_cons bd bv ((ad,av)::tail) env (by simp [parts.1, parts.2.1]),
        parsem_cons ad av tail env parts.2.2.1,
        parsem_cons ad av ((bd,bv)::tail) env (by simp [Ne.symm parts.1, parts.2.2.1]),
        parsem_cons bd bv tail env parts.2.1]
      exact updateEnv_commute (parsem tail env) ad bd (env av) (env bv) (Ne.symm parts.1)
  | @trans before middle after left right ihLeft ihRight =>
      intro valid
      have middleValid : windmill middle := (left.map Prod.fst).nodup_iff.mp valid
      exact (ihLeft valid).trans (ihRight middleValid)

end Flapjack.Compiler.Backend.Parmove
