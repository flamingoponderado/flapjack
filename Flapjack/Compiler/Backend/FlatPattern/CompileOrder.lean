import Flapjack.Compiler.Backend.FlatPattern.CompileTotal

/-! Infrastructure for the source's reverse/traverse/reverse clauses. -/
namespace Flapjack.Compiler.Backend.FlatPattern

/-- Expression-list compilation composes over append, combining metadata by
maximum and disjunction. This supports the order equivalence below; it is
Flapjack proof infrastructure rather than a separate HOL declaration. -/
theorem compileExps_append (cfg : Config) (xs ys : List FlatLang.Exp) :
    compileExps cfg (xs ++ ys) =
      let (i, a, xs') := compileExps cfg xs
      let (j, b, ys') := compileExps cfg ys
      (max i j, a || b, xs' ++ ys') := by
  induction xs with
  | nil =>
      cases h : compileExps cfg ys with
      | mk j rest => cases rest with | mk b ys' => simp [compileExps, h]
  | cons x xs ih =>
      cases hx : compileExp cfg x with
      | mk i rest =>
        cases rest with
        | mk a x' =>
          cases ht : compileExps cfg xs with
          | mk j rest =>
            cases rest with
            | mk b xs' =>
              cases hy : compileExps cfg ys with
              | mk k rest =>
                cases rest with
                | mk c ys' =>
                  simp [compileExps, hx, ht, hy] at ih ⊢
                  rw [ih]
                  simp [Bool.or_assoc]

/-- Compiling a reversed expression list reverses only its output list; the
maximum and global-write metadata are unchanged. HOL's `Con` and `App`
clauses use reverse/traverse/reverse, whereas the total Lean traversal uses
the equivalent direct order. This is Flapjack proof infrastructure. -/
theorem compileExps_reverse (cfg : Config) (xs : List FlatLang.Exp) :
    compileExps cfg xs.reverse =
      let (i, sg, ys) := compileExps cfg xs
      (i, sg, ys.reverse) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hx : compileExp cfg x with
      | mk i rest =>
        cases rest with
        | mk a x' =>
          cases ht : compileExps cfg xs with
          | mk j rest =>
            cases rest with
            | mk b xs' =>
              simp only [List.reverse_cons, compileExps_append, ih, ht, hx, compileExps]
              simp [Nat.max_comm, Bool.or_comm]

end Flapjack.Compiler.Backend.FlatPattern
