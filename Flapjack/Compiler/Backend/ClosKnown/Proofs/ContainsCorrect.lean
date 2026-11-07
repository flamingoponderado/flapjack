import Flapjack.Compiler.Backend.ClosKnown.Inline

/-! Agreement of the executable closure check with the source traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

private theorem containsClosuresHOL_eq_any (xs : List Exp) :
    containsClosuresHOL xs = xs.any containsClosuresExpHOL := by
  induction xs with
  | nil => simp [containsClosuresHOL]
  | cons x xs ih => simp [containsClosuresHOL, ih]

private theorem foldAny_correct (xs : List Exp) (f : Exp → Option Bool) (p : Exp → Bool)
    (initial result : Bool)
    (correct : ∀ x ∈ xs, ∀ value, f x = some value → value = p x)
    (run : xs.foldlM (fun b x => if b then pure true else f x) initial = some result) :
    result = (initial || xs.any p) := by
  induction xs generalizing initial with
  | nil => simpa using run.symm
  | cons x xs ih =>
    cases initial with
    | true =>
      have tail := ih true (by intro y hy; exact correct y (by simp [hy])) (by simpa using run)
      simpa using tail
    | false =>
      cases hx : f x with
      | none => simp [hx] at run
      | some value =>
        have eq := correct x (by simp) value hx
        have tailRun : xs.foldlM (fun b x => if b then pure true else f x) value = some result := by
          simpa [hx] using run
        have tail := ih value (by intro y hy; exact correct y (by simp [hy])) tailRun
        simpa [eq] using tail

/-- Any successful bounded closure check returns the source predicate. -/
theorem containsClosuresFuel_correct (fuel : Nat) :
    ∀ (e : Exp) (result : Bool), containsClosuresFuel fuel e = some result →
      result = containsClosuresExpHOL e := by
  induction fuel with
  | zero => intro e result run; simp [containsClosuresFuel] at run
  | succ fuel ih =>
    intro e result run
    cases e with
    | var => simpa [containsClosuresFuel, containsClosuresExpHOL] using run.symm
    | fn | letrec => simpa [containsClosuresFuel, containsClosuresExpHOL] using run.symm
    | raise trace body | tick trace body =>
      simpa [containsClosuresExpHOL] using ih body result (by simpa [containsClosuresFuel] using run)
    | ifThenElse trace x y z =>
      have h := foldAny_correct [x, y, z] (containsClosuresFuel fuel) containsClosuresExpHOL false result
        (by intro e _ value hr; exact ih e value hr) (by simpa [containsClosuresFuel] using run)
      simpa [containsClosuresExpHOL, Bool.or_assoc] using h
    | «let» trace xs body =>
      have h := foldAny_correct (xs ++ [body]) (containsClosuresFuel fuel) containsClosuresExpHOL false result
        (by intro e _ value hr; exact ih e value hr) (by simpa [containsClosuresFuel] using run)
      simpa [containsClosuresExpHOL, containsClosuresHOL_eq_any, List.any_append] using h
    | handle trace x y =>
      have h := foldAny_correct [x, y] (containsClosuresFuel fuel) containsClosuresExpHOL false result
        (by intro e _ value hr; exact ih e value hr) (by simpa [containsClosuresFuel] using run)
      simpa [containsClosuresExpHOL] using h
    | op trace op xs | call trace ticks op xs =>
      have h := foldAny_correct xs (containsClosuresFuel fuel) containsClosuresExpHOL false result
        (by intro e _ value hr; exact ih e value hr) (by simpa [containsClosuresFuel] using run)
      simpa [containsClosuresExpHOL, containsClosuresHOL_eq_any] using h
    | app trace loc fn xs =>
      have h := foldAny_correct (fn :: xs) (containsClosuresFuel fuel) containsClosuresExpHOL false result
        (by intro e _ value hr; exact ih e value hr) (by simpa [containsClosuresFuel] using run)
      simpa [containsClosuresExpHOL, containsClosuresHOL_eq_any] using h

end Flapjack.Compiler.Backend.ClosKnown
