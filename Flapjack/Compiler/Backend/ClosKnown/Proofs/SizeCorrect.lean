module

public import Flapjack.Compiler.Backend.ClosKnown.Inline

@[expose] public section

/-! Agreement of the executable inliner size analysis with the source. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

private theorem getSizeAuxHOL_eq_sum (xs : List Exp) :
    getSizeAuxHOL xs = (xs.map getSizeExpHOL).sum := by
  induction xs with
  | nil => simp [getSizeAuxHOL]
  | cons x xs ih => simp [getSizeAuxHOL, ih]

private theorem getSizeFunsHOL_eq_map (fs : List (Nat × Exp)) :
    getSizeFunsHOL fs = getSizeAuxHOL (fs.map Prod.snd) := by
  induction fs with
  | nil => simp [getSizeFunsHOL, getSizeAuxHOL]
  | cons f fs ih =>
    cases f
    simp [getSizeFunsHOL, getSizeAuxHOL, ih]

private theorem foldSum_correct (xs : List Exp) (f : Exp → Option Nat) (p : Exp → Nat)
    (initial result : Nat)
    (correct : ∀ x ∈ xs, ∀ value, f x = some value → value = p x)
    (run : xs.foldlM (fun n x => do pure (n + (← f x))) initial = some result) :
    result = initial + (xs.map p).sum := by
  induction xs generalizing initial with
  | nil => simpa using run.symm
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [hx] at run
    | some value =>
      have eq := correct x (by simp) value hx
      have tailRun : xs.foldlM (fun n x => do pure (n + (← f x))) (initial + value) = some result := by
        simpa [hx] using run
      have tail := ih (initial + value) (by intro y hy; exact correct y (by simp [hy])) tailRun
      simpa [eq, Nat.add_assoc] using tail

/-- Any successful bounded size traversal returns the source size. -/
theorem sizeFuel_correct (fuel : Nat) :
    ∀ (e : Exp) (result : Nat), sizeFuel fuel e = some result →
      result = getSizeExpHOL e := by
  induction fuel with
  | zero => intro e result run; simp [sizeFuel] at run
  | succ fuel ih =>
    intro e result run
    cases e with
    | var => simpa [sizeFuel, getSizeExpHOL] using run.symm
    | tick trace e =>
      simpa [getSizeExpHOL] using ih e result (by simpa [sizeFuel] using run)
    | raise trace e | fn trace loc vars arity e =>
      simp only [sizeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at run
      obtain ⟨value, h, rfl⟩ := run
      simp [getSizeExpHOL, ih e value h]
    | ifThenElse trace x y z =>
      simp only [sizeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at run
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := run
      simp [getSizeExpHOL, ih x a ha, ih y b hb, ih z c hc]
    | handle trace x y =>
      simp only [sizeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at run
      obtain ⟨a, ha, b, hb, rfl⟩ := run
      simp [getSizeExpHOL, ih x a ha, ih y b hb]
    | «let» trace xs body =>
      simp only [sizeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at run
      obtain ⟨sum, hs, bodySize, hb, rfl⟩ := run
      have hsum := foldSum_correct xs (sizeFuel fuel) getSizeExpHOL 0 sum
        (by intro e _ value he; exact ih e value he) hs
      simp [getSizeExpHOL, getSizeAuxHOL_eq_sum, hsum, ih body bodySize hb]
    | op trace op xs | call trace ticks op xs =>
      simp only [sizeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at run
      obtain ⟨sum, hs, rfl⟩ := run
      have hsum := foldSum_correct xs (sizeFuel fuel) getSizeExpHOL 0 sum
        (by intro e _ value he; exact ih e value he) hs
      simp [getSizeExpHOL, getSizeAuxHOL_eq_sum, hsum]
    | letrec names loc vars fs body =>
      simp only [sizeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at run
      obtain ⟨sum, hs, bodySize, hb, rfl⟩ := run
      have hsum := foldSum_correct (fs.map Prod.snd) (sizeFuel fuel) getSizeExpHOL 0 sum
        (by intro e _ value he; exact ih e value he) hs
      simp [getSizeExpHOL, getSizeFunsHOL_eq_map, getSizeAuxHOL_eq_sum, hsum, ih body bodySize hb]
    | app trace loc e xs =>
      simp only [sizeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at run
      obtain ⟨value, hv, sum, hs, rfl⟩ := run
      have hsum := foldSum_correct xs (sizeFuel fuel) getSizeExpHOL 0 sum
        (by intro e _ value he; exact ih e value he) hs
      simp [getSizeExpHOL, getSizeAuxHOL_eq_sum, hsum, ih e value hv]

end Flapjack.Compiler.Backend.ClosKnown
