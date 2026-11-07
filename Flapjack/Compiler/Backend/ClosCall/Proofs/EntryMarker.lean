import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationAccounting

/-! Preservation of the numbering pass's incremental entry marker. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang

/-- Successful direct-call traversal preserves a leading constant marker and
the length of the remaining expression list. -/
theorem callsListFuel_entryMarker (fuel : Nat) (trace : BackendCommon.Tra) (n : Nat)
    (xs out : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel fuel (.op trace (.intOp (.const (Int.ofNat n))) [] :: xs) initial =
      some (out, final)) :
    ∃ ys, out = .op trace (.intOp (.const (Int.ofNat n))) [] :: ys ∧ ys.length = xs.length := by
  cases fuel with
  | zero => simp [callsListFuel] at run
  | succ fuel =>
    cases fuel with
    | zero => simp [callsListFuel, callsFuel] at run
    | succ fuel =>
      simp only [callsListFuel, callsFuel, Bind.bind, Option.bind, Pure.pure] at run
      cases tail : callsListFuel (fuel + 1) xs initial with
      | none => simp [tail] at run
      | some result =>
        obtain ⟨ys, state⟩ := result
        simp only [tail, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨ys, rfl, callsListFuel_length (fuel + 1) xs initial state ys tail⟩

/-- The production retry wrapper preserves the marker and tail length. -/
theorem callsListBounded_entryMarker (fuel : Nat) (trace : BackendCommon.Tra) (n : Nat)
    (xs out : List ClosLang.Exp) (initial final : State)
    (run : callsListBounded fuel (.op trace (.intOp (.const (Int.ofNat n))) [] :: xs) initial =
      some (out, final)) :
    ∃ ys, out = .op trace (.intOp (.const (Int.ofNat n))) [] :: ys ∧ ys.length = xs.length := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel (.op trace (.intOp (.const (Int.ofNat n))) [] :: xs) initial with
  | none =>
    simp only [first] at run
    exact callsListFuel_entryMarker _ trace n xs out initial final run
  | some result =>
    simp only [first, Option.some.injEq] at run
    have eq : result = (out, final) := run
    subst result
    exact callsListFuel_entryMarker fuel trace n xs out initial final first

/-- Incremental direct-call conversion preserves the marker and tail length. -/
theorem compileIncFuel_entryMarker (fuel : Nat) (known nextKnown : NumSet)
    (trace : BackendCommon.Tra) (n : Nat) (xs : List ClosLang.Exp)
    (aux : List (Nat × Nat × ClosLang.Exp)) (converted : ClosSem.Program)
    (run : compileIncFuel? fuel known
      (.op trace (.intOp (.const (Int.ofNat n))) [] :: xs, aux) = some (nextKnown, converted)) :
    ∃ ys, converted.1 = .op trace (.intOp (.const (Int.ofNat n))) [] :: ys ∧ ys.length = xs.length := by
  simp only [compileIncFuel?, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨output, state⟩, traversal, knownEq, outputEq, auxEq⟩ := run
  simpa using callsListBounded_entryMarker fuel trace n xs output (known, []) state traversal

end Flapjack.Compiler.Backend.ClosCall
