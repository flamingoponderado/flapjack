module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.RewriteCorrespondence

@[expose] public section

/-! Name preservation for the source-shaped BVI TMC pass. -/
namespace Flapjack.Compiler.Backend.BviTmc.Proofs

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_each_keeps_names"]
theorem compileEach_keepsNames (next : Nat) (xs : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (ys : List (Nat × Nat × Bvi.Exp)) (x : Nat)
    (assumptions : compileEachSource next xs = (next', ys) ∧ x ∈ xs.map Prod.fst) :
    x ∈ ys.map Prod.fst := by
  induction xs generalizing next next' ys with
  | nil => simp at assumptions
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases decision : compileExpSource loc next arity body with
    | none =>
      rcases tail : compileEachSource next rest with ⟨last, output⟩
      simp only [compileEachSource, decision, tail, Prod.mk.injEq, List.map_cons, List.mem_cons] at assumptions
      rcases assumptions with ⟨⟨rfl, rfl⟩, mem | mem⟩
      · simp [mem]
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ih next last output ⟨tail, mem⟩)
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      rcases tail : compileEachSource (next + bvlToBviNamespaces) rest with ⟨last, output⟩
      simp only [compileEachSource, decision, tail, Prod.mk.injEq, List.map_cons, List.mem_cons] at assumptions
      rcases assumptions with ⟨⟨rfl, rfl⟩, mem | mem⟩
      · simp [mem]
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr (Or.inr (ih (next + bvlToBviNamespaces) last output ⟨tail, mem⟩))

@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_prog_keeps_names"]
theorem compileProg_keepsNames (enabled : Bool) (next : Nat) (xs : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (ys : List (Nat × Nat × Bvi.Exp)) (x : Nat)
    (assumptions : compileProgSource enabled next xs = (next', ys) ∧ x ∈ xs.map Prod.fst) :
    x ∈ ys.map Prod.fst := by
  cases enabled with
  | false =>
    simp only [compileProgSource, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at assumptions
    simpa [← assumptions.1.2] using assumptions.2
  | true =>
    simp only [compileProgSource, ↓reduceIte] at assumptions
    exact compileEach_keepsNames next xs next' ys x assumptions

end Flapjack.Compiler.Backend.BviTmc.Proofs
