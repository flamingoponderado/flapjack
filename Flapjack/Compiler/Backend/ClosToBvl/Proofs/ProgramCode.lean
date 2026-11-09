import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InitialState

/-! Connect installed compiled entries to the initial source code map. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The original association-list code map uses a right fold, represented by
reversing the source entries before the canonical finite-map list update. -/
def initialSourceCode (program : List (Nat × Nat × ClosLang.Exp)) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) :=
  HolFiniteMapExact.empty.updateListEq program.reverse

/-- A successful lookup in the initial source code map identifies an entry
of the original program, including when earlier duplicate names shadow later
ones. -/
theorem initialSourceCode_lookup_mem (program : List (Nat × Nat × ClosLang.Exp))
    (name arity : Nat) (body : ClosLang.Exp)
    (found : (initialSourceCode program).lookup name = some (arity, body)) :
    (name, arity, body) ∈ program := by
  have split := install_source_lookup HolFiniteMapExact.empty program.reverse name arity body found
  cases split with
  | inl member => simpa using member
  | inr impossible => simp [HolFiniteMapExact.empty] at impossible

end Flapjack.Compiler.Backend.ClosToBvl
