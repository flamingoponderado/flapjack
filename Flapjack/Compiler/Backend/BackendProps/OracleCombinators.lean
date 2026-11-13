module

public import Flapjack.Compiler.Backend.BackendProps.StateCompiler
public import Flapjack.Compiler.Backend.BackendProps.Pure

@[expose] public section

/-! Combinators for adapting syntax oracles through compiler passes. -/
namespace Flapjack.Compiler.Backend.BackendProps

/-- Apply a pure pass to every syntax-oracle program. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_co_progs_def"]
def pureCoProgs {P Q : Type} (f : P → Q) (oracle : Nat → P) : Nat → Q :=
  f ∘ oracle

/-- Stateful adaptation of an oracle built with the same stateful pass. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "state_co_add_state_co"]
theorem stateCoAddStateCo {S P Q C : Type} (f : S → P → S × Q) (st : S)
    (mk : (Nat → Q) → Nat → C) (progs : Nat → P) :
    stateCo f (syntaxToFullOracle (addStateCo f st mk) progs) =
      syntaxToFullOracle mk (stateCoProgs f st progs) := by
  funext n
  rfl

/-- Pure adaptation commutes with building the corresponding full oracle. -/
@[hol "cakeml/compiler/backend/semantics/backendPropsScript.sml" "pure_co_syntax_to_full_oracle"]
theorem pureCoSyntaxToFullOracle {P Q C : Type} (f : P → Q)
    (mk : (Nat → Q) → Nat → C) (progs : Nat → P) :
    pureCo f ∘ syntaxToFullOracle (mk ∘ pureCoProgs f) progs =
      syntaxToFullOracle mk (pureCoProgs f progs) := by
  funext n
  rfl

end Flapjack.Compiler.Backend.BackendProps
