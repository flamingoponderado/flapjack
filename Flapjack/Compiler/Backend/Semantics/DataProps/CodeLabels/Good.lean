module

public import Flapjack.Compiler.Backend.Semantics.DataProps.CodeLabels
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-! Well-scoped code labels in DATA programs. -/
namespace Flapjack.Compiler.Backend.DataSem

/-- Every referenced code label is defined by the program or allowed
externally. The middle program-entry payload is arbitrary. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "good_code_labels_def"]
def goodCodeLabels {α : Type} (program : List (Nat × α × DataLang.Prog))
    (external : Set Nat) : Prop :=
  (⋃₀ ((fun entry => getCodeLabels entry.2.2) '' {entry | entry ∈ program})) ⊆
    {label | label ∈ program.map Prod.fst} ∪ external

end Flapjack.Compiler.Backend.DataSem
