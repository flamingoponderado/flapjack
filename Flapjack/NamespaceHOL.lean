import Flapjack.HolRef

/-! Primary counterpart of the source namespace script. The association-list
alias and recursively nested namespace carrier preserve list order and repeated
keys. Lookup operations and source-environment construction remain separate. -/
namespace Flapjack.NamespaceHOL

/-- Literal source association-list abbreviation. -/
@[hol "cakeml/semantics/namespaceScript.sml" "alist"]
abbrev Alist (Key Value : Type) := List (Key × Value)

/-- Complete original namespace carrier, with independent module-name,
identifier-name and value types. Both payloads remain association lists. -/
@[hol "cakeml/semantics/namespaceScript.sml" "namespace"]
inductive Namespace (ModuleName Name Value : Type) where
  | bind : List (Name × Value) → List (ModuleName × Namespace ModuleName Name Value) →
      Namespace ModuleName Name Value

end Flapjack.NamespaceHOL
