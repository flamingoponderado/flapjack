module

public import Flapjack.SemanticsHOL
public import Flapjack.PrimTypesHOL.Types

@[expose] public section

/-! Source semantics state and typeability. The declarative type judgments use
the unreviewed expression/declaration encodings; the original grammar-based
`parse` relation and the top-level source semantics are not yet ported. -/
namespace Flapjack.SemanticsHOL
open Flapjack.TypeSystemHOL Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

@[hol "cakeml/semantics/semanticsScript.sml" "state"]
structure SourceState (σ : Type) where
  tenv : TypeEnv
  typeIds : TypeIds
  semSt : SemanticPrimitivesHOL.State σ
  semEnv : SemEnv Value

@[hol "cakeml/semantics/semanticsScript.sml" "semantics"]
inductive SourceSemantics where
  | cannotParse
  | illTyped
  | execute : (HolBehaviour → Prop) → SourceSemantics

/-- Flapjack post-parse typeability infrastructure: the source rule's
disjoint fresh type IDs and `type_ds T` use the unreviewed `TypeDs` encoding.
This is not yet a tagged port of HOL's `can_type_prog_def`. -/
def canTypeProg {σ : Type} (st : SourceState σ) (prog : List Dec) : Prop :=
  ∃ newIds newEnv, disjointTypeIds st.typeIds newIds ∧ TypeDs true st.tenv prog newIds newEnv

end Flapjack.SemanticsHOL
