import Flapjack.SemanticsHOL
import Flapjack.PrimTypesHOL.Types

/-! State and post-parse source semantics. The declarative type judgments use
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

/-- Flapjack post-parse semantics. The original `semantics_def` obtains the
optional program from `parse (lexer_fun input)`; this helper accepts that
result directly and therefore does not claim parser correspondence. -/
noncomputable def semanticsFromParsed {σ : Type} (st : SourceState σ)
    (prelude : List Dec) (parsed : Option (List Dec)) : SourceSemantics := by
  classical
  exact match parsed with
    | none => .cannotParse
    | some prog =>
      if canTypeProg st (prelude ++ prog) then
        .execute (semanticsProg st.semSt st.semEnv (prelude ++ prog))
      else .illTyped

end Flapjack.SemanticsHOL
