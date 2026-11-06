import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundConstructor

/-! Local sequencing and exception propagation over preliminary factored
relations, pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Binding a local name leaves all other short names and all qualified
lookups unchanged. -/
theorem nsLookup_bind_other {α : Type} (env : Namespace ModN VarN α) (name : VarN) (value : α)
    (id : Ident ModN VarN) (other : id ≠ .short name) :
    nsLookup (nsBind name value env) id = nsLookup env id := by
  cases env with
  | bind values modules =>
    cases id with
    | short key =>
      have different : key ≠ name := by
        intro equal
        subst key
        exact other rfl
      have neq : (key == name) = false := by
        change decide (key = name) = false
        simp [different]
      simp [nsBind, nsLookup, List.lookup_cons, neq]
    | long moduleName inner => rfl

end Flapjack.Compiler.Backend.SourceToFlat
