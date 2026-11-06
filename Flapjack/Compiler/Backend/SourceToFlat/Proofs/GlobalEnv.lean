import Flapjack.Compiler.Backend.Semantics.FlatSem
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-! The global environment carrier used by the original source-to-flat value
relation. The relation itself and the pass simulation remain unported. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

abbrev ConstructorKey := (FlatLang.CtorId × FlatLang.TypeId) × Nat
abbrev TypeConstructors := List (FlatLang.CtorId × Nat)

/-- Lookup-and-support view used for the finite-map representation witness. -/
structure GlobalEnvBroad where
  v : List (Option FlatSem.Value)
  cLookup : ConstructorKey → Option SemanticPrimitivesHOL.Stamp
  cSupport : ∃ keys : List ConstructorKey, ∀ key, cLookup key ≠ none → key ∈ keys
  tysLookup : Nat → Option TypeConstructors
  tysSupport : ∃ keys : List Nat, ∀ key, tysLookup key ≠ none → key ∈ keys

/-- Original source-to-flat proof environment with canonical finite maps. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "global_env"
  (fmap_as_finite_support := [c, tys])]
structure GlobalEnv where
  v : List (Option FlatSem.Value)
  c : HolFiniteMapExact ConstructorKey SemanticPrimitivesHOL.Stamp
  tys : HolFiniteMapExact Nat TypeConstructors

namespace GlobalEnv

/-- Expose the lookup functions and their finite-support evidence. -/
def toBroad (env : GlobalEnv) : GlobalEnvBroad where
  v := env.v
  cLookup := env.c.lookup
  cSupport := env.c.finiteSupport
  tysLookup := env.tys.lookup
  tysSupport := env.tys.finiteSupport

/-- Reconstruct the canonical finite maps from the lookup-and-support view. -/
def ofBroad (env : GlobalEnvBroad) : GlobalEnv where
  v := env.v
  c := ⟨env.cLookup, env.cSupport⟩
  tys := ⟨env.tysLookup, env.tysSupport⟩

/-- Canonical roundtrip for both finite-map fields. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) : ofBroad (toBroad env) = env := by
  cases env
  rfl

end GlobalEnv
end Flapjack.Compiler.Backend.SourceToFlat
