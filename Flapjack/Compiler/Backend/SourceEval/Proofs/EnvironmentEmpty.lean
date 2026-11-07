import Flapjack.Compiler.Backend.SourceEval.Proofs.Environment

/-! Empty namespaces in the source evaluator environment relation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

/-- Empty value namespaces eliminate the value-lookup condition on either side.
HOL prints free variables named `x` in both conjuncts, but their inferred
types differ; `leftBase` and `left` preserve those independent variables. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_nsEmpty"]
theorem envRel_nsEmpty {α β : Type} (rel : Value → α → Prop)
    (leftBase : SemEnv α) (left : SemEnv Value) (rightBase : SemEnv β) :
    (∀ right : SemEnv α,
      envRel rel { leftBase with v := nsEmpty } right ↔
        leftBase.c = right.c ∧ nsDom (nsEmpty : Namespace ModN VarN Value) = nsDom right.v ∧
          nsDomMod (nsEmpty : Namespace ModN VarN Value) = nsDomMod right.v) ∧
    (envRel rel left { rightBase with v := nsEmpty } ↔
      left.c = rightBase.c ∧ nsDom left.v = nsDom (nsEmpty : Namespace ModN VarN α) ∧
        nsDomMod left.v = nsDomMod (nsEmpty : Namespace ModN VarN α)) := by
  have emptyLookup : ∀ {T : Type} (id : Ident ModN VarN),
      nsLookup (nsEmpty : Namespace ModN VarN T) id = none := by
    intro T id
    cases id <;> rfl
  constructor
  · intro right
    simp [envRel, emptyLookup]
  · simp [envRel, emptyLookup]

end Flapjack.Compiler.Backend.SourceEval.Proofs
