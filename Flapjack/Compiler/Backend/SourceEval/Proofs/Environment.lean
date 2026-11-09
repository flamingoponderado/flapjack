import Flapjack.Compiler.Backend.SourceEval.Proofs
import Flapjack.NamespaceProps

/-! Environment relation used by the source evaluator proof. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL

/-- Equal constructor environments and namespace domains, with related values
at every identifier present in both environments. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_def"]
def envRel {α : Type} (rel : Value → α → Prop)
    (env : SemEnv Value) (env' : SemEnv α) : Prop :=
  env.c = env'.c ∧ nsDom env.v = nsDom env'.v ∧
    nsDomMod env.v = nsDomMod env'.v ∧
    ∀ name x y, nsLookup env.v name = some x ∧ nsLookup env'.v name = some y → rel x y

/-- Constructor lookup under related environments preserves the constructor namespace. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_nsLookup_c"]
theorem envRel_nsLookup_c {α : Type} (rel : Value → α → Prop)
    (env : SemEnv Value) (env' : SemEnv α) (id : Ident ModN ConN) (r : Option (Nat × Stamp))
    (premises : envRel rel env env' ∧ nsLookup env.c id = r) : env'.c = env.c :=
  premises.1.1.symm

/-- Converting an association list binds it into the empty namespace. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "alist_to_ns_to_bind2"]
theorem alistToNs_to_bind2 {M N V : Type} :
    ∀ l : List (N × V), (alistToNs l : Namespace M N V) = nsBindList l nsEmpty := by
  intro l
  simpa only [(nsAppend_nsEmpty (alistToNs l : Namespace M N V)).1] using
    nsAppend_to_nsBindList (nsEmpty : Namespace M N V) l

/-- A singleton namespace binds one name in the empty namespace. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "nsSing_eq_bind"]
theorem nsSing_eq_bind {M N V : Type} :
    ∀ (n : N) (x : V), (nsSing n x : Namespace M N V) = nsBind n x nsEmpty := by
  intro n x
  rfl

/-- Pair elimination agrees with applying the tuple-pattern function. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "pair_CASE_eq_pairarg"]
theorem pairCase_eq_pairarg {α β γ : Type} (p : β × γ) (f : β → γ → α) :
    Prod.casesOn p f = (fun pair => match pair with | (x, y) => f x y) p := by
  cases p
  rfl

/-- Pointwise weakening of the value relation preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_mono_rel"]
theorem envRel_monoRel {α : Type} (rel rel' : Value → α → Prop)
    (monotone : ∀ y z, rel y z → rel' y z)
    (env : SemEnv Value) (env' : SemEnv α) (related : envRel rel env env') :
    envRel rel' env env' := by
  obtain ⟨constructors, domain, modules, values⟩ := related
  exact ⟨constructors, domain, modules, fun name x y found => monotone x y (values name x y found)⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
