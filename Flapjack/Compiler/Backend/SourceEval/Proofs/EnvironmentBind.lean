module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.Environment
public import Flapjack.NamespaceProps
public import Batteries.Data.List.Basic
public import Flapjack.Misc.Pair

@[expose] public section

namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL Flapjack.AstHOL

/-- Binding related values at the same name preserves the environment relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_add_nsBind"]
theorem envRel_add_nsBind {α β γ : Type} (rel : Value → α → Prop) (env : SemEnv β)
    (ev : Namespace ModN VarN Value) (env' : SemEnv γ) (ev' : Namespace ModN VarN α)
    (x : Value) (y : α) (name : VarN)
    (premises : envRel rel { env with v := ev } { env' with v := ev' } ∧ rel x y) :
    envRel rel { env with v := nsBind name x ev } { env' with v := nsBind name y ev' } := by
  obtain ⟨⟨constructors, domain, modules, values⟩, bound⟩ := premises
  refine ⟨constructors, ?_, ?_, ?_⟩
  · funext id
    apply propext
    by_cases equal : id = .short name
    · subst id
      exact iff_true_intro ⟨x, nsLookup_nsBind.1 name x ev⟩ |>.trans
        (iff_true_intro ⟨y, nsLookup_nsBind.1 name y ev'⟩).symm
    · simp only [nsDom, nsLookup_nsBind.2 id name x ev equal,
        nsLookup_nsBind.2 id name y ev' equal]
      exact iff_of_eq (congrFun domain id)
  · funext path
    apply propext
    cases path with
    | nil => simp [nsDomMod, nsLookupMod]
    | cons m path =>
      have unchanged : ∀ {β : Type} (z : β) (ns : Namespace ModN VarN β),
          nsLookupMod (nsBind name z ns) (m :: path) = nsLookupMod ns (m :: path) := by
        intro β z ns
        cases ns
        rfl
      simp only [nsDomMod, unchanged]
      exact iff_of_eq (congrFun modules (m :: path))
  · intro id a b found
    by_cases equal : id = .short name
    · subst id
      rw [nsLookup_nsBind.1, Option.some.injEq] at found
      rw [nsLookup_nsBind.1, Option.some.injEq] at found
      rcases found with ⟨rfl, rfl⟩
      exact bound
    · apply values id a b
      simpa only [nsLookup_nsBind.2 id name x ev equal,
        nsLookup_nsBind.2 id name y ev' equal] using found

/-- Pointwise related bindings preserve the environment relation in list order. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "env_rel_add_nsBindList"]
theorem envRel_add_nsBindList {α β γ : Type} (rel : Value → α → Prop)
    (env : SemEnv β) (ev : Namespace ModN VarN Value)
    (env' : SemEnv γ) (ev' : Namespace ModN VarN α)
    (xs : List (VarN × Value)) (ys : List (VarN × α))
    (premises : envRel rel { env with v := ev } { env' with v := ev' } ∧
      List.Forall₂ (Flapjack.holRprod (· = ·) rel) xs ys) :
    envRel rel { env with v := nsBindList xs ev } { env' with v := nsBindList ys ev' } := by
  obtain ⟨related, bindings⟩ := premises
  induction bindings with
  | nil => exact related
  | @cons left right xs ys head tail ih =>
    obtain ⟨name, x⟩ := left
    obtain ⟨name', y⟩ := right
    simp only [Flapjack.holRprod] at head
    obtain ⟨rfl, values⟩ := head
    simp only [nsBindList, List.foldr_cons]
    exact envRel_add_nsBind rel env _ env' _ x y name ⟨ih, values⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
