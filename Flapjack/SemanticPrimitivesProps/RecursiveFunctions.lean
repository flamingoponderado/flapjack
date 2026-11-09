module

public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.FiniteMap.AlistExact.Lookup
public import Flapjack.NamespaceProps

@[expose] public section

/-! Properties of recursive-function lookup. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.NamespaceHOL

/-- Building recursive bindings is appending the corresponding closure namespace. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "build_rec_env_merge"]
theorem buildRecEnv_merge {α : Type} (funs : List (VarN × VarN × AstHOL.Exp)) (_unused : α)
    (env : SemEnv Value) (env' : Namespace ModN VarN Value) :
    buildRecEnv funs env env' =
      nsAppend (alistToNs (funs.map fun (f, _, _) => (f, Value.recclosure env funs f))) env' := by
  rw [nsAppend_to_nsBindList]
  unfold buildRecEnv nsBindList
  rw [List.foldr_map]

/-- Recursive-function lookup is association-list lookup. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "find_recfun_ALOOKUP"]
theorem findRecFun_alookup {α β : Type} (funs : List (VarN × α × β)) (name : VarN) :
    findRecFun name funs = Flapjack.holALookup funs name := by
  classical
  induction funs with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨f, x, body⟩ := entry
    by_cases same : f = name
    · subst f
      simp [findRecFun, Flapjack.holALookup]
    · have reverse : name ≠ f := Ne.symm same
      simp [findRecFun, Flapjack.holALookup, same, reverse, ih]

end Flapjack.SemanticPrimitivesProps
