module

public import Flapjack.NamespaceProps
public import Flapjack.NamespaceProps.MapLookup

@[expose] public section

/-!
# Folding namespaces with `nsAppend`

Lean counterparts of the `inferProps` lemmas that map and quantify over a
left fold of `nsAppend`.  `nsAll` takes `DecidableEq` instances for module and
name equality in Lean, which render HOL's classical equality on those types.
-/

namespace Flapjack.NamespaceHOL

noncomputable local instance instDecidableEq_foldAppend (α : Type) : DecidableEq α :=
  Classical.typeDecidableEq α

/-- Original `nsMap_FOLDL_nsAppend`: mapping distributes over a folded append. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "nsMap_FOLDL_nsAppend"]
theorem nsMap_foldl_nsAppend {M N V W : Type} (ls : List (Namespace M N V))
    (ns : Namespace M N V) (f : V → W) :
    nsMap f (ls.foldl nsAppend ns) =
      (ls.map (nsMap f)).foldl nsAppend (nsMap f ns) := by
  induction ls generalizing ns with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, nsMap_nsAppend, ih]

/-- Original `nsAll_FOLDL_nsAppend`: a folded append preserves the predicate. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "nsAll_FOLDL_nsAppend"]
theorem nsAll_foldl_nsAppend {M N V : Type}
    (P : Ident M N → V → Prop) (ls : List (Namespace M N V)) (ns : Namespace M N V)
    (h : nsAll P ns ∧ ∀ x ∈ ls, nsAll P x) :
    nsAll P (ls.foldl nsAppend ns) := by
  induction ls generalizing ns with
  | nil => exact h.1
  | cons x xs ih =>
    rw [List.foldl_cons]
    refine ih (nsAppend ns x) ⟨?_, ?_⟩
    · exact nsAll_nsAppend P ns x ⟨h.1, h.2 x List.mem_cons_self⟩
    · intro y hy
      exact h.2 y (List.mem_cons_of_mem x hy)

end Flapjack.NamespaceHOL
