import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.TagColour
import Flapjack.Compiler.Backend.RegAlloc.Proofs.Invariants

/-!
# reg_allocProof: colouring transport

Ports of `reg_allocProofScript.sml:1307-1325`, `1483-1491` and `3024-3041`: a satisfactory
colouring is injective on a clique, restricts to subgraphs, and the colours read off a
clash-free, fully fixed tag array form a satisfactory colouring. HOL `EL` is the exact
`holEl`, `ALL_DISTINCT` is `List.Nodup`, `EVERY` is bounded membership quantification and
`MAP` is `List.map`.
-/

namespace Flapjack.RegAlloc

open Flapjack

/-- Exact HOL `colouring_satisfactory_cliques` (`reg_allocProofScript.sml:1307-1325`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "colouring_satisfactory_cliques"]
theorem colouringSatisfactoryCliques :
    ∀ (ls : List Nat) (g : List (List Nat)) (f : Nat → Nat),
      ls.Nodup ∧ (∀ x ∈ ls, x < g.length) ∧ colouringSatisfactory f g ∧ isClique ls g →
      (ls.map f).Nodup := by
  intro ls
  induction ls with
  | nil => intro _ _ _; exact List.nodup_nil
  | cons h t ih =>
      intro g f ⟨hd, hb, hc, hcl⟩
      obtain ⟨hnot, hdt⟩ := List.nodup_cons.mp hd
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih g f ⟨hdt, fun x hx => hb x (List.mem_cons_of_mem _ hx), hc,
        fun x y ⟨hx, hy, hxy⟩ => hcl x y ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy,
          hxy⟩⟩⟩
      obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
      have hne : h ≠ y := fun e => hnot (e ▸ hy)
      have he := hcl h y ⟨List.mem_cons_self, List.mem_cons_of_mem _ hy, hne⟩
      exact hne (hc h he.1 y ⟨he.2.1, he.2.2⟩ hfy.symm)

/-- Exact HOL `colouring_satisfactory_subgraph` (`reg_allocProofScript.sml:1483-1491`); `f`,
`g` and `h` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "colouring_satisfactory_subgraph"]
theorem colouringSatisfactorySubgraph {α : Type} (f : Nat → α) (h g : List (List Nat)) :
    colouringSatisfactory f h ∧ isSubgraph g h → colouringSatisfactory f g := by
  intro ⟨hc, hs⟩ x hx y ⟨hy, hm⟩ heq
  have he := hs x y ⟨hx, hy, hm⟩
  exact hc x he.1 y ⟨he.2.1, he.2.2⟩ heq

/-- Exact HOL `no_clash_colouring_satisfactory` (`reg_allocProofScript.sml:3024-3041`);
`adjls` and `node_tag` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "no_clash_colouring_satisfactory"]
theorem noClashColouringSatisfactory (adjls : List (List Nat)) (node_tag : List Tag) :
    noClash adjls node_tag ∧ adjls.length = node_tag.length ∧
      (∀ n ∈ node_tag, n ≠ .Stemp ∧ n ≠ .Atemp) →
    colouringSatisfactory
      (fun f => if f < node_tag.length then extractTag (holEl f node_tag) else 0) adjls := by
  intro ⟨hnc, hl, hall⟩ x hx y ⟨hy, hm⟩ heq
  have hxt : x < node_tag.length := hl ▸ hx
  have hyt : y < node_tag.length := hl ▸ hy
  have hfix : ∀ i, i < node_tag.length → ∃ c, holEl i node_tag = .Fixed c := fun i hi => by
    have hmem : holEl i node_tag ∈ node_tag := by
      rw [holEl_eq_getElem _ _ hi]; exact List.getElem_mem _
    obtain ⟨h1, h2⟩ := hall _ hmem
    cases ht : holEl i node_tag with
    | Fixed c => exact ⟨c, rfl⟩
    | Atemp => exact absurd ht h2
    | Stemp => exact absurd ht h1
  obtain ⟨a, ha⟩ := hfix x hxt
  obtain ⟨b, hb⟩ := hfix y hyt
  have hncxy := hnc x y ⟨hx, hy, hm⟩
  rw [ha, hb] at hncxy
  simp only [if_pos hxt, if_pos hyt, ha, hb, extractTag] at heq
  exact hncxy heq

end Flapjack.RegAlloc
