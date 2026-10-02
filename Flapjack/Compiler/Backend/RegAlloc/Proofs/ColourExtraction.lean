import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.MovePrep
import Flapjack.Compiler.Backend.RegAlloc.Proofs.AccessorEqns
import Flapjack.Compiler.Backend.RegAlloc.Proofs.Invariants
import Flapjack.Misc.Sptree.Wf
import Flapjack.Misc.Sptree.Map

/-!
# reg_allocProof: colour extraction

Ports of `reg_allocProofScript.sml:2038-2066`: reading the fixed colours of the mapped nodes
succeeds without changing the state, and on a well-formed map `extract_color` is the
pointwise `map` of `extract_tag` over the node tags. HOL `EL` is the exact `holEl`,
`lookup`/`map`/`wf`/`toAList`/`fromAList` are the tagged `Spt` operations, and a pattern
lambda `λ(k,v). P` over pairs reads the components.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

/-- A state-preserving `st_ex_MAP` returns the pointwise results (Flapjack infrastructure). -/
private theorem stExMap_pure {β γ : Type} {f : β → M State γ StateException} {g : β → γ}
    (s : State) :
    ∀ (ls : List β), (∀ p ∈ ls, f p s = (.success (g p), s)) →
      stExMap f ls s = (.success (ls.map g), s)
  | [], _ => rfl
  | p :: ps, h => by
      simp only [stExMap, Translator.Monadic.MonadBase.bind, h p List.mem_cons_self,
        stExMap_pure s ps (fun q hq => h q (List.mem_cons_of_mem _ hq)), ret, List.map_cons]

/-- Exact HOL `extract_color_st_ex_MAP_lem` (`reg_allocProofScript.sml:2038-2046`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "extract_color_st_ex_MAP_lem"]
theorem extractColorStExMapLem :
    ∀ (ls : List (Nat × Nat)) (s : State),
      (∀ p ∈ ls, p.2 < s.node_tag.length) →
      stExMap (fun (k, v) => bind (nodeTagSub v) fun t => ret (k, extractTag t)) ls s =
        (.success (ls.map fun (k, v) => (k, extractTag (holEl v s.node_tag))), s) := by
  intro ls s h
  refine stExMap_pure s ls (fun p hp => ?_)
  obtain ⟨k, v⟩ := p
  simp only [Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos (h _ hp), ret]

/-- `ALOOKUP` of a value-mapped association list (Flapjack infrastructure). -/
private theorem alookup_map {α β : Type} (h : α → β) (n : Nat) :
    ∀ (l : List (Nat × α)),
      sptAListLookup n (l.map fun p => (p.1, h p.2)) = (sptAListLookup n l).map h
  | [] => rfl
  | (k, v) :: l => by
      simp only [List.map_cons, sptAListLookup]
      by_cases hk : n = k
      · simp [hk]
      · simp only [if_neg hk]
        exact alookup_map h n l

/-- Exact HOL `extract_color_succeeds` (`reg_allocProofScript.sml:2048-2066`); `s` and `ta`
are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "extract_color_succeeds"]
theorem extractColorSucceeds (s : State) (ta : Spt Nat) :
    goodRaState s ∧ (∀ x y, sptLookup x ta = some y → y < s.dim) ∧ sptWf ta = true →
    extractColor ta s = (.success (sptMap (fun v => extractTag (holEl v s.node_tag)) ta), s) := by
  intro ⟨hg, hb, hw⟩
  have hbl : ∀ p ∈ sptToAList ta, p.2 < s.node_tag.length := fun ⟨k, v⟩ hp => by
    rw [hg.2.1]
    exact hb k v ((sptMemToAList ta k v).mp hp)
  simp only [extractColor, Translator.Monadic.MonadBase.bind, ret]
  rw [stExMap_pure (g := fun p => (p.1, extractTag (holEl p.2 s.node_tag))) s _
    (fun p hp => by
      obtain ⟨k, v⟩ := p
      simp only [Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos (hbl _ hp), ret])]
  simp only [Prod.mk.injEq, Exc.success.injEq, and_true]
  refine (sptEqThm _ _ ⟨sptWfFromAList _, by rw [sptWfMap]; exact hw⟩).mpr (fun n => ?_)
  rw [sptLookup_sptFromAList, alookup_map (fun v => extractTag (holEl v s.node_tag)) n,
    sptLookup_sptMap]
  congr 1
  rw [← sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList]

end Flapjack.RegAlloc
