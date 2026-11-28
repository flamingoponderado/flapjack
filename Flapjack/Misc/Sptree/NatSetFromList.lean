module

public import Flapjack.Misc.Sptree.Wf
public import Flapjack.Misc.Sptree.ToAList
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# Folding insertions over a key list

Counterparts of `wf_nat_set_from_list` and `domain_nat_set_from_list` from
`cakeml/misc/miscScript.sml`. HOL's `domain ns UNION set ls` over `num -> bool`
maps is the pointwise disjunction `fun k => sptDomain ns k \/ k ∈ ls`; the
set-builder needs `Mathlib.Data.Set.Basic`, which lives here rather than in the
widely imported `Sptree/Wf` and `Sptree/ToAList`.
-/

namespace Flapjack

/-- Original `wf_nat_set_from_list`: folding unit insertions over a list keeps a
well-formed tree well-formed. -/
@[hol "cakeml/misc/miscScript.sml" "wf_nat_set_from_list"]
theorem wfNatSetFromList {α : Type} (ls : List Nat) (ns : Spt α) (z : α)
    (hwf : sptWf ns = true) :
    sptWf (ls.foldl (fun s n => sptInsert n z s) ns) = true := by
  induction ls generalizing ns with
  | nil => exact hwf
  | cons a rest ih =>
    simp only [List.foldl_cons]
    exact ih (sptInsert a z ns) (sptWfInsert a z ns hwf)

/-- Original `domain_nat_set_from_list`: the domain of a folded insertion list is
the old domain together with the list's keys. -/
@[hol "cakeml/misc/miscScript.sml" "domain_nat_set_from_list"]
theorem domainNatSetFromList (ls : List Nat) (ns : NumSet) :
    sptDomain (ls.foldl (fun s n => sptInsert n () s) ns) =
      fun k => sptDomain ns k ∨ k ∈ ls := by
  induction ls generalizing ns with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [ih (sptInsert a () ns), sptDomainInsert]
    ext k
    simp only [List.mem_cons]
    rw [or_assoc]
    constructor
    · intro h
      rcases h with a | (b | c)
      · exact Or.inr (Or.inl a)
      · exact Or.inl b
      · exact Or.inr (Or.inr c)
    · intro h
      rcases h with b | (a | c)
      · exact Or.inr (Or.inl b)
      · exact Or.inl a
      · exact Or.inr (Or.inr c)

end Flapjack
