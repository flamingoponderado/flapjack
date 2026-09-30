import Flapjack.Pancake.LoopLang

/-!
# loopProps `acc_vars_acc`

Exact port of `cakeml/pancake/semantics/loopPropsScript.sml:89`'s
`acc_vars_acc` over the faithful width-indexed `HolLoopProg` carrier:
`domain (acc_vars p l) = domain (acc_vars p LN) UNION domain l`.
HOL sets are rendered by the predicate `sptDomain` and union by pointwise
disjunction.  `accVarsHOL` is the tagged `loopLangScript.sml:118-155` port.
-/

namespace Flapjack

variable {width : Nat} [NeZero width]

/-- Flapjack-specific helper: HOL sptree `list_insert` membership.  The HOL
source `sptree$list_insert` lives outside `cakeml/`, so `sptListInsert`
(`Flapjack/Misc/Sptree.lean`) carries no `@[hol]` tag; this membership
characterisation is Flapjack infrastructure and has no separate CakeML
declaration. -/
theorem sptMem_sptListInsert_iff (k : Nat) (keys : List Nat) (tree : NumSet) :
    sptMem k (sptListInsert keys tree) ↔ k ∈ keys ∨ sptMem k tree := by
  induction keys generalizing tree with
  | nil => simp [sptListInsert]
  | cons key keys ih =>
      rw [show sptListInsert (key :: keys) tree =
            sptListInsert keys (sptInsert key () tree) from rfl]
      rw [ih, sptMem_sptInsert]
      simp only [List.mem_cons]
      constructor
      · rintro (hk | hrest)
        · exact Or.inl (Or.inr hk)
        · rcases hrest with hk | hs
          · exact Or.inl (Or.inl hk)
          · exact Or.inr hs
      · rintro (hrest | hs)
        · rcases hrest with hk | hk
          · exact Or.inr (Or.inl hk)
          · exact Or.inl hk
        · exact Or.inr (Or.inr hs)

/-- Flapjack-specific helper: `sptDomain` after `sptInsert`.  This packages
`sptMem_sptInsert` as a function equality, used by `accVarsAccHOL`. -/
theorem sptDomain_sptInsert {α : Type} (key : Nat) (value : α) (tree : Spt α) :
    sptDomain (sptInsert key value tree) =
      (fun k => k = key ∨ sptDomain tree k) := by
  funext k
  apply propext
  exact sptMem_sptInsert k key value tree

/-- Flapjack-specific helper: `sptDomain` after `sptListInsert`.  This packages
`sptMem_sptListInsert_iff` as a function equality. -/
theorem sptDomain_sptListInsert (keys : List Nat) (tree : NumSet) :
    sptDomain (sptListInsert keys tree) =
      (fun k => k ∈ keys ∨ sptDomain tree k) := by
  funext k
  apply propext
  exact sptMem_sptListInsert_iff k keys tree

/-- Exact HOL `acc_vars_acc` (`loopPropsScript.sml:89`): the locals assigned by
`p` when accumulated into `l` are exactly those it assigns into `LN` together
with the domain of `l`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "acc_vars_acc"
  (words_as_type_indexed_bitvec)]
theorem accVarsAccHOL :
    ∀ (p : HolLoopProg width) (l : NumSet),
      sptDomain (accVarsHOL p l) =
        (fun k => sptDomain (accVarsHOL p .ln) k ∨ sptDomain l k)
  | .seq first second, l => by
      have h2 := accVarsAccHOL second l
      have h1 := accVarsAccHOL first (accVarsHOL second l)
      have h1' := accVarsAccHOL first (accVarsHOL second .ln)
      have h2' := accVarsAccHOL second .ln
      simp only [accVarsHOL]
      rw [h1, h2, h1', h2']
      funext k
      simp only [sptDomain, or_assoc]
  | .ite _ _ _ first second _, l => by
      have h2 := accVarsAccHOL second l
      have h1 := accVarsAccHOL first (accVarsHOL second l)
      have h1' := accVarsAccHOL first (accVarsHOL second .ln)
      have h2' := accVarsAccHOL second .ln
      simp only [accVarsHOL]
      rw [h1, h2, h1', h2']
      funext k
      simp only [sptDomain, or_assoc]
  | .loop _ body _, l => by
      simpa only [accVarsHOL] using accVarsAccHOL body l
  | .mark body, l => by
      simpa only [accVarsHOL] using accVarsAccHOL body l
  | .skip, l | .tick, l | .fail, l | .store _ _, l
  | .setGlobal _ _, l | .store32 _ _, l | .storeByte _ _, l
  | .break _, l | .continue _, l | .raise _, l | .return _, l
  | .call none _ _ _, l | .ffi _ _ _ _ _ _, l => by
      funext k
      simp [accVarsHOL, sptDomain]
  | .assign name _, l | .locValue name _, l | .shMem _ name _, l
  | .load32 _ name, l | .loadByte _ name, l => by
      simp only [accVarsHOL, sptDomain_sptInsert]
      funext k
      simp [sptDomain]
  | .arith (.div name _ _), l => by
      simp only [accVarsHOL, sptDomain_sptInsert]
      funext k
      simp [sptDomain]
  | .arith (.longMul v1 v2 _ _), l | .arith (.longDiv v1 v2 _ _ _), l => by
      simp only [accVarsHOL, sptDomain_sptInsert]
      funext k
      simp [sptDomain, or_assoc]
  | .primitive destinations _ _, l => by
      simp only [accVarsHOL, sptDomain_sptListInsert]
      funext k
      simp [sptDomain]
  | .call (some (vs, snd)) target args none, l => by
      simp only [accVarsHOL, sptDomain_sptListInsert]
      funext k
      simp [sptDomain]
  | .call (some (vs, snd)) target args (some (n, p1, p2, snd2)), l => by
      have h2 := accVarsAccHOL p2 (sptInsert n () (sptListInsert vs l))
      have h1 := accVarsAccHOL p1 (accVarsHOL p2 (sptInsert n () (sptListInsert vs l)))
      have h1' := accVarsAccHOL p1 (accVarsHOL p2 (sptInsert n () (sptListInsert vs .ln)))
      have h2' := accVarsAccHOL p2 (sptInsert n () (sptListInsert vs .ln))
      simp only [accVarsHOL]
      rw [h1, h2, h1', h2']
      simp only [sptDomain_sptInsert, sptDomain_sptListInsert]
      funext k
      simp [sptDomain, or_assoc]
  termination_by p _ => sizeOf p

end Flapjack
