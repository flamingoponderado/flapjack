module

public import Flapjack.Compiler.Inference.Unify.WorklistRelation
public import Flapjack.FiniteMap.Exact.Submap
public import Flapjack.Misc.Sptree.Wf
public import Flapjack.HOL.Unification.UnifDef.WellFounded
public import Flapjack.Compiler.Inference.Unify.Walkstar.WorklistWellFounded

@[expose] public section

/-! Well-foundedness of the original paired-list unification relation. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Transfer.Fmsp Flapjack.HOL.Unification

private theorem strictDomain (parent child : Spt Flapjack.Compiler.Inference.InferT)
    (hp : cwfs parent) (hc : cwfs child)
    (sub : (sp2fm parent).submap (sp2fm child)) (ne : child ≠ parent) :
    (sp2fm parent).domain ⊂ (sp2fm child).domain := by
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨HolFiniteMapExact.submapFdomSubset _ _ sub, ?_⟩
  intro domain
  have maps : sp2fm parent = sp2fm child :=
    (HolFiniteMapExact.eqFdomSubmap _ _).mpr ⟨sub, domain⟩
  apply ne
  apply (sptEqThm child parent ⟨hc.2, hp.2⟩).mpr
  intro key
  exact (congrArg (fun m => m.lookup key) maps).symm

private abbrev State := Spt Flapjack.Compiler.Inference.InferT ×
  List (List Flapjack.Compiler.Inference.InferT × List Flapjack.Compiler.Inference.InferT)

private def totalVars (x : State) : Set Nat :=
  substVars ((sp2fm x.1).map2 (fun p => encodeInferT p.2)) ∪ cplistVars x.2

private noncomputable def rank (x : State) : Nat :=
  (totalVars x).ncard - (sp2fm x.1).domain.ncard

private theorem finiteTotalVars (x : State) : (totalVars x).Finite :=
  (finiteSubstVars _).union (finiteCplistVars _)

private theorem domainSubsetTotal (x : State) : (sp2fm x.1).domain ⊆ totalVars x := by
  intro key hk
  left
  left
  change ((sp2fm x.1).map2 (fun p => encodeInferT p.2)).lookup key ≠ none
  change (sp2fm x.1).lookup key ≠ none at hk
  simp only [HolFiniteMapExact.lookup_map2]
  cases found : (sp2fm x.1).lookup key <;> simp_all

private theorem rankDecreases (child parent : State) (h : worklistR child parent)
    (ne : child.1 ≠ parent.1) : rank child < rank parent := by
  have htotal : (totalVars child).ncard ≤ (totalVars parent).ncard :=
    Set.ncard_le_ncard h.2.2.2.1 (finiteTotalVars parent)
  have hdomain : (sp2fm parent.1).domain.ncard < (sp2fm child.1).domain.ncard :=
    Set.ncard_lt_ncard (strictDomain parent.1 child.1 h.2.1 h.1 h.2.2.1 ne)
      ((finiteTotalVars child).subset (domainSubsetTotal child))
  have hbound : (sp2fm parent.1).domain.ncard ≤ (totalVars parent).ncard :=
    Set.ncard_le_ncard (domainSubsetTotal parent) (finiteTotalVars parent)
  have hchildbound : (sp2fm child.1).domain.ncard ≤ (totalVars child).ncard :=
    Set.ncard_le_ncard (domainSubsetTotal child) (finiteTotalVars child)
  dsimp [rank]
  omega

private theorem wfWorklist : WellFounded worklistR := by
  have allAcc : ∀ n, ∀ x : State, rank x ≤ n → Acc worklistR x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      rcases x with ⟨s, wl⟩
      by_cases hw : cwfs s
      · have hs : wfs (sp2fm (sptMap encodeInferT s)) := hw.1
        have bagWf := (wfBagMultisetStep _ (walkstarThWF _ hs)).transGen
        let measure (w : List (List Flapjack.Compiler.Inference.InferT ×
            List Flapjack.Compiler.Inference.InferT)) := (pflat w, w.length)
        have lexWf := bagWf.prod_lex Nat.lt_wfRel.wf
        have wlWf := InvImage.wf measure lexWf
        have allWl : ∀ w, rank (s, w) ≤ n → Acc worklistR (s, w) := by
          intro w
          induction w using wlWf.induction with
          | h w smaller =>
            intro hrank
            apply Acc.intro
            intro child edge
            by_cases eq : child.1 = s
            · rcases child with ⟨cs, cw⟩
              dsimp only at eq
              subst cs
              have decrease : InvImage (Prod.Lex
                  (Relation.TransGen (bagMultisetStep (walkstarR (sp2fm (sptMap encodeInferT s)))))
                  (· < ·)) measure cw w := by
                rcases edge.2.2.2.2 with hbag | ⟨hbag, hlen⟩
                · exact Prod.Lex.left _ _ hbag
                · change Prod.Lex _ _ (measure cw) (measure w)
                  dsimp [measure]
                  rw [hbag]
                  exact Prod.Lex.right _ hlen
              apply smaller cw decrease
              have ht := Set.ncard_le_ncard edge.2.2.2.1 (finiteTotalVars (s, w))
              change (totalVars (s, cw)).ncard ≤ (totalVars (s, w)).ncard at ht
              dsimp [rank] at hrank ⊢
              omega
            · have hlt := rankDecreases child (s, w) edge eq
              exact ih (rank child) (by omega) child (Nat.le_refl _)
        exact allWl wl hx
      · apply Acc.intro
        intro child edge
        exact (hw edge.2.1).elim
  exact ⟨fun x => allAcc (rank x) x (Nat.le_refl _)⟩

/- The original relation is expanded in the statement to expose the imported,
   reviewed finite-map producer used by its definition. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "WF_kcunifywlR"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem wfKcunifywlR : WellFounded
    (fun (child parent : Spt InferT × List (List InferT × List InferT)) =>
      cwfs child.1 ∧ cwfs parent.1 ∧ (sp2fm parent.1).submap (sp2fm child.1) ∧
        Set.Subset
          (Set.union (substVars ((sp2fm child.1).map2 (fun p => encodeInferT p.2)))
            (cplistVars child.2))
          (Set.union (substVars ((sp2fm parent.1).map2 (fun p => encodeInferT p.2)))
            (cplistVars parent.2)) ∧
        (Relation.TransGen
            (bagMultisetStep (walkstarR (sp2fm (sptMap encodeInferT child.1))))
            (pflat child.2) (pflat parent.2) ∨
          (pflat child.2 = pflat parent.2 ∧ child.2.length < parent.2.length))) := by
  exact wfWorklist

end Flapjack.Compiler.Inference.Unify
