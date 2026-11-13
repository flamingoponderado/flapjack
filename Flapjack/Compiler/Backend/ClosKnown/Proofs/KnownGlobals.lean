module

public import Flapjack.Compiler.Backend.ClosKnown.Total
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.OpGlobals

@[expose] public section

/-! Global-write framing for the total known-function traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps

/-- The total traversal retains global lookups outside the expression's
write bag. This helper has no separate HOL declaration. -/
theorem knownExprTotalLookupUnchanged (c : Config) (e : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox) :
    ∀ k, setGlobals e k = 0 →
      sptLookup k (knownExprTotal c e env globals).2.2 = sptLookup k globals := by
  induction c, e, env, globals using knownExprTotal.induct
    (motive2 := fun _ _ _ _ _ => True)
    (motive3 := fun c xs env globals => ∀ k, elistGlobals xs k = 0 →
      sptLookup k (knownListTotal c xs env globals).2 = sptLookup k globals) <;>
    simp_all [knownExprTotal, knownListTotal, setGlobals, elistGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_eq_zero_iff, Flapjack.bagUnion, Flapjack.emptyBag]
  case case8 =>
    intro k hop hx
    rename_i c env g0 t op xs out mid h a final opRun ih
    exact (knownOpLookupUnchanged op (out.map Prod.snd).reverse mid a final k opRun hop).trans (ih k hx)
  all_goals try (intros; split <;> simp_all)
  all_goals try (rw [knownExprTotal.eq_def]; simp_all)
  all_goals grind

/-- The total list traversal retains lookups outside its write bag. This is
This helper has no separate HOL declaration. -/
theorem knownListTotalLookupUnchanged (c : Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox) (k : Nat)
    (outside : elistGlobals xs k = 0) :
    sptLookup k (knownListTotal c xs env globals).2 = sptLookup k globals := by
  have h := knownExprTotalLookupUnchanged c (.call BackendCommon.orphanTrace 0 0 xs) env globals k
  simpa [knownExprTotal] using h (by simpa [setGlobals] using outside)

/-- A resulting tree lookup either already held or belongs to the input write
bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_changed_globals_cases"]
theorem knownListTotalChangedGlobalsCases (c : Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (g0 : Spt ValApprox) (result : List (ClosLang.Exp × ValApprox))
    (g : Spt ValApprox) (run : knownListTotal c xs env g0 = (result, g)) :
    ∀ k a, sptLookup k g = some a → sptLookup k g0 = some a ∨ elistGlobals xs k ≠ 0 := by
  intro k a found
  by_cases outside : elistGlobals xs k = 0
  · left
    have unchanged := knownListTotalLookupUnchanged c xs env g0 k outside
    rw [run] at unchanged
    simpa [← unchanged] using found
  · exact Or.inr outside

/-- New or changed approximation entries belong to the input write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_changed_globals"]
theorem knownListTotalChangedGlobals (c : Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (g0 : Spt ValApprox) (result : List (ClosLang.Exp × ValApprox))
    (g : Spt ValApprox) (run : knownListTotal c xs env g0 = (result, g)) :
    ∀ i, sptMem i g ∧ (sptMem i g0 → sptLookup i g ≠ sptLookup i g0) →
      elistGlobals xs i ≠ 0 := by
  intro i ⟨member, changed⟩
  obtain ⟨value, found⟩ := (sptMem_iff_lookup i g).1 member
  rcases knownListTotalChangedGlobalsCases c xs env g0 result g run i value found with old | written
  · have oldMember := (sptMem_iff_lookup i g0).2 ⟨value, old⟩
    exact False.elim (changed oldMember (found.trans old.symm))
  · exact written

/-- The result domain is contained in the prior domain and input write set. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_changed_globals_alt_set"]
theorem knownListTotalChangedGlobalsAltSet (c : Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (g0 : Spt ValApprox) (result : List (ClosLang.Exp × ValApprox))
    (g : Spt ValApprox) (run : knownListTotal c xs env g0 = (result, g)) :
    ∀ i, sptMem i g → sptMem i g0 ∨ elistGlobals xs i ≠ 0 := by
  intro i member
  obtain ⟨value, found⟩ := (sptMem_iff_lookup i g).1 member
  rcases knownListTotalChangedGlobalsCases c xs env g0 result g run i value found with old | written
  · exact Or.inl ((sptMem_iff_lookup i g0).2 ⟨value, old⟩)
  · exact Or.inr written

/-- The original multiplicity bound for output approximation domains. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_changed_globals_alt"]
theorem knownListTotalChangedGlobalsAlt (c : Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (g0 : Spt ValApprox) (result : List (ClosLang.Exp × ValApprox))
    (g : Spt ValApprox) (run : knownListTotal c xs env g0 = (result, g)) :
    Flapjack.subBag (Flapjack.bagOfSet (sptDomain g))
      (Flapjack.bagUnion (Flapjack.bagOfSet (sptDomain g0)) (elistGlobals xs)) := by
  classical
  intro key count bounded
  have included :=  knownListTotalChangedGlobalsAltSet c xs env g0 result g run key
  simp only [Flapjack.bagInn, Flapjack.bagOfSet, Flapjack.bagUnion] at bounded ⊢
  by_cases current : sptDomain g key
  · have alternatives := included current
    by_cases prior : sptDomain g0 key
    · simp only [current, prior, ite_true] at bounded ⊢
      omega
    · have written := alternatives.resolve_left prior
      simp only [current, prior, ite_true, ite_false, Nat.zero_add] at bounded ⊢
      omega
  · simp only [current, ite_false] at bounded
    omega

end Flapjack.Compiler.Backend.ClosKnown
