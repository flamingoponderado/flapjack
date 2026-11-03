import Flapjack.Compiler.Backend.ClosKnown.Total
import Flapjack.Compiler.Backend.ClosKnown.Proofs.OpGlobals

/-! Global-write framing for the total known-function traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps

/-- The total traversal retains global lookups outside the expression's
write bag. Flapjack infrastructure while full source traversal correspondence
is under review. -/
theorem knownExprTotalLookupUnchanged (c : Config) (e : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox) :
    ∀ k, setGlobals e k = 0 →
      sptLookup k (knownExprTotal c e env globals).2.2 = sptLookup k globals := by
  induction c, e, env, globals using knownExprTotal.induct
    (motive2 := fun _ _ _ _ _ => True)
    (motive3 := fun c xs env globals => ∀ k, elistGlobals xs k = 0 →
      sptLookup k (knownListTotal c xs env globals).2 = sptLookup k globals) <;>
    simp_all [knownExprTotal, knownListTotal, setGlobals, elistGlobals,
      FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_eq_zero_iff]
  case case8 =>
    intro k hop hx
    rename_i c env g0 t op xs out mid h a final opRun ih
    exact (knownOpLookupUnchanged op (out.map Prod.snd).reverse mid a final k opRun hop).trans (ih k hx)
  all_goals try (intros; split <;> simp_all)
  all_goals try (rw [knownExprTotal.eq_def]; simp_all)
  all_goals grind

/-- The total list traversal retains lookups outside its write bag. This is
Flapjack infrastructure pending review of the complete HOL traversal. -/
theorem knownListTotalLookupUnchanged (c : Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox) (k : Nat)
    (outside : elistGlobals xs k = 0) :
    sptLookup k (knownListTotal c xs env globals).2 = sptLookup k globals := by
  have h := knownExprTotalLookupUnchanged c (.call BackendCommon.orphanTrace 0 0 xs) env globals k
  simpa [knownExprTotal] using h (by simpa [setGlobals] using outside)

/-- A resulting tree lookup either already held or belongs to the input write
bag. This is infrastructure for the executed traversal, not yet a HOL port. -/
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

end Flapjack.Compiler.Backend.ClosKnown
