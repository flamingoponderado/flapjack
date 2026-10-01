import Flapjack.Misc.Sptree
import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack infrastructure exposing the guarded selector parameter. It has no
separately claimed HOL original; `ssaLocalsRel_selectorIndependent` establishes
that the unspecified NONE behavior of a SOME-correct selector is irrelevant. -/
def ssaLocalsRelWith {α : Type} (select : Option Nat → Nat) (next : Nat)
    (ssa : Spt Nat) (source target : Spt α) : Prop :=
  (∀ x y, sptLookup x ssa = some y → sptMem y target) ∧
  (∀ x y, sptLookup x source = some y →
    sptMem x ssa ∧ sptLookup (select (sptLookup x ssa)) target = some y ∧
      (isAllocVar x → x < next))

/-- Flapjack infrastructure: the domain conjunct forces SOME before the selector
is observed. No tree well-formedness, relation, or selected-result premise is
assumed. This supplies the source comparison for HOL THE, whose only defining
clause is THE (SOME n) = n; it makes no claim about THE NONE. -/
theorem ssaLocalsRel_selectorIndependent {α : Type}
    (selectA selectB : Option Nat → Nat)
    (hA : ∀ n, selectA (some n) = n) (hB : ∀ n, selectB (some n) = n)
    (next : Nat) (ssa : Spt Nat) (source target : Spt α) :
    ssaLocalsRelWith selectA next ssa source target ↔
      ssaLocalsRelWith selectB next ssa source target := by
  suffices forward : ∀ a b : Option Nat → Nat,
      (∀ n, a (some n) = n) → (∀ n, b (some n) = n) →
      ssaLocalsRelWith a next ssa source target →
        ssaLocalsRelWith b next ssa source target from
    ⟨forward selectA selectB hA hB, forward selectB selectA hB hA⟩
  intro a b ha hb h
  rcases h with ⟨hm, hl⟩
  refine ⟨hm, ?_⟩
  intro x y hx
  rcases hl x y hx with ⟨hd, he, hn⟩
  rcases (sptMem_iff_lookup x ssa).mp hd with ⟨r, hr⟩
  refine ⟨hd, ?_, hn⟩
  simpa only [hr, ha, hb] using he

/-- Native SSA locals relation. HOL THE is observed only under the source-domain
conjunct. The checked selector-independence theorem above justifies `getD 0`
for that guarded use without asserting that HOL THE NONE equals zero. All
source/target value types remain generic and no input tree is required to be
well formed. This proof predicate has no executed compiler route. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_def"]
def ssaLocalsRel {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) : Prop :=
  ssaLocalsRelWith (fun value => value.getD 0) next ssa source target

end Flapjack.Compiler.Backend.WordAlloc
