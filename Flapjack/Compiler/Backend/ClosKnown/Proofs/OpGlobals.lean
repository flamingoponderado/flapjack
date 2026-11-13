module

public import Flapjack.Compiler.Backend.ClosKnown.KnownOp
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals

@[expose] public section

/-! Global approximation changes made by known-function primitives. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps

/-- Outside the source operation's write bag, primitive approximation
leaves every tree lookup unchanged. This is proof infrastructure. -/
theorem knownOpLookupUnchanged (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox) (key : Nat)
    (known : knownOpHOL op args g0 = (a, g)) (outside : opGlobalBag op key = 0) :
    sptLookup key g = sptLookup key g0 := by
  unfold knownOpHOL at known
  split at known <;> simp_all [opGlobalBag]
  all_goals try (split at known <;> simp_all)
  rcases known with ⟨_, rfl⟩
  exact sptLookup_sptInsert_ne _ _ _ _ outside

/-- Any resulting lookup either was present unchanged or belongs to the
operation's global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_changed_globals_cases"]
theorem knownOpChangedGlobalsCases (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (result : ValApprox) (g : Spt ValApprox)
    (known : knownOpHOL op args g0 = (result, g)) :
    ∀ k a, sptLookup k g = some a →
      sptLookup k g0 = some a ∨ opGlobalBag op k ≠ 0 := by
  intro k a found
  by_cases outside : opGlobalBag op k = 0
  · left
    rw [← knownOpLookupUnchanged op args g0 result g k known outside]
    exact found
  · exact Or.inr outside

/-- Changes to the domain or existing lookup are confined to the operation's
global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_changed_globals"]
theorem knownOpChangedGlobals (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (result : ValApprox) (g : Spt ValApprox)
    (known : knownOpHOL op args g0 = (result, g)) :
    ∀ i, sptMem i g ∧ (sptMem i g0 → sptLookup i g ≠ sptLookup i g0) →
      opGlobalBag op i ≠ 0 := by
  intro i ⟨member, changed⟩
  obtain ⟨value, found⟩ := (sptMem_iff_lookup i g).1 member
  rcases knownOpChangedGlobalsCases op args g0 result g known i value found with old | added
  · have oldMember := (sptMem_iff_lookup i g0).2 ⟨value, old⟩
    exact False.elim (changed oldMember (found.trans old.symm))
  · exact added

/-- The result domain is included in the previous domain plus the write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_changed_globals_alt_set"]
theorem knownOpChangedGlobalsAltSet (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (result : ValApprox) (g : Spt ValApprox)
    (known : knownOpHOL op args g0 = (result, g)) :
    ∀ i, sptMem i g → sptMem i g0 ∨ opGlobalBag op i ≠ 0 := by
  intro i member
  obtain ⟨value, found⟩ := (sptMem_iff_lookup i g).1 member
  rcases knownOpChangedGlobalsCases op args g0 result g known i value found with old | added
  · exact Or.inl ((sptMem_iff_lookup i g0).2 ⟨value, old⟩)
  · exact Or.inr added

/-- The original multiplicity bound for primitive-operation output domains. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_changed_globals_alt"]
theorem knownOpChangedGlobalsAlt (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (result : ValApprox) (g : Spt ValApprox)
    (known : knownOpHOL op args g0 = (result, g)) :
    Flapjack.subBag (Flapjack.bagOfSet (sptDomain g))
      (Flapjack.bagUnion (Flapjack.bagOfSet (sptDomain g0)) (opGlobalBag op)) := by
  classical
  intro key count bounded
  have included :=  knownOpChangedGlobalsAltSet op args g0 result g known key
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
