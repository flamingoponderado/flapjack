import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGlobalSafety

/-! Preservation of approximation entries during known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown.KnownSubspt
open ClosProps

/-- Multiplicity in the bag formed from a sparse-tree domain. This is the
pointwise rendering of HOL's BAG_OF_SET over sptree domain. -/
noncomputable def domainBag {A : Type} (g : Spt A) (i : Nat) : Nat := by
  classical
  exact if sptMem i g then 1 else 0

/-- A disjoint primitive write preserves every old approximation and adds
only entries in the primitive's write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_subspt"]
theorem knownOpSubspt (op : ClosLang.Op) (args : List ValApprox) (g0 : Spt ValApprox)
    (a : ValApprox) (g : Spt ValApprox)
    (h : knownOpHOL op args g0 = (a, g) ∧ ∀ i, sptMem i g0 → opGlobalBag op i = 0) :
    (∀ i, domainBag g i ≤ domainBag g0 i + opGlobalBag op i) ∧ sptSubspt g0 g := by
  classical
  obtain ⟨run, disjoint⟩ := h
  constructor
  · intro i
    by_cases old : sptMem i g0
    · simp [domainBag, old]
      split <;> omega
    · by_cases new : sptMem i g
      · have changed := knownOpChangedGlobalsAltSet op args g0 a g run i new
        have written : opGlobalBag op i ≠ 0 := changed.resolve_left old
        simp [domainBag, old, new]
        omega
      · simp [domainBag, old, new]
  · intro i member
    have eq := knownOpLookupUnchanged op args g0 a g i run (disjoint i member)
    have ⟨value, lookup⟩ := (sptMem_iff_lookup i g0).1 member
    refine ⟨(sptMem_iff_lookup i g).2 ⟨value, ?_⟩, eq⟩
    exact eq.trans lookup

/-- A uniquely writing program preserves every original approximation and its
resulting domain is bounded by the old domain plus the input write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_subspt"]
theorem knownSubspt (c : Config) (xs : List ClosLang.Exp) (aenv : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c xs aenv g0 = (eas, g) ∧
      (∀ e ∈ xs, esgcFree e) ∧ (∀ a ∈ aenv, valApproxSgcFree a) ∧
      globalsApproxSgcFree g0 ∧ ∀ i, domainBag g0 i + elistGlobals xs i ≤ 1) :
    (∀ i, domainBag g i ≤ domainBag g0 i + elistGlobals xs i) ∧ sptSubspt g0 g := by
  classical
  obtain ⟨run, _, _, _, distinct⟩ := h
  have disjoint : ∀ i, sptMem i g0 → elistGlobals xs i = 0 := by
    intro i member
    have bound := distinct i
    simp [domainBag, member] at bound
    omega
  constructor
  · intro i
    by_cases old : sptMem i g0
    · simp [domainBag, old]
      split <;> omega
    · by_cases new : sptMem i g
      · have changed := knownListTotalChangedGlobalsAltSet c xs aenv g0 eas g run i new
        have written : elistGlobals xs i ≠ 0 := changed.resolve_left old
        simp [domainBag, old, new]
        omega
      · simp [domainBag, old, new]
  · intro i member
    have eq := knownListTotalLookupUnchanged c xs aenv g0 i (disjoint i member)
    rw [run] at eq
    have ⟨value, lookup⟩ := (sptMem_iff_lookup i g0).1 member
    refine ⟨(sptMem_iff_lookup i g).2 ⟨value, ?_⟩, eq⟩
    exact eq.trans lookup

end Flapjack.Compiler.Backend.ClosKnown.KnownSubspt
